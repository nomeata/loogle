import Lean.Meta
import Lake.CLI.Error
import Lake.Util.Cli
import Mathlib.Tactic.Find

import Seccomp

set_option autoImplicit false


open Lean Core Meta Elab Term Command

instance : ToExpr System.FilePath where
  toTypeExpr := Lean.mkConst ``System.FilePath
  toExpr path := mkApp (Lean.mkConst ``System.FilePath.mk) (toExpr path.1)

elab "#compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

elab "#looglePath" : term =>
  return toExpr (← IO.getEnv "LOOGLE_PATH")

def compileTimeSearchPath : SearchPath :=
  match #looglePath with 
  | some p => System.SearchPath.parse p
  | none => #compileTimeSearchPath

def Result := Except String (String × Array Lean.Name)
def Printer := Result → IO Unit 

def runQuery (query : String) : CoreM Result  := withCurrHeartbeats do
  match Parser.runParserCategory (← getEnv) `find_patterns query with
  | .error err => pure $ .error err
  | .ok s => do
    MetaM.run' do
      try
        let args ← TermElabM.run' $ Mathlib.Tactic.Find.parseFindPatterns (.mk s)
        match ← Mathlib.Tactic.Find.find args with
        | .ok (header, names) => do
            pure $ .ok (← header.toString, names.toArray)
        | .error err => pure $ .error (← err.toString)
      catch e =>
        pure $ .error (← e.toMessageData.toString)


def printPlain : Printer
  | .error err => IO.println err
  | .ok (header, names) => do
      IO.println header
      names.forM (fun name => IO.println name)

def toJson : Result → Json
  | .error err => .mkObj [("error", .str err)]
  | .ok (header, names) =>
      .mkObj [("header", header),
              ("names", .arr (names.map (fun name => .str name.toString)))]

def printJson : Printer := fun r => do
  IO.println (toJson r).compress
  (← IO.getStdout).flush

def single (print : Printer) (query : String) : CoreM Unit := do
  let r ← runQuery query
  print r

def interactive (print : Printer) : CoreM Unit := do
  while true do
    let query := (← (← IO.getStdin).getLine).trim
    if query.isEmpty then break
    single print query

unsafe def work (path : Option String) (mod : String) (act : CoreM Unit) : IO Unit := do
  match path with
  | some p => searchPathRef.set [p]
  | none => searchPathRef.set compileTimeSearchPath
  withImportModules [{module := mod.toName}, {module := `Mathlib.Tactic.Find}] {} 0 fun env => do
    let ctx := {fileName := "/", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> act'.toIO ctx state
  where act' := do
    -- warm up the cache eagerly
    let _ ← MetaM.run' $ Mathlib.Tactic.Find.findDeclsByConsts.get
    Seccomp.enable
    act

structure LoogleOptions where
  interactive : Bool := false
  json : Bool := false
  query : Option String := none
  module : String := "Mathlib"
  searchPath : Option String := none
  wantsHelp : Bool := false
abbrev CliMainM := ExceptT Lake.CliError IO
abbrev CliStateM := StateT LoogleOptions CliMainM
abbrev CliM := Lake.ArgsT CliStateM


def takeArg (arg : String) : CliM String := do
  match (← Lake.takeArg?) with
  | none => throw <| Lake.CliError.missingArg arg
  | some arg => pure arg

def lakeShortOption : (opt : Char) → CliM PUnit
| 'i' => modifyThe LoogleOptions ({· with interactive := true})
| 'j' => modifyThe LoogleOptions ({· with json := true})
| 'h' => modifyThe LoogleOptions ({· with wantsHelp := true})
| opt => throw <| Lake.CliError.unknownShortOption opt

def lakeLongOption : (opt : String) → CliM PUnit
| "--help"  => lakeShortOption 'h'
| "--interactive"  => lakeShortOption 'i'
| "--json" => lakeShortOption 'j'
| "--path"     => do modifyThe LoogleOptions ({· with searchPath := ← takeArg "--path"})
| "--module"   => do modifyThe LoogleOptions ({· with module := ← takeArg "--module"})
| opt         => throw <| Lake.CliError.unknownLongOption opt

def lakeOption :=
  Lake.option {
    short := lakeShortOption
    long := lakeLongOption
    longShort := Lake.shortOptionWithArg lakeShortOption
  }

def usage := "
USAGE:
  loogle [OPTIONS] [QUERY]

OPTIONS:
  --help
  --interactive, -i     read querys from stdin
  --json, -j            print result in JSON format
  --module mod          import this module (default: Mathlib)
  --path path           search for .olean files here (default: the build time path)

Current search path:
" ++ String.join (compileTimeSearchPath.map (fun p => s!" * {p}\n"))

unsafe def loogleCli : CliM PUnit := do
  match (← Lake.getArgs) with
  | [] => IO.println usage
  | _ => -- normal CLI
    Lake.processOptions lakeOption
    let opts ← getThe LoogleOptions
    let queries ← Lake.takeArgs
    let print := if opts.json then printJson else printPlain
    if opts.wantsHelp || queries.isEmpty && not opts.interactive
    then IO.println usage
    else work opts.searchPath opts.module do
      queries.forM (single print)
      if opts.interactive
      then interactive print

unsafe def main (args : List String) : IO Unit := do
  match (← (loogleCli.run args |>.run' {}).run) with
    | .ok _ => pure ()
    | .error e => IO.println e.toString
