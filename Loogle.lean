import Lean.Meta
import Lake.CLI.Error
import Lake.Util.Cli
import Std.Util.Pickle
import Mathlib.Tactic.Find

import Seccomp

set_option autoImplicit false


section RunParser
open Lean Parser

--- like `Parser.runParserCategory`, but does not need a parser category. H'T Kyle Miller
def Parser.runParser (env : Environment) (declName : Name) (input : String)
    (fileName := "<input>") :
    Except String Syntax :=
  let p := andthenFn whitespace (evalParserConst declName)
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

end RunParser

open Lean Core Meta Elab Term Command
open Mathlib.Tactic

instance : ToExpr System.FilePath where
  toTypeExpr := Lean.mkConst ``System.FilePath
  toExpr path := mkApp (Lean.mkConst ``System.FilePath.mk) (toExpr path.1)

elab "#compileTimeSearchPath" : term => do
  let path ← searchPathRef.get
  let path' :=
    -- A little hack to not embed the searchpath when building under nix
    if path.any (fun p => p.toString.endsWith "Loogle-depRoot")
    then [] else path
  return toExpr path'
def compileTimeSearchPath : SearchPath := #compileTimeSearchPath

/-- Like `Find.Failure`, but without syntax references and with syntax pretty-printed -/
def Failure := String × Array String

def Result := Except Failure Find.Result
def Printer := Result → IO Unit 

def runQuery (index : Find.Index) (query : String) : CoreM Result  := withCurrHeartbeats do
  match Parser.runParser (← getEnv) `Mathlib.Tactic.Find.find_filters query with
  | .error err => pure $ .error (err, #[])
  | .ok s => do
    MetaM.run' do
      try
        match ← TermElabM.run' $ Mathlib.Tactic.Find.find index (.mk s) with
        | .ok result => pure $ .ok result
        | .error err => do
          let suggs ← err.suggestions.mapM fun sugg => do
            return (← PrettyPrinter.ppCategory ``Find.find_filters sugg).pretty
          pure $ .error (← err.message.toString, suggs)
      catch e =>
        pure $ .error (← e.toMessageData.toString, #[])

def printPlain : Printer
  | .error (err, suggs) => do
    IO.println err
    unless suggs.isEmpty do
    IO.println "Maybe you meant:"
    suggs.forM (fun s => IO.println ("* " ++ s))
  | .ok result => do
    IO.println (← result.header.toString)
    result.hits.forM fun (ci, mod) => match mod with
      | none => IO.println s!"{ci.name}" -- unlikely to happen in CLI usage
      | some mod => IO.println s!"{ci.name} (from {mod})"

def toJson : Result → IO Json -- only in IO for MessageData.toString
  | .error (err, suggs) => do
      if suggs.isEmpty then
        pure $ .mkObj [ ("error", .str err) ]
      else
        pure $ .mkObj [ ("error", .str err), ("suggestions", .arr (suggs.map .str)) ]
  | .ok result => do
      pure $ .mkObj [
        ("header", ← result.header.toString),
        ("count", .num result.count),
        ("hits", .arr $ result.hits.map fun (ci, mod) => .mkObj [
            ("name", .str ci.name.toString),
            ("module", match mod with | none => .null | some name => .str name.toString)
        ])
      ]

def printJson : Printer := fun r => do
  IO.println (← toJson r).compress
  (← IO.getStdout).flush

def single (index : Find.Index) (print : Printer) (query : String) : CoreM Unit := do
  let r ← runQuery index query
  print r

def interactive (index : Find.Index) (print : Printer) : CoreM Unit := do
  while true do
    let query := (← (← IO.getStdin).getLine).trim
    if query.isEmpty then break
    single index print query

structure LoogleOptions where
  interactive : Bool := false
  json : Bool := false
  query : Option String := none
  module : String := "Mathlib"
  searchPath : Option String := none
  writeIndex : Option String := none
  readIndex : Option String := none
  wantsHelp : Bool := false

unsafe def work (opts : LoogleOptions) (act : Find.Index → CoreM Unit) : IO Unit := do
  if let some p := opts.searchPath
  then searchPathRef.set [p]
  else searchPathRef.set compileTimeSearchPath

  let imports := #[{module := opts.module.toName}, {module := `Mathlib.Tactic.Find}]
  withImportModules imports {} 0 fun env => do
    let ctx := {fileName := "/", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> act'.toIO ctx state
  where act' : CoreM Unit := do
    let index ← match opts.readIndex with
    | some path => do
      let (index, _) ← unpickle _ path
      Find.Index.mkFromCache index
    | none => Find.Index.mk
    -- warm up cache eagerly
    let _ ← index.1.cache.get
    let _ ← index.2.cache.get
    if let some path := opts.writeIndex then pickle path (← index.getCache)
    Seccomp.enable
    act index

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
| "--help" => lakeShortOption 'h'
| "--interactive" => lakeShortOption 'i'
| "--json" => lakeShortOption 'j'
| "--path" => do modifyThe LoogleOptions ({· with searchPath := ← takeArg "--path"})
| "--module" => do modifyThe LoogleOptions ({· with module := ← takeArg "--module"})
| "--write-index" => do modifyThe LoogleOptions ({· with writeIndex := ← takeArg "--write-index"})
| "--read-index" => do modifyThe LoogleOptions ({· with readIndex := ← takeArg "--read-index"})
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
  --write-index file    persists the search index to a file
  --read-index file     read the search index from a file. This file is blindly trusted!
" ++
if compileTimeSearchPath.isEmpty then "" else "
Default search path
" ++ String.join (compileTimeSearchPath.map (fun p => s!" * {p}\n"))

unsafe def loogleCli : CliM PUnit := do
  match (← Lake.getArgs) with
  | [] => IO.println usage
  | _ => -- normal CLI
    Lake.processOptions lakeOption
    let opts ← getThe LoogleOptions
    let queries ← Lake.takeArgs
    let print := if opts.json then printJson else printPlain
    if opts.wantsHelp ||
      queries.isEmpty && not opts.interactive && opts.writeIndex.isNone
    then IO.println usage
    else work opts  fun index => do
      queries.forM (single index print)
      if opts.interactive
      then interactive index print

unsafe def main (args : List String) : IO Unit := do
  match (← (loogleCli.run args |>.run' {}).run) with
    | .ok _ => pure ()
    | .error e => IO.println e.toString
