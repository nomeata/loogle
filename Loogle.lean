import Lean.Meta
import Lake.CLI.Error
import Lake.Util.Cli

import Loogle.Find

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
open Loogle

instance : ToExpr System.FilePath where
  toTypeExpr := Lean.mkConst ``System.FilePath
  toExpr path := mkApp (Lean.mkConst ``System.FilePath.mk) (toExpr path.1)

elab "#compileTimeSearchPath" : term => do
  let path ← searchPathRef.get
  let path' :=
    -- A little hack to not embed the searchpath when building under nix
    if path.any (fun p => p.toString.startsWith "/nix/store")
    then [] else path
  return toExpr path'
def compileTimeSearchPath : SearchPath := #compileTimeSearchPath

/-- Like `Find.Failure`, but without syntax references and with syntax pretty-printed -/
abbrev Failure := String

def Result := (Except Failure Find.Result × Array String × Nat)
def Printer := Result → CoreM Unit

def runQuery (index : Find.Index) (query : String) : CoreM Result :=
  withCurrHeartbeats do
    let (r, suggs) ← tryCatchRuntimeEx
      (handler := fun e => do return (.error (← e.toMessageData.toString), #[])) do
        match Parser.runParser (← getEnv) `Loogle.Find.find_filters query with
        | .error err => pure $ (.error err, #[])
        | .ok s => do
          MetaM.run' do
            match ← TermElabM.run' $ Loogle.Find.find index (.mk s) with
            | .ok result => do
              let suggs ← result.suggestions.mapM fun sugg => do
                return (← PrettyPrinter.ppCategory ``Find.find_filters sugg).pretty
              pure $ (.ok result, suggs)
            | .error err => do
              let suggs ← err.suggestions.mapM fun sugg => do
                return (← PrettyPrinter.ppCategory ``Find.find_filters sugg).pretty
              return (.error (← err.message.toString), suggs)
    let heartbeats := ((← IO.getNumHeartbeats) - (← getInitHeartbeats )) / 1000
    return (r, suggs, heartbeats)

def printPlain : Printer
  | (.error err, suggs, _) => do
    IO.println err
    unless suggs.isEmpty do
    IO.println "Maybe you meant:"
    suggs.forM (fun s => IO.println ("* " ++ s))
  | (.ok result, _) => do
    IO.println (← result.header.toString)
    result.hits.forM fun (ci, mod) => match mod with
      | none => IO.println s!"{ci.name}" -- unlikely to happen in CLI usage
      | some mod => IO.println s!"{ci.name} (from {mod})"

open PrettyPrinter in
/-- Like PrettyPrinter.ppSignature, but omits the id -/
def ppSignature (name : Name) : MetaM Format := withCurrHeartbeats do
  tryCatchRuntimeEx do
    let e ← mkConstWithLevelParams name
    let (stx, _infos) ← delabCore e (delab := Delaborator.delabConstWithSignature)
    let stx : Syntax := stx
    -- stx[1] picks out the signature
    ppTerm ⟨stx[1]⟩
   fun e =>
    return f!"[Failed to pretty-print signature: {← e.toMessageData.format}]"


def toJson : Result → CoreM Json -- only in IO for MessageData.toString
  | (.error err, suggs, heartbeats) => do
      if suggs.isEmpty then
        pure $ .mkObj [ ("error", .str err), ("heartbeats", heartbeats) ]
      else
        pure $ .mkObj [ ("error", .str err), ("suggestions", .arr (suggs.map .str)), ("heartbeats", heartbeats)]
  | (.ok result, suggs, heartbeats) => do
      pure $ .mkObj $ [
        ("header", .str (← result.header.toString)),
        ("heartbeats", .num heartbeats),
        ("count", .num result.count),
        ("hits", .arr $ ← result.hits.mapM fun (ci, mod) => do
          let ty := (← (ppSignature ci.name).run').pretty
          let ds := match ← findDocString? (← getEnv) ci.name false with
            | some s => .str s
            | none => .null
          let mod := match mod with | none => .null | some name => .str name.toString
          return .mkObj [
            ("name", .str ci.name.toString),
            ("type", .str ty),
            ("module", mod ),
            ("doc", ds )
          ]
        )
      ] ++
      (if suggs.isEmpty then [] else [
        ("suggestions", .arr (suggs.map .str))
      ])

def printJson : Printer := fun r => do
  IO.println (← toJson r).compress
  (← IO.getStdout).flush

def single (index : Find.Index) (print : Printer) (query : String) : CoreM Unit := do
  let r ← runQuery index query
  print r

def interactive (index : Find.Index) (print : Printer) : CoreM Unit := do
  IO.println "Loogle is ready."
  (← IO.getStdout).flush
  while true do
    let query := (← (← IO.getStdin).getLine).trim
    if query.isEmpty then break
    single index print query

structure LoogleOptions where
  interactive : Bool := false
  json : Bool := false
  query : Option String := none
  module : String := "Mathlib"
  searchPath : List System.FilePath := []
  writeIndex : Option String := none
  readIndex : Option String := none
  wantsHelp : Bool := false

unsafe def work (opts : LoogleOptions) (act : Find.Index → CoreM Unit) : IO Unit := do
  if opts.searchPath.isEmpty
  then searchPathRef.set compileTimeSearchPath
  else searchPathRef.set opts.searchPath

  Lean.enableInitializersExecution
  let imports := #[{module := opts.module.toName}, {module := `Loogle.Find}]
  let env ← importModules (loadExts := true) imports {}
  let ctx := {fileName := "/", fileMap := Inhabited.default}
  let state := {env}
  Prod.fst <$> act'.toIO ctx state
where act' : CoreM Unit := do
  let index ← match opts.readIndex with
  | some path => do
    let (index, _) ← unpickle _ path
    Find.Index.mkFromCache index
  | none =>
    -- Special-case Mathlib and use the cached index if present
    if opts.writeIndex.isNone && opts.module.toName = `Mathlib
    then Find.cachedIndex.get
    else Find.Index.mk
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
| "--path" => do
    let path : System.FilePath ← takeArg "--path"
    modifyThe LoogleOptions fun opts => {opts with searchPath := opts.searchPath ++ [path]}
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
