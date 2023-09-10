import Lean.Meta
import Lake.CLI.Error
import Lake.Util.Cli
import Std.Util.Pickle
import Lean.Data.Trie
import Mathlib.Lean.Expr.Basic

import Loogle.Seccomp
import Loogle.Trie2

set_option autoImplicit false

open Lean Core Meta Elab Term Command

def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName


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

def Result := NameSet
def Printer := Result → IO Unit 

def Index := Trie (Array Name)

def runQuery (index : Index) (query : String) : CoreM Result  := withCurrHeartbeats do
    let hits : NameSet := index.findPrefix query |>.foldl (init := .empty) fun s a =>
      a.foldl (init := s) .insert
    return hits

def printPlain : Printer
  | hits => IO.println s!"Found {hits.size} hits"

def single (print : Printer) (index : Index) (query : String) : CoreM Unit := do
  let r ← runQuery index query
  print r

def interactive (print : Printer) (index : Index) : CoreM Unit := do
  while true do
    let query := (← (← IO.getStdin).getLine).trim
    if query.isEmpty then break
    single print index query

structure LoogleOptions where
  interactive : Bool := false
  json : Bool := false
  query : Option String := none
  module : String := "Mathlib"
  searchPath : Option String := none
  writeIndex : Option String := none
  readIndex : Option String := none
  wantsHelp : Bool := false

unsafe def work (opts : LoogleOptions) (act : Index → CoreM Unit) : IO Unit := do
  if let some p := opts.searchPath
  then searchPathRef.set [p]
  else searchPathRef.set compileTimeSearchPath

  let imports := [{module := opts.module.toName}, {module := `Mathlib.Tactic.Find}]
  withImportModules imports {} 0 fun env => do
    let ctx := {fileName := "/", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> act'.toIO ctx state
  where act' : CoreM Unit := do
    let index ← match opts.readIndex with
    | some path => do
      let (index, _) ← unpickle Index path
      pure index
    | none => do
        let mut t : Index := .empty
        let env ← getEnv
        for ⟨n, _⟩ in env.constants.toList do
          unless  ← isBlackListed n do
            let s := n.toString
            for i in List.range (s.length - 1) do -- -1 to not consider the empty suffix
              let suf := s.drop i
              t := t.upsert suf fun ns? => ns? |>.getD #[] |>.push n
        pure t
      if let some path := opts.writeIndex then pickle path index
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
    let print := printPlain
    if opts.wantsHelp ||
      queries.isEmpty && not opts.interactive && opts.writeIndex.isNone
    then IO.println usage
    else work opts fun index => do
      queries.forM (single print index)
      if opts.interactive
      then interactive print index

unsafe def main (args : List String) : IO Unit := do
  match (← (loogleCli.run args |>.run' {}).run) with
    | .ok _ => pure ()
    | .error e => IO.println e.toString
