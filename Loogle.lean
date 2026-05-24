module

public import Lean.Meta

public import Loogle.Find
public import Loogle.Parsers

public import Seccomp

public import Lean.PrettyPrinter.Delaborator.Builtins

set_option autoImplicit false

@[expose] public section

open Lean Core Meta Elab Term Command
open Loogle

meta instance : ToExpr System.FilePath where
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

def runQuery (index : Find.Index) (maxResults : Nat) (query : String) : CoreM Result :=
  withCurrHeartbeats do
    let (r, suggs) ← tryCatchRuntimeEx
      (handler := fun e => do return (.error (← e.toMessageData.toString), #[])) do
        match runStandaloneParser (← getEnv) queryParser query with
        | .error err => pure $ (.error err, #[])
        | .ok s => do
          let filters : Array Term :=
            (Syntax.SepArray.mk (sep := ", ") s.getArgs).getElems.map (⟨·⟩)
          MetaM.run' do
            match ← TermElabM.run' $ Loogle.Find.find index filters (maxShown := maxResults) with
            | .ok result => do
              let suggs ← result.suggestions.mapM Loogle.Find.renderFilters
              pure $ (.ok result, suggs)
            | .error err => do
              let suggs ← err.suggestions.mapM Loogle.Find.renderFilters
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
          let ty := (← (ppSignature ci.name).run').pretty (width := 10000)
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

def single (index : Find.Index) (maxResults : Nat) (print : Printer) (query : String) :
    CoreM Unit := do
  let r ← runQuery index maxResults query
  print r

def interactive (index : Find.Index) (maxResults : Nat) (print : Printer) : CoreM Unit := do
  IO.println "Loogle is ready."
  (← IO.getStdout).flush
  while true do
    let query := (← (← IO.getStdin).getLine).trimAscii.copy
    if query.isEmpty then break
    single index maxResults print query

/-- How the loogle binary should treat a cached index file on disk. -/
inductive IndexMode where
  /-- Do not touch any index file. -/
  | noIndex
  /-- Read the file if it exists and its depHash matches the current root
  module; otherwise build the index from scratch and write it back. -/
  | useIndex
  /-- Build the index from scratch and write it to the file unconditionally. -/
  | writeIndex
  /-- Read the file; fail if it is absent or stale. -/
  | readIndex
  deriving Inhabited, BEq

structure LoogleOptions where
  interactive : Bool := false
  json : Bool := false
  query : Option String := none
  module : String := "Mathlib"
  searchPath : List System.FilePath := []
  /-- The lifecycle of the on-disk index file. Defaults to `useIndex` because
  the speed-up from a cached index is dramatic and the location is
  predictable; pass `--index-mode none` to skip caching entirely. -/
  indexMode : IndexMode := .useIndex
  /-- Override for the index file path. When `none`, the default location is
  derived from the root module's `.olean` (swap `.olean` for `.loogle-index`). -/
  indexFile : Option System.FilePath := none
  maxResults : Nat := 200
  wantsHelp : Bool := false

/-- Try to read the `depHash` field of the Lake-generated `.trace` file sitting
next to the given module's `.olean`. Returns `none` if there is no trace file
(e.g. for stdlib modules shipped with the toolchain). Lake's `depHash` is a
hash of every transitive input (sources, import hashes, compiler version,
options), so a single comparison detects any change anywhere in the closure. -/
def readModuleDepHash (mod : Name) : IO (Option String) := do
  let oleanPath ← findOLean mod
  let tracePath := oleanPath.withExtension "trace"
  if !(← tracePath.pathExists) then
    return none
  let content ← IO.FS.readFile tracePath
  match Lean.Json.parse content with
  | .ok json => return json.getObjValAs? String "depHash" |>.toOption
  | .error _ => return none

unsafe def work (opts : LoogleOptions) (act : Find.Index → CoreM Unit) : IO Unit := do
  -- An explicit `--path` wins; otherwise honour `LEAN_PATH` (e.g. set up by
  -- `lake env`) so loogle works inside any Lake project of the same toolchain;
  -- only fall back to the build-time search path when no environment is set.
  let searchPath : SearchPath ←
    if !opts.searchPath.isEmpty then
      pure opts.searchPath
    else
      match (← IO.getEnv "LEAN_PATH") with
      | some s => pure (System.SearchPath.parse s)
      | none   => pure compileTimeSearchPath
  searchPathRef.set searchPath

  Lean.enableInitializersExecution
  -- We deliberately do not import `Loogle.Find` here: the query parser is
  -- baked into the binary via `Loogle.Parsers` and does not need the user's
  -- environment to know anything about loogle.
  let imports := #[{module := opts.module.toName}]
  let env ← importModules (loadExts := true) imports {}
  let ctx := {fileName := "/", fileMap := Inhabited.default}
  let state := {env}
  Prod.fst <$> act'.toIO ctx state
where
  /-- Default index file path: sit next to the root module's `.olean`, with the
  `.olean` suffix replaced by `.loogle-index`. -/
  defaultIndexPath : IO System.FilePath := do
    return (← findOLean opts.module.toName).withExtension "loogle-index"
  /-- `Lean.saveModuleData` (called by `pickle`) already writes to a
  `<path>.tmp.<pid>` and renames atomically, so we only need to add a
  friendly error wrapper. On a write failure (often a read-only default
  location), surface a message suggesting `--index-file`. -/
  writePickle (path : System.FilePath) (data : Find.PickledIndex) : IO Unit := do
    try
      pickle path data
    catch e =>
      let hint :=
        if opts.indexFile.isNone then
          " (the default location is derived from the root module's olean and \
           may be in a read-only build tree; pass `--index-file PATH` to \
           choose a writable location)"
        else ""
      throw <| .userError s!"loogle: failed to write index to {path}: {e}{hint}"
  /-- Try to load `path` and verify its depHash matches `curDepHash`. -/
  tryRead (curDepHash : String) (path : System.FilePath) :
      IO (Except String Find.Index) := unsafe do
    if !(← path.pathExists) then
      return .error s!"no index file at {path}"
    try
      let ((storedHash, names, trie), _) ← unpickle Find.PickledIndex path
      if storedHash != curDepHash then
        return .error s!"index at {path} is stale \
          (built against {storedHash}, current is {curDepHash})"
      return .ok (← Find.Index.mkFromCache (names, trie))
    catch e =>
      return .error s!"failed to read index at {path}: {e}"
  act' : CoreM Unit := do
    let index ← do
      if opts.indexMode == .noIndex then
        Find.Index.mk
      else match ← readModuleDepHash opts.module.toName with
      | none =>
        -- Some modules (notably stdlib modules shipped with the toolchain)
        -- have no Lake trace file, so we cannot tell whether a cached index
        -- is fresh. `read` is fatal in that case; `use` / `write` degrade to
        -- a one-shot in-memory build.
        let msg := s!"no Lake trace file for {opts.module}; cannot verify \
          index freshness — running without an on-disk index"
        if opts.indexMode == .readIndex then
          throwError s!"loogle: {msg}"
        IO.eprintln s!"loogle: {msg}"
        Find.Index.mk
      | some curDepHash =>
        let path ← match opts.indexFile with
          | some p => pure p
          | none => defaultIndexPath
        let writeFresh : CoreM Find.Index := do
          let idx ← Find.Index.mk
          let (names, trie) ← idx.getCache
          writePickle path (curDepHash, names, trie)
          return idx
        match opts.indexMode with
        | .noIndex => Find.Index.mk  -- unreachable
        | .readIndex =>
          match ← tryRead curDepHash path with
          | .ok idx => pure idx
          | .error msg => throwError s!"loogle: {msg}"
        | .useIndex =>
          match ← tryRead curDepHash path with
          | .ok idx => pure idx
          | .error msg =>
            IO.eprintln s!"loogle: {msg}; rebuilding."
            writeFresh
        | .writeIndex =>
          writeFresh

    -- Warm up the cache eagerly *before* `Seccomp.enable`. The first access
    -- spawns a worker thread; doing that here keeps query-time entirely
    -- inside the syscalls the seccomp filter allows. Critical for the
    -- read-from-file path, where there is no other cache touch beforehand.
    let _ ← index.1.cache.get.run'
    let _ ← index.2.cache.get.run'

    Seccomp.enable
    act index

