import Aesop
import Lean.Meta
import Mathlib.Tactic.Find
import Mathlib.Tactic.ToExpr
import Mathlib.Tactic.RunCmd
-- import Seccomp

open Lean Core Meta Elab Term Command

elab "compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

def Result := Except String (String × Array Lean.Name)
def Printer := Result → IO Unit 

def runQuery (query : String) : CoreM Result  := do
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

unsafe def work (mod : String) (act : CoreM Unit) : IO Unit := do
  searchPathRef.set compileTimeSearchPath
  withImportModules [{module := mod.toName}, {module := `Mathlib.Tactic.Find}] {} 0 fun env => do
    let ctx := {fileName := "/", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> act'.toIO ctx state
  where act' := do
    -- warm up the cache eagerly
    let _ ← MetaM.run' $ Mathlib.Tactic.Find.findDeclsByConsts.get
    -- Seccomp.enable
    act

unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["-i"] => work "Mathlib" (interactive printPlain)
  | ["-j"] => work "Mathlib" (interactive printJson)
  | [query] => work "Mathlib" (single printPlain query)
  | [mod, "-i"] => work mod (interactive printPlain)
  | [mod, "-j"] => work mod (interactive printJson)
  | [mod, query] => work mod (single printPlain query)
  | _ => IO.println "Usage: loogle [module] query"
