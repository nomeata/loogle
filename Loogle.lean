import Lean.Meta
import Mathlib.Tactic.Find
import Mathlib.Tactic.ToExpr
import Mathlib.Tactic.RunCmd
import Seccomp

open Lean Core Meta Elab Term Command

elab "compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

def runQuery (query : String) : CoreM Unit := do
  match Parser.runParserCategory (← getEnv) `find_patterns query with
  | .error err => IO.println err
  | .ok s => do
    MetaM.run' do
      let args ← TermElabM.run' $ Mathlib.Tactic.Find.parseFindPatterns (.mk s)
      match ← Mathlib.Tactic.Find.find args with
      | .ok (header, names) => do
          IO.println (← header.toString)
          names.forM (fun name => IO.println name)
      | .error err => IO.println (← err.toString)

def interactive : CoreM Unit := do
  while true do
    let query := (← (← IO.getStdin).getLine).trim
    if query.isEmpty then break
    runQuery query

unsafe def work (mod : String) (act : CoreM Unit) : IO Unit := do
  searchPathRef.set compileTimeSearchPath
  withImportModules [{module := mod.toName}, {module := `Mathlib.Tactic.Find}] {} 0 fun env => do
    Seccomp.enable
    let ctx := {fileName := "", fileMap := Inhabited.default}
    let state := {env}
    Prod.fst <$> act.toIO ctx state

unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["-i"] => work "Mathlib" interactive
  | [query] => work "Mathlib" (runQuery query)
  | [mod, "-i"] => work mod interactive
  | [mod, query] => work mod (runQuery query)
  | _ => IO.println "Usage: loogle [module] query"
