/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Loogle.Find
public import Loogle.BaseIOThunk
public meta import Loogle.Find
public meta import Loogle.BaseIOThunk
public meta import Lean
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.TryThis

public meta section

namespace Loogle.Find

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Tactic Lean.Meta

/-- Process-local index used by the in-Lean `#find` command. The first call
to `#find` in a Lean session triggers a full scan of the imported
environment; the resulting caches live for the lifetime of the process. -/
initialize cachedIndex : Loogle.Thunk Index ← Loogle.Thunk.new Index.mk

/-- Option to control whether `#find` should print types of found lemmas. -/
register_option find.showTypes : Bool := {
  defValue := true
  descr    := "showing types in #find"
}

private def elabFind (ref : Lean.Syntax) (filters : Array (Lean.TSyntax `term)) :
    TermElabM Unit := do
  match ← find (← cachedIndex.get) filters with
  | .error ⟨refErr, warn, suggestions⟩ => do
    Lean.logErrorAt refErr warn
    unless suggestions.isEmpty do
      let suggs : Array Lean.Meta.Tactic.TryThis.Suggestion ← suggestions.mapM fun sugg => do
        return { suggestion := .string (← renderFilters sugg) }
      Lean.Meta.Tactic.TryThis.addSuggestions ref suggs
  | .ok result => do
    let showTypes := (← Lean.MonadOptions.getOptions).get
        find.showTypes.name find.showTypes.defValue
    let names := result.hits.map fun x => (x.1.name, x.1.type)
    Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConstsAndTypes names showTypes)

/--
The `#find` command finds definitions and lemmas in various ways. One can search by: the constants
involved in the type; a substring of the name; a subexpression of the type; or a subexpression
located in the return type or a hypothesis specifically. All of these search methods can be
combined in a single query, comma-separated.

1. By constant:
   ```lean
   #find Real.sin
   ```
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:
   ```lean
   #find "differ"
   ```
   finds all lemmas that have `"differ"` somewhere in their lemma _name_.
   This check is case-insensitive.

3. By subexpression:
   ```lean
   #find _ * (_ ^ _)
   ```
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power.

   The pattern can also be non-linear, as in
   ```lean
   #find Real.sqrt ?a * Real.sqrt ?a
   ```

   If the pattern has parameters, they are matched in any order. Both of these will find `List.map`:
   ```
   #find (?a -> ?b) -> List ?a -> List ?b
   #find List ?a -> (?a -> ?b) -> List ?b
   ```

4. By main conclusion:
   ```lean
   #find ⊢ tsum _ = _ * tsum _
   ```
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape.

   As before, if the pattern has parameters, they are matched against the hypotheses of
   the lemma in any order; for example,
   ```lean
   #find ⊢ _ < _ → tsum _ < tsum _
   ```
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.


If you pass more than one such search filter, `#find` will return lemmas which match _all_ of them.
The search
```lean
#find Real.sin, "two", tsum,  _ * _, _ ^ _, ⊢ _ < _ → _
```
will find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
substring of the lemma name, include a product and a power somewhere in the type, *and* have a
hypothesis of the form `_ < _`.

`#find` maintains a per-process index of which lemmas mention which other constants and name
fragments. The first use in a Lean session is slow (in the order of minutes on Mathlib);
subsequent uses reuse the in-memory index.

By default `#find` prints names and types of found definitions and lemmas. You can also make it print
names only by setting `find.showTypes` to `false`:

```lean
set_option find.showTypes false
```
-/
elab(name := findSyntax) s:"#find " args:term,* : command =>
  liftTermElabM <| elabFind s args.getElems

@[inherit_doc findSyntax]
elab(name := findSyntaxTac) s:"#find " args:term,* : tactic =>
  elabFind s args.getElems

end Loogle.Find
