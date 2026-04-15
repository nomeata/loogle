/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public meta import Loogle.Find

public meta section

namespace Loogle.Find

open Lean.Elab.Command

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

`#find` maintains an index of which lemmas mention which other constants and name fragments.
If you have downloaded the olean cache for mathlib, the index will be precomputed. If not,
the _first_ use of `#find` in a module will be slow (in the order of minutes). If you cannot use
the distributed cache, it may be useful to open a scratch file, `import Mathlib`, and use `#find`
there, this way you will find lemmas that you have not yet imported, and the
cache will stay up-to-date.

By default `#find` prints names and types of found definitions and lemmas. You can also make it print
names only by setting `find.showType` to `false`:

```lean
set_option find.showTypes false
```
-/
elab(name := findSyntax) "#find " args:find_filters : command =>
  liftTermElabM $ elabFind args

@[inherit_doc findSyntax]
elab(name := findSyntaxTac) "#find " args:find_filters : tactic =>
  elabFind args
