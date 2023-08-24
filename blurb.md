## Try these:

* [`Real.sin`](?q=Real.sin)
* [`Real.sin tsum`](?q=Real.sin tsum)
* [`(Real.sin (_ + 2*Real.pi))`](?q=(Real.sin (_ %2B 2*Real.pi)))
* [`(List.replicate (_ + _) _)`](?q=(List.replicate (_ %2B _) _))
* [`(Real.sqrt ?a * Real.sqrt ?a)`](?q=(Real.sqrt %3Fa * Real.sqrt %3Fa))

## Documentation

This website gives access to the `#find` command to search through mathlib for definitions and lemmas in various ways. One can search by: the constants
involved in the type; a substring of the name; a subexpression of the type; or a subexpression
located in the return type or a hypothesis specifically. All of these search methods can be
combined in a single query.


1. By constant:
   ```lean
   #find Real.sin
   ```
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:
   ```lean
   #find "two"
   ```
   finds all lemmas that have `"two"` as part of the lemma _name_.

3. By subexpression:
   ```lean
   #find (_ * (_ ^ _))
   ```
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power. The pattern can also be non-linear, as in
   ```lean
   #find (Real.sqrt ?a * Real.sqrt ?a)
   ```

4. By conclusion and/or hypothesis:
   ```lean
   #find ⊢ (tsum _ = _ * tsum _)
   ```
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape. If the pattern has hypotheses, they are matched against the hypotheses of
   the lemma in any order; for example,
   ```lean
   #find ⊢ (_ < _ → tsum _ < tsum _)
   ```
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.
5. In combination:
   ```lean
   #find Real.sin "two" tsum  (_ * _) (_ ^ _) ⊢ (_ < _ → _)
   ```
   will find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
   substring of the lemma name, include a product and a power somewhere in the type, *and* have a
   hypothesis of the form `_ < _`.

If you pass more than one such search filter, `#find` will only return lemmas which match _all_ of
them simultaneously. At least some filter must mention a concrete name, because `#find` maintains
an index of which lemmas mention which other constants. This is also why the _first_ use of `#find`
will be somewhat slow (typically less than half a minute with all of `Mathlib` imported), but
subsequent uses are faster.

## Source code

You can find the source code for this service at <https://github.com/nomeata/loogle>.


