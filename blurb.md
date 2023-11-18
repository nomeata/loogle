## About
Loogle searches of Lean and Mathlib definitions and theorems.

You may also want to try the [CLI version](https://github.com/nomeata/loogle), the [VS Code extension](https://marketplace.visualstudio.com/items?itemName=ShreyasSrinivas.loogle-lean), the [`lean.nvim` integration](https://github.com/Julian/lean.nvim#features) or the [Zulip bot](https://github.com/nomeata/loogle#zulip-bot).

## Usage

Loogle finds definitions and lemmas in various ways:

1. By constant:\
   🔍 [`Real.sin`](/?q=Real.sin)\
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:\
   🔍 [`"differ"`](/?q="differ")\
   finds all lemmas that have `"differ"` somewhere in their lemma _name_.

3. By subexpression:\
   🔍 [`_ * (_ ^ _)`](/?q=_+*+(_+^+_))\
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power.

   The pattern can also be non-linear, as in\
   🔍 [`Real.sqrt ?a * Real.sqrt ?a`](/?q=Real.sqrt+%3Fa+*+Real.sqrt+%3Fa)

   If the pattern has parameters, they are matched in any order. Both of these will find `List.map`:\
   🔍 [`(?a -> ?b) -> List ?a -> List ?b`](/?q=(?a -> ?b) -> List ?a -> List ?b)\
   🔍 [`List ?a -> (?a -> ?b) -> List ?b`](/?q=List ?a -> (?a -> ?b) -> List ?b)

4. By main conclusion:\
   🔍 [`|- tsum _ = _ * tsum _`](/?q=|- tsum _ = _ * tsum _)\
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape.

   As before, if the pattern has parameters, they are matched against the hypotheses of
   the lemma in any order; for example,\
   🔍 [`|- _ < _ → tsum _ < tsum _`](/?q=|- _ < _ → tsum _ < tsum _)\
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.


If you pass more than one such search filter, separated by commas Loogle will return lemmas which match _all_ of them.
The search\
🔍 [`Real.sin, "two", tsum, _ * _, _ ^ _, |- _ < _ → _`](/?q=Real.sin,+"two",+tsum,+_+*+_,+_+^+_,+|-+_+<+_+→+_)\
woould find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
substring of the lemma name, include a product and a power somewhere in the type, *and* have a
hypothesis of the form `_ < _` (if there were any such lemmas). Metavariables (`?a`) are assigned independently in each filter.

The `#lucky` button will directly send you to the documentation of the first hit.

## Source code

You can find the source code for this service at <https://github.com/nomeata/loogle>.
The <https://loogle.lean-lang.org/> service is currently provided by Joachim Breitner <<mail@joachim-breitner.de>>.
