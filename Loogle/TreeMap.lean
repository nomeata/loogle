import Std
namespace Std.TreeSet

variable {α : Type _} {cmp}

-- from https://github.com/leanprover-community/mathlib4/blob/c0a057e453edb8d89d4b2eaeeb8e0eb0f714f715/Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean#L40-L45

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`.
If equal keys exist in both, the key from `t₂` is preferred.
-/
def union_loogle (t₁ t₂ : TreeSet α cmp) : TreeSet α cmp :=
  t₂.foldl .insert t₁

/-- The intersection of a (non-empty) array of `RBTree`s. If
the input is empty, the empty tree is returned. -/
def intersects_loogle (ts : Array (TreeSet α cmp)) : TreeSet α cmp :=
  if ts.isEmpty then {} else
  -- sorts smallest set to the back, and iterate over that one
  -- TODO: An `RBTree` admits bulk operations, which could replace this implementation
  let ts := ts.qsort (·.size > ·.size)
  ts.back!.foldl (init := {}) fun s m =>
    if ts.pop.all (·.contains m) then s.insert m else s


end Std.TreeSet
