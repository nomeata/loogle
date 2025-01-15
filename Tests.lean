import Loogle.Find

-- We want the following tests to be self-contained.
-- Therefore we erase all knowledge about imported definitios from find:

elab (name := erase_loogle_cache) "erase_loogle_cache " : command => do
  Loogle.Find.cachedIndex.1.cache.set (.inr (.pure (pure (.empty, .empty))))
  Loogle.Find.cachedIndex.2.cache.set (.inr (.pure (pure (.empty, .empty))))

erase_loogle_cache

/-- error: Cannot search: No constants or name fragments in search pattern. -/
#guard_msgs in
#find

/-- info: Found 0 definitions whose name contains "namefragmentsearch". -/
#guard_msgs in
#find "namefragmentsearch"

/-- We use this definition in all tests below to get reproducible results,
including the statistics about how many lemas were found in the index. -/
def my_true : Bool := true

theorem my_true_eq_true : my_true = true := rfl

theorem my_true_eq_True : my_true = true := rfl -- intentionally capitalized

/--
info: Found 3 definitions mentioning my_true.
• my_true : Bool
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find my_true

/--
info: Found 3 definitions whose name contains "my_true".
• my_true : Bool
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find "my_true"

/--
info: Found 3 definitions whose name contains "y_tru".
• my_true : Bool
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find "y_tru"

/--
info: Found 3 definitions mentioning my_true.
Of these, 2 have a name containing "eq".
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find my_true, "eq"

/--
info: Found 2 definitions mentioning Bool, my_true and Eq.
Of these, 2 match your pattern(s).
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find my_true = _

/--
info: Found 2 definitions mentioning Bool, my_true and Eq.
Of these, 0 match your pattern(s).
-/
#guard_msgs in
#find (_ = my_true)

/--
error: unknown identifier 'doesn'texist'
---
info: Try these:
• "doesn'texist"
-/
#guard_msgs in
#find doesn'texist


/-- error: unknown identifier 'doesn'texist' -/
#guard_msgs in
#find (doesn'texist = _)

/-- error: Cannot search for _. Did you forget to put a term pattern in parentheses? -/
#guard_msgs in
#find my_true, _

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test1 {n m : Nat} :
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n () := by
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test2 {n m : Nat} :
  List.replicate n () ++ List.replicate m () = List.replicate (n + m) () := by
  sorry

/--
info: Found 2 definitions mentioning List.replicate, List and HAppend.hAppend.
Of these, one matches your pattern(s).
• non_linear_pattern_test1 : ∀ {n : Nat} {m : Nat},
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n ()
-/
#guard_msgs in
#find List.replicate ?n _ ++ List.replicate ?n _

/--
info: Found 2 definitions mentioning List.replicate, List and HAppend.hAppend.
Of these, 2 match your pattern(s).
• non_linear_pattern_test2 : ∀ {n m : Nat}, List.replicate n () ++ List.replicate m () = List.replicate (n + m) ()
• non_linear_pattern_test1 : ∀ {n : Nat} {m : Nat},
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n ()
-/
#guard_msgs in
#find List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, List, Eq and HAppend.hAppend.
Of these, one matches your pattern(s).
• non_linear_pattern_test1 : ∀ {n : Nat} {m : Nat},
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n ()
-/
#guard_msgs in
#find |- _ = List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, List, Eq and HAppend.hAppend.
Of these, one matches your pattern(s).
• non_linear_pattern_test2 : ∀ {n m : Nat}, List.replicate n () ++ List.replicate m () = List.replicate (n + m) ()
-/
#guard_msgs in
#find |- List.replicate ?n _ ++ List.replicate ?m _ = _

theorem hyp_ordering_test1 {n : Nat} (h : 0 < n) (_ : n + n = 6 * n): 0 ≤ n := Nat.le_of_lt h
theorem hyp_ordering_test2 {n : Nat} (_ : n + n = 6 * n) (h : 0 < n) : 0 ≤ n := Nat.le_of_lt h

/--
info: Found 2 definitions mentioning LE.le, LT.lt and OfNat.ofNat.
Of these, 2 match your pattern(s).
• hyp_ordering_test1 : ∀ {n : Nat}, 0 < n → n + n = 6 * n → 0 ≤ n
• hyp_ordering_test2 : ∀ {n : Nat}, n + n = 6 * n → 0 < n → 0 ≤ n
-/
#guard_msgs in
#find ⊢ 0 < ?n → _ ≤ ?n


-- Regression test

section LinearPatternTest
namespace LinearPatternTest

class Star (R : Type _) where star : R → R
export Star(star)

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem star_comm_self' {R} [Mul R] [Star R] (x : R) : star x * x = x * star x := sorry

/--
info: Found 2 definitions mentioning star.
Of these, one matches your pattern(s).
• star_comm_self' : ∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x : R), star x * x = x * star x
-/
#guard_msgs in
#find star _

/--
info: Found one definition mentioning HMul.hMul, star and Eq.
Of these, one matches your pattern(s).
• star_comm_self' : ∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x : R), star x * x = x * star x
-/
#guard_msgs in
#find star ?a * ?a = ?a * star ?_

/--
info: Found one definition mentioning HMul.hMul, star and Eq.
Of these, one matches your pattern(s).
• star_comm_self' : ∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x : R), star x * x = x * star x
-/
#guard_msgs in
#find star ?a * ?a = ?b * star ?b


end LinearPatternTest

section ListMapTest

open Loogle.Find
open Lean Elab Command

elab s:"#assert_match " name_s:ident concl:(turnstyle)? query:term : command => liftTermElabM do
    let pat ← Loogle.Find.elabTerm' query none
    let name := Lean.TSyntax.getId name_s
    let matcher ←
      if concl.isSome
      then matchConclusion pat
      else matchAnywhere pat
    let c := (← getEnv).constants.find! name
    unless ← matcher c do
      logErrorAt s "Pattern does not match when it should!"

#assert_match List.map (?a -> ?b) -> List ?a -> List ?b
#assert_match List.map List ?a → (?a -> ?b) -> List ?b
#assert_match List.map |- (?a -> ?b) -> List ?a -> List ?b
#assert_match List.get |- List ?a -> ?a

end ListMapTest

section DefaultingTest

set_option autoImplicit true

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem test_with_zero {α} [Zero α] [HMul α α α] [LE α] {a : α}: 0 ≤ a * a := sorry

-- Tests the defaulting does not kick in below

#assert_match test_with_zero |- 0 ≤ ?a * ?a

end DefaultingTest


/-- error: Name pattern is too general -/
#guard_msgs in
#find ""

/-- error: Name pattern is too general -/
#guard_msgs in
#find "."

/--
info: Found 2 definitions whose name contains "my_true_eq_True".
• my_true_eq_True : my_true = true
• my_true_eq_true : my_true = true
-/
#guard_msgs in
#find "my_true_eq_True" -- checks for case-insensitivity


-- Check that |- only allows Sort-typed things

/--
info: Found 0 definitions mentioning And and True.
Of these, 0 match your pattern(s).
-/
#guard_msgs in
#find And True

/-- error: Conclusion pattern is of type Bool, should be of type `Sort` -/
#guard_msgs in
#find |- true

/-- error: Conclusion pattern is of type Prop → Prop, should be of type `Sort` -/
#guard_msgs in
#find |- And True

/--
info: Found 0 definitions mentioning And, True and my_true.
Of these, 0 match your pattern(s).
-/
#guard_msgs in
#find |- And True True, my_true


-- Searching for qualified names

def Namespaced.TestDefinition := true

theorem TestDefinition_eq_true:
  Namespaced.TestDefinition = true := rfl

/--
error: unknown identifier 'TestDefinition'
---
info: Try these:
• "TestDefinition"
• Namespaced.TestDefinition
-/
#guard_msgs in
#find TestDefinition


-- Handlig duplcats

def NamespacedA.AnotherTestDefinition := true
def NamespacedB.AnotherTestDefinition := true
def NamespacedC.AnotherTestDefinition := true
theorem NamespcedA.AnotherTestDefinition_eq_true:
  NamespacedA.AnotherTestDefinition = true := rfl
theorem NamespcedB.AnotherTestDefinition_eq_true:
  NamespacedB.AnotherTestDefinition = true := rfl

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try these:
• "AnotherTestDefinition"
• NamespacedA.AnotherTestDefinition
• NamespacedB.AnotherTestDefinition
• NamespacedC.AnotherTestDefinition
-/
#guard_msgs in
#find AnotherTestDefinition

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try these:
• "some string before", "AnotherTestDefinition", some (Expr after)
• "some string before", NamespacedA.AnotherTestDefinition, some (Expr after)
• "some string before", NamespacedB.AnotherTestDefinition, some (Expr after)
• "some string before", NamespacedC.AnotherTestDefinition, some (Expr after)
-/
#guard_msgs in
#find "some string before", AnotherTestDefinition, some (Expr after)

-- doesn't give suggestions (yet)

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try these:
• "some string before", NamespacedA.AnotherTestDefinition = _, some (Expr after)
• "some string before", NamespacedB.AnotherTestDefinition = _, some (Expr after)
• "some string before", NamespacedC.AnotherTestDefinition = _, some (Expr after)
-/
#guard_msgs in
#find "some string before", AnotherTestDefinition = _, some (Expr after)

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try these:
• "some string before", |- NamespacedA.AnotherTestDefinition = _, some (Expr after)
• "some string before", |- NamespacedB.AnotherTestDefinition = _, some (Expr after)
• "some string before", |- NamespacedC.AnotherTestDefinition = _, some (Expr after)
-/
#guard_msgs in
#find "some string before", |- AnotherTestDefinition = _, some (Expr after)

-- The following check checks that a type error (or other error) at an identifier
-- that can be resolved doesn't make #find look for possible candidates

/--
error: application type mismatch
  Nat.add 0 my_true
argument
  my_true
has type
  Bool : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
#find Nat.add 0 my_true


-- A pattern with a coercion

inductive A where | A1 : A | A2 : A
inductive B where | mk : B
def B.ofA : A → B | A.A1 => B.mk | A.A2 => B.mk
instance : Coe A B where coe := B.ofA

def findThisLemma : A.A1 = B.mk := rfl
def doNotFindThisLemma : ∀ a, a = B.mk := fun _a => rfl

/--
info: Found one definition mentioning B, A.A1, B.ofA, B.mk and Eq.
Of these, one matches your pattern(s).
• findThisLemma : B.ofA A.A1 = B.mk
-/
#guard_msgs in
#find A.A1 = B.mk


/--
info: Found one definition mentioning B, A.A1, B.ofA, B.mk and Eq.
Of these, one matches your pattern(s).
• findThisLemma : B.ofA A.A1 = B.mk
-/
#guard_msgs in
#find Eq B.mk A.A1


set_option pp.raw true

/--
info: Found one definition mentioning B, A.A1, B.ofA, B.mk and Eq.
Of these, one matches your pattern(s).
• findThisLemma : Eq.{1} B (B.ofA A.A1) B.mk
-/
#guard_msgs in
#find ↑A.A1 = B.mk


def this_peculiar_name_repeats_a_peculiar_substring := true
def this_other_peculiar_name_repeats_a_peculiar_substring := true
/--
info: Found 2 definitions whose name contains "peculiar".
• this_other_peculiar_name_repeats_a_peculiar_substring : Bool
• this_peculiar_name_repeats_a_peculiar_substring : Bool
-/
#guard_msgs in
#find "peculiar"


/--
info: Found 2 definitions whose name contains "peculiar".
Of these, one has a name containing "peculiar" and "the".
• this_other_peculiar_name_repeats_a_peculiar_substring : Bool
-/
#guard_msgs in
#find "peculiar", "the"

-- To make find not to print types of found definitions and lemmas use `find.showTypes` option

set_option find.showTypes false

/--
info: Found 3 definitions mentioning my_true.
Of these, 2 have a name containing "eq".
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find my_true, "eq"
