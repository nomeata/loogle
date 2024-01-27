import Loogle.Trie
import Std.Data.ByteArray

set_option autoImplicit false

@[simp]
axiom String.utf8ByteSize_eq_toUTF8_size (s : String) : s.utf8ByteSize = s.toUTF8.size

@[simp]
axiom String.getUtf8Byte_eq_toUTF8_get (s : String) (i : Nat) (h : i < s.utf8ByteSize) :
  s.getUtf8Byte i h = s.toUTF8.get ⟨i, s.utf8ByteSize_eq_toUTF8_size ▸ h⟩

axiom String.toUTF8_inj (s₁ s₂ : String) (h : s₁.toUTF8 = s₂.toUTF8) : s₁ = s₂

macro "simp_utf8" : tactic =>
  `(tactic|simp only [String.getUtf8Byte_eq_toUTF8_get, String.utf8ByteSize_eq_toUTF8_size] at *)

@[simp]
theorem ByteArray.toList_mk (bs : Array UInt8) : (ByteArray.mk bs).toList = bs.toList := sorry

@[simp]
theorem ByteArray.toList_push (bs : ByteArray) (c : UInt8) :
  (bs.push c).toList = bs.toList ++ [c] := sorry

theorem ByteArray.size_list (bs : ByteArray) :
  bs.size = bs.toList.length := sorry

theorem ByteArray.findIdx_list (bs : ByteArray) (p : UInt8 → Bool) :
  bs.findIdx? p = bs.toList.findIdx? p := sorry

theorem ByteArray.get_list (bs : ByteArray) (i : Fin bs.size) :
  bs.get i = bs.toList.get (i.cast (bs.size_list)) := sorry

theorem List.nodup_snoc :
  ∀ {α : Type _} {a : α} {l : List α}, List.Nodup (l ++ [a]) ↔ a ∉ l ∧ List.Nodup l := sorry

theorem Array.get?_modify {α : Type _} (ts : Array α) (i j : Nat) (f : α → α) :
  (ts.modify i f).get? j = (if i = j then (ts.get? i).map f else ts.get? j) := sorry

open Loogle

@[simp]
theorem Trie.hasPrefix_empty {s : String} {i : Nat} :
    Trie.hasPrefix s .empty i = true := by
  unfold Trie.hasPrefix Trie.hasPrefix.loop
  simp


theorem Trie.commonPrefix_differs
  (s₁ : String) (s₂ : ByteArray) (offset1 : Nat)
  (h1 : offset1 + Trie.commonPrefix s₁ s₂ offset1 < s₁.toUTF8.size)
  (h2 : Trie.commonPrefix s₁ s₂ offset1 < s₂.size) :
  s₁.toUTF8.get ⟨offset1 + Trie.commonPrefix s₁ s₂ offset1, h1⟩
    ≠ ByteArray.get! s₂ (Trie.commonPrefix s₁ s₂ offset1) := sorry

theorem Trie.commonPrefix_differs_head
  (s₁ : String) (s₂ : ByteArray) (offset1 : Nat)
  (heq0 : Trie.commonPrefix s₁ s₂ offset1 = 0)
  (h1 : offset1 < s₁.toUTF8.size)
  (h2 : 0 < s₂.size) :
  s₁.toUTF8.get ⟨offset1, h1⟩ ≠ ByteArray.get! s₂ 0 := by
    have := Trie.commonPrefix_differs s₁ s₂ offset1
    simp only [heq0, Nat.add_zero] at this
    apply this <;> assumption


inductive Trie.valid {α} : Trie α → Prop
  | leaf (v : Option α) : valid (.leaf v)
  | path (v : Option α)
    (ps : ByteArray) (hps : 0 < ps.size)
    (t : Trie α) (ht : Trie.valid t) : valid (.path v ps hps t)
  | node (v : Option α)
    (cs : ByteArray)
    (ts : Array (Trie α))
    (hsize : cs.size = ts.size)
    (hdistinct : cs.toList.Nodup)
    (hts : ∀ t, t ∈ ts → Trie.valid t) : Trie.valid (Trie.node v cs ts)

theorem valid_mkPath {α} (v : Option α) (ps : ByteArray) (t : Trie α) (ht : Trie.valid t) :
    Trie.valid (Trie.mkPath v ps t) := by
  unfold Trie.mkPath
  split
  · exact Trie.valid.path _ _ _ _ ht
  · exact ht

theorem valid_loop_insertEmpty {α} (i : Nat) (k : String) (f : Option α → α) :
    Trie.valid (Trie.upsert.insertEmpty k f i) := by
  unfold Trie.upsert.insertEmpty
  apply valid_mkPath
  apply Trie.valid.leaf

theorem valid_loop_upsert {α} (t : Trie α) (i : Nat) (k : String) (f : Option α → α) (h : Trie.valid t):
    Trie.valid (Trie.upsert.loop k f i t) := by
  cases h with
  | leaf v =>
    simp only [Trie.upsert.loop]; simp_utf8
    split
    case inr hi => apply Trie.valid.leaf
    case inl hi => apply valid_mkPath; apply Trie.valid.leaf
  | path v ps hps t ht =>
    simp only [Trie.upsert.loop]; simp_utf8
    split
    case inr hi => apply Trie.valid.path; assumption
    case inl hi =>
      split
      case inl hp =>
        apply valid_mkPath
        apply valid_loop_upsert -- induction happens here
        apply valid_mkPath
        exact ht
      case inr hp =>
        apply Trie.valid.node
        · simp [ByteArray.size]
        · have heq0 : Trie.commonPrefix k ps i = 0 := by omega
          have := Trie.commonPrefix_differs_head k ps i heq0 hi hps
          simpa [List.Nodup]
        · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
          constructor
          case left =>
            apply valid_loop_insertEmpty
          case right =>
            simp only [List.not_mem_nil, false_implies, forall_const, and_true]
            apply valid_mkPath
            exact ht
  | node v cs ts hsize hdisitnct hts =>
    simp only [Trie.upsert.loop]; simp_utf8
    split
    case inr hi => apply Trie.valid.node <;> assumption
    case inl hi =>
      rw [ByteArray.findIdx_list]
      split
      case h_1 _ hfindnone =>
        apply Trie.valid.node
        · simpa
        · simp only [ByteArray.toList_push, List.nodup_snoc, hdisitnct, and_true]
          simp only [List.mem_iff_get?, not_exists]
          intro j hj
          have := List.findIdx?_of_eq_none hfindnone j
          rw [hj] at this
          simp at this
          done
        · simp only [← Array.mem_data, Array.push_data, List.mem_append, List.mem_singleton]
          simp only [Array.mem_data]
          intro t ht
          cases ht with
          | inl ht => exact hts t ht
          | inr ht => cases ht; apply valid_loop_insertEmpty
      case h_2 _ idx _hfindsome =>
        apply Trie.valid.node
        · simpa
        · assumption
        · simp only [← Array.mem_data, List.mem_iff_get?, forall_exists_index]
          simp only [← Array.get?_eq_data_get?]
          simp only [Array.get?_modify]
          intro t' j
          split
          case inl hj =>
            cases hj
            simp only [Option.map_eq_some', forall_exists_index, and_imp]
            intro t'' ht'' ht''
            cases ht''
            apply valid_loop_upsert -- induction happens here
            apply hts
            simp only [← Array.mem_data, List.mem_iff_get?]
            simp only [← Array.get?_eq_data_get?]
            exact ⟨_, ht''⟩
          case inr hj =>
            intro ht''
            apply hts
            simp only [← Array.mem_data, List.mem_iff_get?]
            simp only [← Array.get?_eq_data_get?]
            exact ⟨_, ht''⟩
            done
termination_by _ => k.toUTF8.size - i
decreasing_by
  simp_wf
  omega

theorem valid_upsert {α} (t : Trie α) (k : String) (f : Option α → α) (h : Trie.valid t):
  Trie.valid (t.upsert k f) := valid_loop_upsert _ _ _ _ h


theorem find?_loop_mkPath {α} (t : Trie α) (k : String) (v : Option α) (ps : ByteArray) (i : Nat)
  (hi : i < k.toUTF8.size) :
    Trie.find?.loop k i (Trie.mkPath v ps t) =
      if Trie.hasPrefix k ps i then
        Trie.find?.loop k (i + ps.size) t
      else
        none := by
  unfold Trie.mkPath
  split
  next => simp [Trie.find?.loop, hi]
  next =>
    have : ps = .empty := sorry
    subst ps
    simp

theorem find_upsert_loop {α} (t : Trie α) (k₁ k₂ : String) (f : Option α → α) (h : Trie.valid t)
  (i : Nat) (hprefix : k₁.toUTF8.extract 0 i = k₂.toUTF8.extract 0 i) :
  Trie.find?.loop k₂ i (Trie.upsert.loop k₁ f i t) =
    let v := Trie.find?.loop k₂ i t; (if k₂ = k₁ then some (f v) else v) := by
  cases h with
  | leaf v =>
    -- This kills the let; known issue
    simp only [Trie.upsert.loop, Trie.find?.loop]; simp_utf8
    split
    case inr hi₁ =>
      simp only [Trie.upsert.loop, Trie.find?.loop]; simp_utf8
      split
      case inl hi₂ =>
        have : ¬ k₂= k₁ := by intro h; cases h; contradiction
        simp only [this, ite_false]
      case inr hi₂ =>
        have : k₁ = k₂ := by
          apply String.toUTF8_inj
          sorry
        simp only [this, ite_true]
    case inl hi₁ =>
      if hi₂ : i < ByteArray.size (String.toUTF8 k₂)
      then
        simp only [hi₂, ite_true]
        simp only [find?_loop_mkPath, hi₂]; simp_utf8
        split
        case inl hprefix =>
          simp only [Trie.find?.loop]; simp_utf8
          split
          case inl hi₃ =>
            suffices k₂ ≠ k₁ by simp [this]
            intro hk; cases hk
            simp at hi₃
            omega
          case inr hi₃ =>
            suffices k₂ = k₁ by simp [this]
            have hsize : ByteArray.size (String.toUTF8 k₂) ≤
                ByteArray.size (String.toUTF8 k₁) := by simp at hi₃; omega
            clear hi₃
            sorry
        case inr hprefix =>
          sorry
      else
        sorry


theorem find_upsert {α} (t : Trie α) (k₁ k₂ : String) (f : Option α → α) (h : Trie.valid t) :
    (t.upsert k₁ f).find? k₂ = (if k₂ = k₁ then some (f (t.find? k₂)) else t.find? k₂) := by
  sorry
