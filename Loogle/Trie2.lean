/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura, Joachim Breitner

Trie for tokenizing the Lean language
-/
import Lean.Data.Format

set_option autoImplicit false

inductive ByteTrie (α : Type) where
  | Node : Option α → ByteArray -> Array (ByteTrie α) → ByteTrie α

namespace ByteTrie
variable {α : Type}

def empty : ByteTrie α :=
  ⟨none, .empty, .empty⟩

instance : EmptyCollection (ByteTrie α) :=
  ⟨empty⟩

instance : Inhabited (ByteTrie α) where
  default := empty

partial def upsert (t : ByteTrie α) (s : ByteArray) (f : Option α → α) : ByteTrie α :=
  let rec insertEmpty (i : Nat) : ByteTrie α :=
    match i == ByteArray.size s  with
    | true => ByteTrie.Node (f .none) .empty .empty
    | false =>
      let c := s.get! i
      let t := insertEmpty (i + 1)
      ByteTrie.Node none (ByteArray.empty.push c) #[t]
  let rec loop
    | i, ByteTrie.Node v cs ts =>
      match i == ByteArray.size s  with
      | true  => ByteTrie.Node (f v) cs ts
      | false =>
        let c := s.get! i
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            ByteTrie.Node v (cs.push c) (ts.push t)
          | some idx =>
            ByteTrie.Node v cs (ts.modify idx (loop (i + 1)))
  loop 0 t

partial def insert (t : ByteTrie α) (s : ByteArray) (val : α) : ByteTrie α :=
  upsert t s (fun _ => val)

partial def find? (t : ByteTrie α) (s : ByteArray) : Option α :=
  let rec loop
    | i, ByteTrie.Node val cs ts =>
      match i == ByteArray.size s  with
      | true  => val
      | false =>
        let c := s.get! i
        match cs.findIdx? (· == c) with
        | none   => none
        | some idx => loop (i + 1) (ts.get! idx)
  loop 0 t

/-- Return values that match the given `prefix` -/
partial def findPrefix (t : ByteTrie α) (pre : ByteArray) : Array α :=
  go t 0 |>.run #[] |>.2
where
  go (t : ByteTrie α) (i : Nat) : StateM (Array α) Unit :=
    if i == ByteArray.size pre then
      collect t
    else
      let c := pre.get! i
      let ⟨_, cs, ts⟩ := t
      match cs.findIdx? (· == c) with
      | none   => pure ()
      | some idx => go (ts.get! idx) (i + 1)

  collect (t : ByteTrie α) : StateM (Array α) Unit := do
    let ⟨a?, _cs, ts⟩ := t
    if let some a := a? then
      modify (·.push a)
    ts.forM fun t' => collect t'

/-

private def updtAcc (v : Option α) (i : String.Pos) (acc : String.Pos × Option α) : String.Pos × Option α :=
  match v, acc with
  | some v, (_, _) => (i, some v)  -- we pattern match on `acc` to enable memory reuse
  | none,   acc    => acc

partial def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : String.Pos × Option α :=
  let rec loop
    | Trie.Node v m, i, acc =>
      match s.atEnd i with
      | true  => updtAcc v i acc
      | false =>
        let acc := updtAcc v i acc
        let c   := s.get i
        let i   := s.next i
        match RBNode.find compare m c with
        | some t => loop t i acc
        | none   => acc
  loop t i (i, none)

private partial def toStringAux {α : Type} : Trie α → List Format
  | Trie.Node _ map => map.fold (fun Fs c t =>
   format (repr c) :: (Format.group $ Format.nest 2 $ flip Format.joinSep Format.line $ toStringAux t) :: Fs) []

instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩
end Trie

end Parser
end Lean
-/

end ByteTrie


def Trie := ByteTrie
abbrev Trie.empty := @ByteTrie.empty
abbrev Trie.insert {α : Type} (t : Trie α) (s : String) (val : α) : Trie α :=
  ByteTrie.insert t s.toUTF8 val
abbrev Trie.findPrefix {α : Type} (t : Trie α) (pre : String) : Array α :=
  ByteTrie.findPrefix t pre.toUTF8
abbrev Trie.find?  {α : Type} (t : Trie α) (s : String) : Option α :=
  ByteTrie.find? t s.toUTF8
def Trie.upsert {α : Type} (t : Trie α) (s : String) (f : Option α → α) : Trie α  :=
  ByteTrie.upsert t s.toUTF8 f