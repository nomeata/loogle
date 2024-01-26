/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura, Joachim Breitner

A string trie data structure, used for tokenizing the Lean language.

Adapted from Lean.Data.Trie to use path compression.

-/
import Lean.Data.Format
import Std.Tactic.Omega

namespace Loogle


/-- A Trie is a key-value store where the keys are of type `String`,
and the internal structure is a tree that branches on the bytes of the string.  -/
inductive Trie (α : Type) where
  | leaf : Option α → Trie α
  | path : Option α → ByteArray → Trie α → Trie α
  | node : Option α → ByteArray → Array (Trie α) → Trie α

namespace Trie
variable {α : Type}

/-- The empty `Trie` -/
def empty : Trie α := leaf none

instance : EmptyCollection (Trie α) :=
  ⟨empty⟩

instance : Inhabited (Trie α) where
  default := empty

def commonPrefix (s₁ : String) (s₂ : ByteArray)  (offset1 : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h : offset1 + i < s₁.utf8ByteSize then
      if h' : i < s₂.size then
        if s₁.getUtf8Byte (offset1 + i) h == s₂.get ⟨i, h'⟩ then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
  loop 0
termination_by loop => s₂.size - i

def hasPrefix (s₁ : String) (s₂ : ByteArray) (offset1 : Nat) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h' : i < s₂.size then
      if h : offset1 + i < s₁.utf8ByteSize then
        if s₁.getUtf8Byte (offset1 + i) h == s₂.get ⟨i, h'⟩ then
          loop (i + 1)
        else
          false
      else
        false
    else
      true
  loop 0
termination_by loop => s₂.size - i

/-- Insert or update the value at a the given key `s`.  -/
def upsert (t : Trie α) (s : String) (f : Option α → α) : Trie α :=
  let rec insertEmpty (i : Nat) : Trie α :=
    if i < s.utf8ByteSize then
      path none (s.toUTF8.extract i s.utf8ByteSize) (leaf (f .none))
    else
      leaf (f .none)
  let rec loop
    | i, leaf v =>
      if i < s.utf8ByteSize then
        path v (s.toUTF8.extract i s.utf8ByteSize) (leaf (f .none))
      else
        leaf (f v)
    | i, path v ps t' =>
      if h : i < s.utf8ByteSize then
        let j := commonPrefix s ps i
        if hj : 0 < j then
          -- split common prefix, continue
          let ps1 := ps.extract 0 j
          path v ps1 <| loop (i + j) <|
            if j < ps.size then
              let ps2 := ps.extract j ps.size
              path none ps2 t'
            else
              t'
        else
          -- no common prefix, split off first character
          let c := s.getUtf8Byte i h
          let c' := ps.get! 0
          let ps' := ps.extract 1 ps.size
          let t := insertEmpty (i + 1)
          node v (.mk #[c, c']) #[t, path none ps' t']
      else
        path (f v) ps t'
    | i, node v cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            node v (cs.push c) (ts.push t)
          | some idx =>
            node v cs (ts.modify idx (loop (i + 1)))
      else
        node (f v) cs ts
  loop 0 t
termination_by loop i _ => s.utf8ByteSize - i
decreasing_by simp_wf; omega

/-- Inserts a value at a the given key `s`, overriding an existing value if present. -/
def insert (t : Trie α) (s : String) (val : α) : Trie α :=
  upsert t s (fun _ => val)

/-- Looks up a value at the given key `s`.  -/
def find? (t : Trie α) (s : String) : Option α :=
  let rec loop
    | i, leaf val =>
      if i < s.utf8ByteSize then
        none
      else
        val
    | i, path val ps t' =>
      if i < s.utf8ByteSize then
        if 0 < ps.size then
          if hasPrefix s ps i then
            loop (i + ps.size) t'
          else
            none
        else none -- should be dead code
      else
        val
    | i, node val cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
        | none   => none
        | some idx => loop (i + 1) (ts.get! idx)
      else
        val
  loop 0 t
termination_by loop i _ => s.utf8ByteSize - i
decreasing_by simp_wf; omega

/-- Returns an `Array` of all values in the trie, in no particular order. -/
def values (t : Trie α) : Array α := go t |>.run #[] |>.2
  where
    go : Trie α → StateM (Array α) Unit
      | leaf a? => do
        if let some a := a? then
          modify (·.push a)
      | path a? _ t' => do
        if let some a := a? then
          modify (·.push a)
        go t'
      | node a? _ ts => do
        if let some a := a? then
          modify (·.push a)
        ts.attach.forM fun ⟨t',_⟩ => go t'

/-- Returns all values whose key have the given string `pre` as a prefix, in no particular order. -/
def findPrefix (t : Trie α) (pre : String) : Array α := go t 0
  where
    go (t : Trie α) (i : Nat) : Array α :=
      if h : i < pre.utf8ByteSize then
        let c := pre.getUtf8Byte i h
        match t with
        | leaf _val => .empty
        | path _val ps t' =>
          if 0 < ps.size then
            if hasPrefix pre ps i
            then go t' (i + ps.size)
            else .empty
          else
            .empty -- should be an invariant
        | node _val cs ts =>
          match cs.findIdx? (· == c) with
          | none   => .empty
          | some idx =>
            if let some ⟨t',_⟩ := ts.attach.get? idx then
            go t' (i + 1)
            else .empty -- should be unreachable
      else
        t.values


open Lean in
private partial def toStringAux {α : Type} : Trie α → List Format
  | leaf _ => []
  | path _ ps t =>
    [ format (repr ps.data), Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t ]
  | node _ cs ts =>
    List.join $ List.zipWith (fun c t =>
      [ format (repr c), (Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t) ]
    ) cs.toList ts.toList

open Lean in
instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩

end Trie


end Loogle
