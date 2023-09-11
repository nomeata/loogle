/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura, Joachim Breitner

A string trie data strucuture, used for tokenizing the Lean language
-/
import Lean.Data.Format

import Loogle.StringByte

set_option autoImplicit false

inductive Trie (α : Type) where
  | Leaf : Option α → Trie α
  | Node1 : Option α → UInt8 → Trie α → Trie α
  | Node : Option α → ByteArray -> Array (Trie α) → Trie α

namespace Trie
variable {α : Type}

def empty : Trie α := Leaf none

instance : EmptyCollection (Trie α) :=
  ⟨empty⟩

instance : Inhabited (Trie α) where
  default := empty

partial def upsert (t : Trie α) (s : String) (f : Option α → α) : Trie α :=
  let rec insertEmpty (i : Nat) : Trie α :=
    match i == s.utf8ByteSize  with
    | true => Trie.Node (f .none) .empty .empty
    | false =>
      let c := s.getUtf8Byte i
      let t := insertEmpty (i + 1)
      Trie.Node1 none c t
  let rec loop
    | i, Leaf v =>
      match i == s.utf8ByteSize  with
      | true  => Trie.Leaf (f v)
      | false =>
          let c := s.getUtf8Byte i
          let t := insertEmpty (i + 1)
          Trie.Node1 v c t
    | i, Node1 v c' t' =>
      match i == s.utf8ByteSize  with
      | true  => Trie.Node1 (f v) c' t'
      | false =>
        let c := s.getUtf8Byte i
        if c == c'
        then Trie.Node1 v c' (loop (i + 1) t')
        else 
          let t := insertEmpty (i + 1)
          Trie.Node v (.mk #[c, c']) #[t, t']
    | i, Trie.Node v cs ts =>
      match i == s.utf8ByteSize  with
      | true  => Trie.Node (f v) cs ts
      | false =>
        let c := s.getUtf8Byte i
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            Trie.Node v (cs.push c) (ts.push t)
          | some idx =>
            Trie.Node v cs (ts.modify idx (loop (i + 1)))
  loop 0 t

partial def insert (t : Trie α) (s : String) (val : α) : Trie α :=
  upsert t s (fun _ => val)

partial def find? (t : Trie α) (s : String) : Option α :=
  let rec loop
    | i, Trie.Leaf val =>
      match i == s.utf8ByteSize  with
      | true  => val
      | false => none
    | i, Trie.Node1 val c' t' =>
      match i == s.utf8ByteSize  with
      | true  => val
      | false =>
        let c := s.getUtf8Byte i
        if c == c'
        then loop (i + 1) t'
        else none
    | i, Trie.Node val cs ts =>
      match i == s.utf8ByteSize  with
      | true  => val
      | false =>
        let c := s.getUtf8Byte i
        match cs.findIdx? (· == c) with
        | none   => none
        | some idx => loop (i + 1) (ts.get! idx)
  loop 0 t

/-- Return values that match the given `prefix` -/
partial def findPrefix (t : Trie α) (pre : String) : Array α :=
  go t 0 |>.run #[] |>.2
where
  go (t : Trie α) (i : Nat) : StateM (Array α) Unit :=
    if i == pre.utf8ByteSize then
      collect t
    else
      let c := pre.getUtf8Byte i
      match t with
      | Leaf _val =>
        pure ()
      | Node1 _val c' t' =>
        if c == c'
        then go t' (i + 1)
        else pure ()
      | Node _val cs ts =>
        match cs.findIdx? (· == c) with
        | none   => pure ()
        | some idx => go (ts.get! idx) (i + 1)

  collect (t : Trie α) : StateM (Array α) Unit := do
    match t with
    | Leaf a? =>
      if let some a := a? then
        modify (·.push a)
    | Node1 a? _ t' =>
      if let some a := a? then
        modify (·.push a)
      collect t'
    | Node a? _ ts =>
      if let some a := a? then
        modify (·.push a)
      ts.forM fun t' => collect t'

private def updtAcc (v : Option α) (i : Nat) (acc : String.Pos × Option α) : String.Pos × Option α :=
  match v, acc with
  | some v, (_, _) => (.mk i, some v)
       -- we pattern match on `acc` to enable memory reuse
       -- by constuction, only valid string positions have entries in the trie
  | none,   acc    => acc

partial def matchPrefix (s : String) (t : Trie α) (i : String.Pos) : String.Pos × Option α :=
  let rec loop
    | Trie.Leaf v, i, acc =>
      updtAcc v i acc
    | Trie.Node1 v c' t', i, acc =>
      match i == s.utf8ByteSize with
      | true  => updtAcc v i acc
      | false =>
        let acc := updtAcc v i acc
        let c   := s.getUtf8Byte i
        if c == c'
        then loop t' (i + 1) acc
        else acc
    | Trie.Node v cs ts, i, acc =>
      match i == s.utf8ByteSize with
      | true  => updtAcc v i acc
      | false =>
        let acc := updtAcc v i acc
        let c   := s.getUtf8Byte i
        match cs.findIdx? (· == c) with
        | none   => acc
        | some idx => loop (ts.get! idx) (i + 1) acc
  loop t i.byteIdx (i, none)

open Lean

private partial def toStringAux {α : Type} : Trie α → List Format
  | Trie.Leaf _ => []
  | Trie.Node1 _ c t =>
    [ format (repr c), Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t ]
  | Trie.Node _ cs ts =>
    List.join $ List.zipWith (fun c t =>
      [ format (repr c), (Format.group $ Format.nest 4 $ flip Format.joinSep Format.line $ toStringAux t) ]
    ) cs.toList ts.toList

instance {α : Type} : ToString (Trie α) :=
  ⟨fun t => (flip Format.joinSep Format.line $ toStringAux t).pretty⟩

#eval Trie.empty
  |>.insert "hello" ()
  |>.insert "heho" ()
  |>.insert "hella" ()
  |>.insert "helli" ()
  |>.insert "xeno" ()

end Trie