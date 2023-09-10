import Lean.Data.Trie

abbrev Trie := Lean.Parser.Trie
abbrev Trie.empty := @Lean.Parser.Trie.empty
abbrev Trie.insert {α : Type} (t : Trie α) (s : String) (val : α) : Trie α :=
  Lean.Parser.Trie.insert t s val
abbrev Trie.findPrefix {α : Type} (t : Trie α) (pre : String) : Array α :=
  Lean.Parser.Trie.findPrefix t pre
abbrev Trie.find?  {α : Type} (t : Trie α) (s : String) : Option α :=
  Lean.Parser.Trie.find? t s

def Trie.upsert {α : Type} (t : Trie α) (s : String) (f : Option α → α) : Trie α  :=
  t.insert s (f (t.find? s))
