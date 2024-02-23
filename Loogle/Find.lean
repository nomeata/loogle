/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Lean
import Std.Data.String.Basic
import Std.Util.Pickle
import Std.Lean.Delaborator

import Loogle.Cache
import Loogle.NameRel
import Loogle.RBTree
import Loogle.BlackListed
import Loogle.Trie

/-!
# The `#find` command and tactic.
-/

open Lean Meta Elab

/-!
## Formatting utilities
-/

/-- Puts `MessageData` into a bulleted list -/
def MessageData.bulletList (xs : Array MessageData) : MessageData :=
  MessageData.joinSep (xs.toList.map (m!"• " ++ ·)) Format.line

/-- Puts `MessageData` into a comma-separated list with `"and"` at the back (no Oxford comma).
Best used on non-empty arrays; returns `"– none –"` for an empty array.  -/
def MessageData.andList (xs : Array MessageData) : MessageData :=
  match xs with
  | #[] => m!"– none –"
  | #[x] => x
  | _ => MessageData.joinSep xs.pop.toList m!", " ++ m!" and " ++ xs.back

/-- Formats a list of names and types, as you would expect from a lemma-searching command.  -/
def MessageData.bulletListOfConstsAndTypes {m} [Monad m] [MonadEnv m] [MonadError m]
    (names : Array (Name × Expr)) (showTypes : Bool := false) : m MessageData := do
    let ms ← names.mapM fun (n,t) => do
      let n := ppConst (← mkConstWithLevelParams n)
      if showTypes then
        return m!"{n} : {t}"
      else
        return n
    pure (MessageData.bulletList ms)
/-!
## Name sorting
-/

namespace Loogle.Find

/-- Sorts a thing with a name so that names defied in modules that come earlier (as per `ModuleIdx`)
come earlier. Within one module, sort according to given function, and finally by Name.
-/
def sortByModule' {m} [Monad m] [MonadEnv m] {α} (name : α → Name) (f : α → Nat)
    (ns : Array α) : m (Array (α × Option ModuleIdx)) := do
  let env ← getEnv
  return ns
    |>.map (fun x => (env.getModuleIdxFor? (name x), f x, x))
    -- Sort by modindex and then by the given predicate
    -- A ModIdx of none means locally defined, we put them first.
    -- The modindex corresponds to a topological sort of the modules, so basic lemmas come earlier.
    |>.qsort (fun (mi₁, k₁, x₁) (mi₂, k₂, x₂) =>
      match mi₁, mi₂ with
      | none, none => Nat.blt k₁ k₂ || Nat.beq k₁ k₂ && Name.lt (name x₁) (name x₂)
      | none, some _ => true
      | some _, none => false
      | some mi₁, some mi₂ =>
        Nat.blt mi₁ mi₂ ||
        Nat.beq mi₁ mi₂ && (Nat.blt k₁ k₂ || Nat.beq k₁ k₂ && Name.lt (name x₁) (name x₂)))
    |>.map fun (mi, _k, x) => (x, mi)

/-- See `sortByModule'` --/
def sortByModule {m} [Monad m] [MonadEnv m] {α} (name : α → Name) (f : α → Nat)
    (ns : Array α) : m (Array α) := do
  return (← sortByModule' name f ns).map (·.1)

/-- In lieu of an real `Lean.Expr.size` function, explicitly fold for now -/
def exprSize (e : Expr ) : Nat := go e 0
  where @[nolint docBlame] go : Expr → Nat → Nat
    | Expr.forallE _ d b _, c  => go b (go d (c + 1))
    | Expr.lam _ d b _, c      => go b (go d (c + 1))
    | Expr.letE _ t v b _, c   => go b (go v (go t (c + 1)))
    | Expr.app f a, c          => go a (go f (c + 1))
    | Expr.mdata _ b, c        => go b (c + 1)
    | Expr.proj _ _ b, c       => go b (c + 1)
    | _, c                     => c + 1

/-!
## Matching term patterns against conclusions or any subexpression
-/

/-- Comparing `HeadIndex` for whether the terms could be equal; for `HeadIndex.mvar` we have no
information. -/
def canMatch : HeadIndex → HeadIndex → Bool
  | .mvar _, _ => true
  | _, .mvar _ => true
  | hi₁, hi₂ => hi₁ == hi₂

/-- A predicate on `ConstantInfo` -/
def ConstMatcher := ConstantInfo → MetaM Bool

private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false

/-- Like defEq, but the pattern is a function type, matches parameters up to reordering -/
def matchUpToHyps (pat: AbstractMVarsResult) (head : HeadIndex) (e : Expr) : MetaM Bool := do
  forallTelescope e fun e_params e_concl ↦ do
    if canMatch head e_concl.toHeadIndex then
      let (_, _, pat_e) ← openAbstractMVarsResult pat
      let (pat_params, _, pat_concl) ← forallMetaTelescope pat_e
      isDefEq e_concl pat_concl <&&> matchHyps pat_params.toList [] e_params.toList
    else
      pure false

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if the conclusion of the
lemma matches the pattern.  If the pattern is a function type, it matches up to parameter
reordering. -/
def matchConclusion (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := (← forallMetaTelescope t).2.2.toHeadIndex
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    matchUpToHyps pat head cTy

/-- A wrapper around `Lean.Meta.forEachExpr'` that checks if any subexpression matches the
predicate.  -/
def Lean.Meta.anyExpr (input : Expr) (pred : Expr → MetaM Bool) : MetaM Bool := do
  let found  ← IO.mkRef false
  Lean.Meta.forEachExpr' input fun sub_e => do
    if ← pred sub_e then found.set true
    -- keep searching if we haven't found it yet
    not <$> found.get
  found.get

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if _any_ subexpression
matches that patttern. If the pattern is a function type, it matches up to parameter reordering. -/
def matchAnywhere (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := (← forallMetaTelescope t).2.2.toHeadIndex
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    -- NB: Lean.Meta.forEachExpr`' handles nested foralls in one go, so
    -- in `(a → b → c)`, it will never vist `b → c`.
    -- But since we use `matchUpToHyps` instead of `isDefEq` directly, this is ok.
    Lean.Meta.anyExpr cTy $ matchUpToHyps pat head

/-!
## The two indexes used

`#find` uses two indexes: One mapping names to names of constants that mention
that name anywhere, which is the primary index that we use.

Additionaly, for queries that involve _only_ lemma name fragments, we maintain a suffix trie
of lemma names.
-/

/-- For all names `n` mentioned in the type of the constant `c`, add a mapping from
`n` to `c.name` to the relation. -/
private def addDecl (name : Lean.Name) (c : ConstantInfo) (m : NameRel) : MetaM NameRel := do
  if ← Loogle.isBlackListed name then
    return m
  let consts := c.type.foldConsts {} (flip NameSet.insert)
  return consts.fold (init := m) fun m n => m.insert n name


/-- A suffix trie for `Name`s -/
def SuffixTrie := Loogle.Trie (Array Name)
deriving Nonempty

/-- Insert a `Name` into a `SuffixTrie` -/
def SuffixTrie.insert (t : SuffixTrie) (n : Lean.Name) : SuffixTrie := Id.run $ do
  let mut t := t
  let s := n.toString.toLower
  for i in List.range (s.length - 1) do -- -1 to not consider the empty suffix
    let suf := s.drop i
    t := t.upsert suf fun ns? => ns? |>.getD #[] |>.push n
  pure t

/-- Insert a declaration into a `SuffixTrie`, if the name isn't blacklisted. -/
@[nolint unusedArguments]
def SuffixTrie.addDecl (name : Lean.Name) (_ : ConstantInfo) (t : SuffixTrie) :
    MetaM SuffixTrie := do
  if ← Loogle.isBlackListed name then
    return t
  return t.insert name

-- /-- Search the suffix trie, returning an empty array if nothing matches -/
def SuffixTrie.find (t : SuffixTrie) (s : String) : NameSet :=
  t.findPrefix s.toLower |>.map (RBTree.fromArray (cmp := _)) |>.foldl (init := {}) NameSet.append

/-- Search the suffix trie, returning an empty array if nothing matches -/
def SuffixTrie.findSuffix (t : SuffixTrie) (s : String) : Array Name :=
  (Loogle.Trie.find? t s.toLower).getD #[]

open Std.Tactic

/-- The index used by `#find`: A declaration cache with a `NameRel` mapping names to the name
of constants they are mentinend in, and a declaration cache storing a suffix trie. -/
structure Index where mk'' ::
  /-- Maps names to the names of constants they are mentioned in. -/
  nameRelCache : DeclCache2 NameRel
  /-- Suffix trie of lemma names -/
  trieCache: DeclCache2 SuffixTrie
deriving Nonempty

-- NB: In large files it may be slightly wasteful to calculate a full NameSet for the local
-- definition upon every invocation of `#find`, and a linear scan might work better. For now,
-- this keeps the code below more uniform.

/-- Create a fresh index.  -/
def Index.mk : IO Index := do
  let c1 ← DeclCache2.mk "#find: init cache" .empty addDecl
  let c2 ← DeclCache2.mk "#find: init trie" .empty SuffixTrie.addDecl
  pure ⟨c1, c2⟩

/-- The part of the index that includes the imported definitions, for example to be persisted and
distributed by `MathlibExtras.Find`.  -/
def Index.getCache (i : Index) : CoreM (NameRel × SuffixTrie) := do
  let r ← i.nameRelCache.getImported
  let t ← i.trieCache.getImported
  pure (r, t)

/-- Create an index from a cached value -/
def Index.mkFromCache (init : NameRel × SuffixTrie) : IO Index := do
  let c1 ← DeclCache2.mkFromCache .empty addDecl init.1
  let c2 ← DeclCache2.mkFromCache .empty SuffixTrie.addDecl init.2
  pure ⟨c1, c2⟩

/-!
## The #find syntax and elaboration helpers
-/

open Parser

/-- The turnstyle uesd bin `#find`, unicode or ascii allowed -/
syntax turnstyle := patternIgnore("⊢ " <|> "|- ")
/-- a single `#find` filter. The `term` can also be an ident or a strlit,
these are distinguished in `parseFindFilters` -/
syntax find_filter := (turnstyle term) <|> term

/-- The argument to `#find`, a list of filters -/
syntax find_filters := find_filter,*

/-- A variant of `Lean.Elab.Term.elabTerm` that does not complain for example
when a type class constraint has no instances.  -/
def elabTerm' (t : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ ·  with ignoreTCFailures := true, errToSorry := false }) do
    let t ← Term.elabTerm t expectedType?
    -- So far all tests work without the following line. Lets expand the test
    -- suite once someone complains
    -- Term.synthesizeSyntheticMVars (mayPostpone := true) (ignoreStuckTC := true)
    instantiateMVars t

/-!
## Generating suggestions for unresolvable names

For `#find` it is really helpful if, when the user entered a term with a name that cannot
be resolved, we use the name trie to see if it exists maybe in some qualified form. For
simple `ident` patterns, this is straight forward, but for expressions it is harder: The term
elaborator simply throws an unstructured expression.

So we’ll use the source reference from that exception, check if there is an `.ident` at tht position
in the source, check if the name there does not resolve in the environments, generate
possible suggestions, and re-assemble the syntax.

The following functions are rather hackish, maybe there can be a more principled approach.
-/

/-- Equality on `SourceInfo` -/
private def SourceInfo.beq  : SourceInfo → SourceInfo → Bool
  | .original _ p1 _ p2, .original _ p3 _ p4
  | .original _ p1 _ p2, .synthetic p3 p4 _
  | .synthetic p1 p2 _, .synthetic p3 p4 _
  | .synthetic p1 p2 _, .original _ p3 _ p4
  => p1 == p3 && p2 == p4
  | _, _ => false


/-- Within the given `Syntax`, see if the `SourceInfo` points to an `.ident` -/
partial def findNameAt (needle : SourceInfo) : Syntax → Option Name
  | .node _ _ cs => cs.findSome? (findNameAt needle)
  | .ident si _ n _ =>
    if SourceInfo.beq needle si then
      .some n
    else
      .none
  | _ => .none

/-- Within the given `Syntax`, if the `SourceInfo` points to an `.ident`, replace the `Name` -/
partial def replaceIdentAt' (needle : SourceInfo) (new_name : Name) : Syntax → Syntax
  | .node si kind cs => .node si kind (cs.map (replaceIdentAt' needle new_name))
  | .ident si str n prs =>
    if SourceInfo.beq needle si then
      .ident si (new_name.toString) new_name []
    else
      .ident si str n prs
  | s => s

/-- Within the given `TSyntax`, if the `SourceInfo` points to an `.ident`, replace the `Name` -/
def replaceIdentAt {kind} (si : SourceInfo) (n : Name) : TSyntax kind → TSyntax kind
  | .mk s => .mk (replaceIdentAt' si n s)

/-- When a name cannot be resolved, see if we can find it in the trie under some namepace. -/
def resolveUnqualifiedName (index : Index) (n : Name) : MetaM (Array Name) := do
  let s := "." ++ n.toString
  let (t₁, t₂) ← index.trieCache.get
  let names := t₁.findSuffix s ++ t₂.findSuffix s
  let names := names.filter ((← getEnv).contains ·)
  sortByModule id (fun _ => 0) names

/-- If the `s` at `si` is an identifier not found in he environment, produce a list
of possible suggestions in place of `s`. -/
def suggestQualifiedNames {kind} (index : Index) (s : TSyntax kind) (si : SourceInfo) :
    MetaM (Array (TSyntax kind)) := do
  let .some n := findNameAt si s | pure #[]
  let .none := (← getEnv).find? n | pure #[]
  let suggestedNames ← resolveUnqualifiedName index n
  return suggestedNames.map fun sugg => replaceIdentAt si sugg s

/-- If the `s` at the subexpression `needle` is an identifier `find_filter`, suggest replacing it
with a name string filter. -/
partial def suggestQuoted' (needle : SourceInfo) (s : Syntax) : Syntax :=
  match s with
  | .node si₁ ``find_filter #[.ident si₂ str _n _prs]  =>
    if SourceInfo.beq needle si₂ then
      .node si₁ ``find_filter #[Syntax.mkStrLit str.toString]
    else
      s
  | .node si kind cs =>
    .node si kind <| cs.map (suggestQuoted' needle)
  | _ => s

/-- If the `s` at the subexpression `needle` is an identifier `find_filter`, suggest replacing it
with a name string filter. -/
partial def suggestQuoted {kind} (needle : SourceInfo) : TSyntax kind → Array (TSyntax kind)
  | .mk s =>
    let s' := suggestQuoted' needle s
    if s == s' then  #[] else #[.mk s']


/-!
## The core find tactic engine
-/

/-- The parsed and elaborated arguments to `#find`  -/
structure Arguments where
  /-- Identifiers to search for -/
  idents : Array Name
  /-- Lemma name substrings to search for -/
  namePats : Array String
  /-- Term patterns to search for. The boolean indicates conclusion patterns. -/
  terms : Array (Bool × Expr)
  /-- Extra messages arising from parsing -/
  parserMessage : MessageData

/-- Result of `find` -/
structure Result where
  /-- Statistical summary -/
  header : MessageData
  /-- Total number of matches -/
  count : Nat
  /-- Matching definition (with defining module, if imported)  -/
  hits : Array (ConstantInfo × Option Name)
  /-- Alternative suggestions  -/
  suggestions : Array (TSyntax ``find_filters)

/-- Negative result  of `find` -/
structure Failure where
  /-- Position of error message -/
  ref : Syntax
  /-- Error message -/
  message : MessageData
  /-- Alternative suggestions  -/
  suggestions : Array (TSyntax ``find_filters)

/-- The core of the `#find` tactic with all parsing/printing factored out, for
programmatic use (e.g. the loogle CLI).
It also does not use the implicit global Index, but rather expects one as an argument. -/
def find (index : Index) (args : TSyntax ``find_filters) (maxShown := 200) :
    TermElabM (Except Failure Result) := do
  profileitM Exception "#find" (← getOptions) do
    let mut message := MessageData.nil
    let mut idents := #[]
    let mut namePats := #[]
    let mut terms := #[]
    try
      match args with
      | `(find_filters| $args':find_filter,*) =>
        for argi in List.range args'.getElems.size do
        let arg := args'.getElems[argi]!
          match arg with
          | `(find_filter| $_:turnstyle $s:term) => do
            let e ← elabTerm' s (some (mkSort (← mkFreshLevelMVar)))
            let t := ← inferType e
            unless t.isSort do
              throwErrorAt s m!"Conclusion pattern is of type {t}, should be of type `Sort`"
            terms := terms.push (true, e)
          | `(find_filter| $ss:str) => do
            let str := Lean.TSyntax.getString ss
            if str = "" || str = "." then
              throwErrorAt ss "Name pattern is too general"
            namePats := namePats.push str
          | `(find_filter| $i:ident) => do
            let n := Lean.TSyntax.getId i
            if (← getEnv).contains n then
              idents := idents.push n
            else
              throwErrorAt i m!"unknown identifier '{n}'"
          | `(find_filter| _) => do
            throwErrorAt arg ("Cannot search for _. " ++
              "Did you forget to put a term pattern in parentheses?")
          | `(find_filter| $s:term) => do
            let e ← elabTerm' s none
            terms := terms.push (false, e)
          | _ => throwErrorAt args "unexpected argument to #find"
        | _ => throwErrorAt args "unexpected argument to #find"
    catch e => do
      let .error ref msg := e | throw e
      let suggestions1 := suggestQuoted (.fromRef ref) args
      let suggestions2 ← suggestQualifiedNames index args (.fromRef ref)
      return .error ⟨ref, msg, suggestions1 ++ suggestions2⟩

    -- Collect set of names to query the index by
    let needles : NameSet :=
          {} |> idents.foldl NameSet.insert
             |> terms.foldl (fun s (_,t) => t.foldConsts s (flip NameSet.insert))
    let (indexHits, remainingNamePats)  ← do
      if needles.isEmpty then do
        if namePats.isEmpty then
          return .error ⟨args, m!"Cannot search: No constants or name fragments in search pattern.",
            #[]⟩
        -- No constants in patterns, use trie
        let (t₁, t₂) ← index.trieCache.get
        let hitArrays := namePats.map (fun s => (s, t₁.find s ++ t₂.find s))
        -- If we have more than one name fragment pattern, use the one that returns the smallest
        -- array of names
        let hitArrays := hitArrays.qsort fun (_, a₁) (_, a₂) => a₁.size > a₂.size
        let (needle, hits) := hitArrays.back
        if hits.size == 1 then
          message := message ++ m!"Found one definition whose name contains \"{needle}\".\n"
        else
          message := message ++ m!"Found {hits.size} definitions whose name contains \"{needle}\".\n"
        let remainingNamePats := hitArrays.pop.map (·.1)
        pure (hits, remainingNamePats)
      else do
        -- Query the declaration cache
        let (m₁, m₂) ← index.nameRelCache.get
        let hits := RBTree.intersects <| needles.toArray.map <| fun needle =>
          ((m₁.find needle).union (m₂.find needle)).insert needle

        let needlesList := MessageData.andList (needles.toArray.map .ofName)
        if hits.size == 1 then
          message := message ++ m!"Found one definition mentioning {needlesList}.\n"
        else
          message := message ++ m!"Found {hits.size} definitions mentioning {needlesList}.\n"
        pure (hits, namePats)

    -- Filter by name patterns
    let nameMatchers := remainingNamePats.map (String.Matcher.ofString ·.toLower)
    let hits2 := indexHits.toArray.filter fun n => nameMatchers.all fun m =>
      m.find? n.toString.toLower |>.isSome
    unless (remainingNamePats.isEmpty) do
      let nameList := MessageData.andList <| namePats.map fun s => m!"\"{s}\""
      if hits2.size == 1 then
        message := message ++ m!"Of these, one has a name containing {nameList}.\n"
      else
        message := message ++ m!"Of these, {hits2.size} have a name containing {nameList}.\n"

    -- Obtain ConstantInfos
    let env ← getEnv
    let hits3 := hits2.filterMap env.find?

    -- Filter by term patterns
    let pats ← liftM <| terms.mapM fun (isConclusionPattern, t) =>
      if isConclusionPattern then
        matchConclusion t
      else
        matchAnywhere t
    let hits4 ← hits3.filterM fun ci => pats.allM (· ci)
    unless (pats.isEmpty) do
      if hits4.size == 1 then
        message := message ++ m!"Of these, one matches your pattern(s).\n"
      else
        message := message ++ m!"Of these, {hits4.size} match your pattern(s).\n"

    -- Sort by modindex and then by theorem size.
    let hits5 ← sortByModule' (·.name) (exprSize ·.type) hits4

    -- Apply maxShown limit
    unless (hits5.size ≤ maxShown) do
      message := message ++ m!"Of these, only the first {maxShown} are shown.\n"
    let hits6 := hits5.extract 0 maxShown

    -- Resolve ModIndex to module name
    let hits7 := hits6.map fun (ci, mi) =>
      let modName : Option Name := do env.header.moduleNames[(← mi).toNat]!
      (ci, modName)

    -- If searching by names had hits, but searching by patterns does not,
    -- suggest search just by names
    let mut suggestions := #[]
    if !needles.isEmpty && !indexHits.isEmpty && hits7.isEmpty then
      let is := needles.toArray.map Lean.mkIdent
      let sugg ← `(find_filters| $[$is:ident],*)
      suggestions := suggestions.push sugg

    return .ok ⟨message, hits4.size, hits7, suggestions⟩

/-
###  The per-module cache used by the `#find` command
-/

open System (FilePath)

/-- Where to search for the cached index -/
def cachePath : IO FilePath :=
  try
    return (← findOLean `LoogleMathlibCache).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "LoogleMathlibCache.extra"

/-- The `DeclCache` used by `#find` -/
initialize cachedIndex : Index ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _) ← unpickle _ path
    Index.mkFromCache d
  else
    Index.mk

open Command

/--
Option to control whether `find` should print types of found lemmas
-/
register_option find.showTypes : Bool := {
  defValue := true
  descr := "showing types in #f"
}

def elabFind (args : TSyntax `Loogle.Find.find_filters) : TermElabM Unit := do
  profileitM Exception "find" (← getOptions) do
      match ← find cachedIndex args with
      | .error ⟨s, warn, suggestions⟩ => do
        Lean.logErrorAt s warn
        unless suggestions.isEmpty do
          Std.Tactic.TryThis.addSuggestions args <| suggestions.map fun sugg =>
            { suggestion := .tsyntax sugg }
      | .ok result =>
        let showTypes := (<- getOptions).get find.showTypes.name find.showTypes.defValue
        let names := result.hits.map $ fun x=> (x.1.name, x.1.type)
        Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConstsAndTypes names showTypes)


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
