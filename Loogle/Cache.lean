/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Gabriel Ebner
-/
module

public import Lean.Meta.DiscrTree

/-!
# Once-per-file cache used by loogle

`Cache`, `DeclCache`, and `DeclCache2` are loogle's own copy of the
caching scaffolding originally written for batteries (see
`Batteries.Util.Cache`), kept local so that loogle does not depend on
batteries directly.
-/

@[expose] public section

open Lean Meta

namespace Loogle.Cache

/-- Once-per-file cache. -/
def Cache (α : Type) := IO.Ref <| MetaM α ⊕ Task (Except Exception α)

-- Needed because we use `Cache` with `initialize`.
instance : Nonempty (Cache α) := inferInstanceAs <| Nonempty (IO.Ref _)

/-- Creates a cache with an initialization function. -/
def Cache.mk (init : MetaM α) : IO (Cache α) := IO.mkRef <| Sum.inl init

/-- `Meta`-flavoured `wrapAsync` (cf. `Core.wrapAsync`). -/
def metaWrapAsync {α : Type} (act : α → MetaM β) (cancelTk? : Option IO.CancelToken) :
    MetaM (α → EIO Exception β) := do
  let metaCtx ← readThe Meta.Context
  let metaSt ← getThe Meta.State
  Core.wrapAsync (fun a => act a |>.run' metaCtx metaSt) cancelTk?

/--
Access the cache. Calling this function for the first time will initialize the cache
with the function provided in the constructor.
-/
def Cache.get (cache : Cache α) : MetaM α := do
  let t ← match ← ST.Ref.get (m := BaseIO) cache with
    | .inr t => pure t
    | .inl init =>
      let res ← EIO.asTask <| (← metaWrapAsync (fun _ => init) (cancelTk? := none)) ()
      cache.set (m := BaseIO) (.inr res)
      pure res
  match t.get with
  | Except.ok res => pure res
  | Except.error err => throw err

/--
Cached fold over the environment's declarations,
where a given function is applied to `α` for every constant.
-/
structure DeclCache (α : Type) where mk' ::
  /-- The cached data. -/
  cache : Cache α
  /-- Function for adding a declaration from the current file to the cache. -/
  addDecl : Name → ConstantInfo → α → MetaM α
  /-- Function for adding a declaration from the library to the cache.
  Defaults to the same behaviour as adding a declaration from the current file. -/
  addLibraryDecl : Name → ConstantInfo → α → MetaM α := addDecl
  deriving Nonempty

/--
Creates a `DeclCache`.

The cached structure `α` is initialized with `empty`, and then `addLibraryDecl`
is called for every imported constant. After all imported constants have been
added, we run `post`. Finally, the result is cached.

When `get` is called, `addDecl` is also called for every constant in the
current file.
-/
def DeclCache.mk (profilingName : String) (empty : α)
    (addDecl : Name → ConstantInfo → α → MetaM α)
    (addLibraryDecl : Name → ConstantInfo → α → MetaM α := addDecl)
    (post : α → MetaM α := fun a => pure a) : IO (DeclCache α) := do
  let cache ← Cache.mk do
    profileitM Exception profilingName (← getOptions) do
      post <|← (← getEnv).constants.map₁.foldM (init := empty) fun a n c =>
        addLibraryDecl n c a
  pure { cache, addDecl }

/--
Access the cache. Calling this function for the first time will initialize the cache
with the function provided in the constructor.
-/
def DeclCache.get (cache : DeclCache α) : MetaM α := do
  (← getEnv).constants.map₂.foldlM (init := ← cache.cache.get) fun a n c =>
    cache.addDecl n c a

/--
A type synonym for a `DeclCache` containing a pair of elements.
The first will store declarations in the current file,
the second will store declarations from imports (and will hopefully be "read-only" after creation).
-/
def DeclCache2 (α : Type) : Type := DeclCache (α × α)

instance (α : Type) [h : Nonempty α] : Nonempty (DeclCache2 α) :=
  -- work around lack of Prod.nonempty in std/core:
  h.elim fun x => @instNonemptyDeclCache _ ⟨x,x⟩

/--
Creates a `DeclCache`.
The cached structure `α` is initialized with `empty`,
and then `addLibraryDecl` is called for every imported constant, and the result is cached.
After all imported constants have been added, we run `post`.
When `get` is called, `addDecl` is also called for every constant in the current file.
-/
def DeclCache2.mk (profilingName : String) (empty : α)
    (addDecl : Name → ConstantInfo → α → MetaM α)
    (post : α → MetaM α := fun a => pure a) : IO (DeclCache2 α) :=
  DeclCache.mk profilingName
    (empty := (empty, empty))
    (addDecl := fun n c (m₁, m₂) => do pure (← addDecl n c m₁, m₂))
    (addLibraryDecl := fun n c (m₁, m₂) => do pure (m₁, ← addDecl n c m₂))
    (post := fun (m₁, m₂) => return (m₁, ← post m₂))

/--
Access the cache.
Calling this function for the first time
will initialize the cache with the function
provided in the constructor.
-/
def DeclCache2.get (cache : DeclCache2 α) : MetaM (α × α) := DeclCache.get cache

/--
Access the cache (imports only).
Suitable to get a value to be pickled and fed to `mkFromCache` later.
-/
def DeclCache2.getImported (cache : DeclCache2 α) : CoreM α := do
  let (_, m₂) ← (cache.cache.get).run'
  pure m₂

/--
Creates a `DeclCache2` from a pre-computed index, typically obtained via `DeclCache2.getImports`.
The cached structure `α` is initialized with the given value.
When `get` is called, `addDecl` is additionally called for every constant in the current file.
-/
def DeclCache2.mkFromCache (empty : α) (addDecl : Name → ConstantInfo → α → MetaM α) (cached : α) :
    IO (DeclCache2 α) := do
  let cache ← Cache.mk (pure (empty, cached))
  pure { cache, addDecl := fun n c (m₁, m₂) => do pure (← addDecl n c m₁, m₂) }

end Loogle.Cache
