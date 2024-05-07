/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Batteries.Util.Cache

open Lean Meta

-- Odd to have that namespace in std4
namespace Batteries.Tactic

/--
A type synonym for a `DeclCache` containing a pair of elements.
The first will store declarations in the current file,
the second will store declarations from imports (and will hopefully be "read-only" after creation).
-/
def DeclCache2 (α : Type) : Type := DeclCache (α × α)

instance (α : Type) [h : Nonempty α] : Nonempty (DeclCache2 α) :=
  -- inferInstanceAs (Nonempty (DeclCache (α × α)))
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
  let (_, m₂) ← cache.cache.get
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
