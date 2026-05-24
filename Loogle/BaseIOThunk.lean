module

public import Std.Sync.Mutex

/-!
# Monadic version of `Thunk`

This file defines `Loogle.BaseThunk` and `Loogle.Thunk`.

It makes the choice that errors are cached just like values,
as opposed to declaring them uncacheable as Python's `functools` caching operations do.
-/

public section

namespace Loogle

/-- A version of `Thunk` that runs in `BaseIO`.

Note that unlike `Thunk`, this does not have optimized C-side support. -/
structure BaseThunk (α : Type) : Type where
  private ref : IO.Ref (Option α)
  private mutex : Std.BaseMutex
  init : BaseIO α
deriving Nonempty

/-- Construct a new lazily initialized reference, used typically as
```lean
initialize foo : Loogle.BaseThunk Foo ← Loogle.BaseThunk.new mkFoo
```
in place of
```lean
initialize foo : Foo ← mkFoo
```
-/
def BaseThunk.new {α} (init : BaseIO α) : BaseIO (BaseThunk α) := do
  return { ref := ← IO.mkRef none, mutex := ← Std.BaseMutex.new, init := init}

/-- Obtain the value, constructing it in a thread-safe way if necessary. -/
def BaseThunk.get {α} (l : BaseThunk α) : BaseIO α := do
  if let .some a ← l.ref.get then
    return a
  try
    l.mutex.lock
    if let .some a ← l.ref.get then
      return a
    let a ← l.init
    l.ref.set (some a)
    return a
  finally
    l.mutex.unlock

/-- A wrapper for `Loogle.BaseThunk` to also cache `IO.Error`s.-/
abbrev Thunk (α : Type) : Type := BaseThunk (Except IO.Error α)

/-- Construct a new lazily initialized reference, used typically as
```lean
initialize foo : Loogle.Thunk Foo ← Loogle.Thunk.new mkFoo
```
in place of
```lean
initialize foo : Foo ← mkFoo
```
-/
def Thunk.new {α} (init : IO α) : BaseIO (Thunk α) := BaseThunk.new <| init.toBaseIO

/-- Obtain the value, constructing it in a thread-safe way if necessary.

If the initializer fails, the error is also cached.
Note this diverges from the behavior of Python's `@functools.lru_cache` and related helpers. -/
def Thunk.get {α} (l : Thunk α) : IO α := do
  match ← BaseThunk.get l with
  | .ok a => return a
  | .error e => throw e

end Loogle
