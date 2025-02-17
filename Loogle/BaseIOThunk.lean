import Std.Sync.Mutex

/-!
# Monadic version of `Thunk`

This file defines `BaseIO.Thunk` and `IO.Thunk`.

It makes the choice that errors are cached just like values,
as opposed to declaring them uncacheable as Python's `functools` caching operations do.
-/

/-- A version of `Thunk` that runs in `BaseIO`.

Note that unlike `Thunk`, this does not have optimized C-side support. -/
structure BaseIO.Thunk (α : Type) : Type where
  private ref : IO.Ref (Option α)
  private mutex : Std.BaseMutex
  init : BaseIO α
deriving Nonempty

/-- Construct a new lazily initialized reference, used typically as
```lean
initialize foo : BaseIO.Thunk Foo ← BaseIO.Thunk.new mkFoo
```
in place of
```lean
initialize foo : Foo ← mkFoo
```
-/
def BaseIO.Thunk.new {α} (init : BaseIO α) : BaseIO (BaseIO.Thunk α) := do
  return { ref := ← IO.mkRef none, mutex := ← Std.BaseMutex.new, init := init}

/-- Obtain the value, constructing it in a thread-safe way if necessary. -/
def BaseIO.Thunk.get {α} (l : BaseIO.Thunk α) : BaseIO α := do
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

/-- A wrapper for `BaseIO.Thunk` to also cache `IO.Error`s.-/
abbrev IO.Thunk (α : Type) : Type := BaseIO.Thunk (Except IO.Error α)

/-- Construct a new lazily initialized reference, used typically as
```lean
initialize foo : IO.Thunk Foo ← IO.Thunk.new mkFoo
```
in place of
```lean
initialize foo : Foo ← mkFoo
```
-/
def IO.Thunk.new {α} (init : IO α) : BaseIO (IO.Thunk α) := BaseIO.Thunk.new <| init.toBaseIO

/-- Obtain the value, constructing it in a thread-safe way if necessary.

If the initializer fails, the error is also cached.
Note this diverges from the behavior of Python's `@functools.lru_cache` and related helpers. -/
def IO.Thunk.get {α} (l : IO.Thunk α) : IO α := do
  match ← BaseIO.Thunk.get l with
  | .ok a => return a
  | .error e => throw e
