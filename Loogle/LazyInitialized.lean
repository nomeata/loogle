import Std.Sync.Mutex

/-- Wrapper for a lazily-initializer reference. -/
structure LazilyInitialized (α : Type) : Type where
  private ref : IO.Ref (Option α)
  private mutex : Std.BaseMutex
  init : IO α
deriving Nonempty

/-- Construct a new lazily initialized reference, used typically as
```lean
initialize foo : LazilyInitialized Foo ← LazilyInitialized.new mkFoo
```
in place of
```lean
initialize foo : Foo ← mkFoo
```
-/
def LazilyInitialized.new {α} (init : IO α) : IO (LazilyInitialized α) := do
  return { ref := ← IO.mkRef none, mutex := ← Std.BaseMutex.new, init := init}

/-- Obtain the value, constructing it in a thread-safe way if necessary. -/
def LazilyInitialized.get {α} (l : LazilyInitialized α) : IO α := do
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
