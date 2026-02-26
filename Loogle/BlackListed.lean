/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, E.W.Ayers, Arthur Paulino
-/
import Lean

namespace Loogle

open Lean Meta

/-- Decides whether a declaration should be hidden from the user.

This follows the same logic as doc-gen4's `isBlackListed`
(see `DocGen4/Process/DocInfo.lean`):
- Projection functions (structure field accessors) are always shown.
- Declarations without source ranges are hidden (these are auto-generated, e.g.
  `injEq`, `sizeOf_spec`, `ctorIdx`).
- Declarations with internal names, auxiliary recursors, no-confusion lemmas,
  matchers, and recursors are hidden.
-/
def isBlackListed {m} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    (declName : Name) : m Bool := do
  if (← getEnv).isProjectionFn declName then return false
  match ← findDeclarationRanges? declName with
  | some _ =>
    let env ← getEnv
    pure (declName.isInternal)
    <||> (pure <| isAuxRecursor env declName)
    <||> (pure <| isNoConfusion env declName)
    <||> (pure <| declName.isInternalDetail)
    <||> isRec declName
    <||> isMatcher declName
  | none => return true

end Loogle
