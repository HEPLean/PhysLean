/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
/-!
# Time

In this file we define the time worldvolume as a real line.

-/

/-- The type `Time` represents the time manifold. -/
abbrev Time := ℝ

namespace Time

/-- Given a function `f : Time → M` the derivative of `f`. -/
informal_definition deriv where
  deps := []
  tag := "7MTUR"

end Time
