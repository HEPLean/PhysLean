/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
/-!
# Momentum

In this module we define the type `Momentum`, which represents the momentum of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/

/-- Momentum in `d`-dimensional space in an arbitary, but given, set of units.
  In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum. -/
structure Momentum (d : ℕ := 3) where
  /-- The underlying vector of a momentum. -/
  val : Fin d → ℝ

TODO "IO7OT" "On the type `Momentum` define the instance of an inner product space."
