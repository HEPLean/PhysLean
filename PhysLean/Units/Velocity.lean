/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
/-!
# Velocity

In this module we define the type `Velocity`, which represents the velocity of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/
open Dimension

/-- Velocity in `d`-dimensional space in an arbitary, but given, set of units.
  In `(3+1)d` space time this corresponds to `3`-velocity not `4`-velocity. -/
abbrev Velocity (d : ℕ := 3) : Type := Measured (L𝓭 * T𝓭⁻¹) (Fin d → ℝ)
