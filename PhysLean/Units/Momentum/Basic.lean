/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
import PhysLean.Units.Basic
import PhysLean.Units.Velocity
import PhysLean.Units.Mass
/-!
# Momentum

In this module we define the type `Momentum`, which represents the momentum of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/
open Dimension

/-- Momentum in `d`-dimensional space in an arbitary, but given, set of units.
  In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum. -/
abbrev Momentum (d : ℕ := 3) : Type := Measured (M𝓭 * L𝓭 * T𝓭⁻¹) (Fin d → ℝ)

TODO "IO7OT" "On the type `Momentum` define the instance of a vector space."

namespace Momentum

unseal Rat.add Rat.mul

/-- The momentum of a particle with mass `m` and velocity `v`. -/
def ofMassAndVelocity {d} (m : Mass) (v : Velocity d) : Momentum d := m • v

end Momentum
