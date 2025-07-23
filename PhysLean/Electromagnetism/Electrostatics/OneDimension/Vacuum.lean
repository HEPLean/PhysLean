/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Mathematics.Distribution.OfBounded
import PhysLean.Mathematics.Distribution.PowMul
/-!

# A electrostatics in a 1d vacuum

In this module we study the electrostatics in 1d with the presence of no charges.

The aim of this module is to show that, in 1-dimension, if an electric field satifies
Gauss's law for the vacuum, then it must be the constant electric field.

-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace OneDimVacuum
open Space StaticElectricField MeasureTheory
noncomputable section

/-- The zero charge distribution in 1d space. -/
def chargeDistribution : ChargeDistribution 1 := 0

/-- An electric field obey's Gauss's law for the vacuum in 1 dimension if and only if
  it is the constant electric field. -/
@[sorryful]
lemma gaussLaw_iff (q ε : ℝ) (E : StaticElectricField 1) :
    E.GaussLaw ε (chargeDistribution) ↔ ∃ m, E = constD 1 m := by
  sorry

end
end OneDimVacuum

end Electromagnetism
