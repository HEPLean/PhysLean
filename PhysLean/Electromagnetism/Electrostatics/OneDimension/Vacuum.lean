/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Mathematics.Distribution.OfBounded
import PhysLean.Mathematics.Distribution.PowMul
/-!

# A electrostatics of a point particle in 1d.

-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace OneDimVacuum
open Space StaticElectricField MeasureTheory
noncomputable section


def chargeDistribution : ChargeDistribution 1 := 0

end
end OneDimVacuum

end Electromagnetism
