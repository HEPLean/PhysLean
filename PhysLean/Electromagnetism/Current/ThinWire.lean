/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Electromagnetism.Distributions.Potential
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
import PhysLean.SpaceAndTime.Space.DistConst
import PhysLean.Mathematics.Distribution.PowMul
/-!

# The magnetic field around a thin wire
-/

namespace Electromagnetism
open Distribution SchwartzMap
open Space StaticElectricField MeasureTheory

/-!

## B. The Potentials

-/

/-!

### B.1. The electromagnetic potential

-/

/-- The electromagnetic potential of a point particle stationary at the origin
  of 1d space. -/
noncomputable def thinWire (I : ℝ) : ElectromagneticPotentialD 3 :=
  ElectromagneticPotentialD.toComponents.symm fun μ =>
  match μ with
  | Sum.inl 0 => 0
  | Sum.inr 0 => SpaceTime.distTimeSlice.symm <| Space.constantTime <| Distribution.ofFunction
    (fun x => - I / (2 * Real.pi) * Real.log ‖x‖)
      (IsDistBounded.log.const_smul _)
      (AEMeasurable.aestronglyMeasurable <| by fun_prop)
  | Sum.inr ⟨Nat.succ i, h⟩ =>  0


end Electromagnetism
