/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.Basic
/-!

# Electromagnetism

In this file we define the electric field, the magnetic field, and the field strength tensor.

-/

namespace Electromagnetism

/-- The electric field is a map from `d`+1 dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := SpaceTime d → EuclideanSpace ℝ (Fin d)

/-- The magnetic field is a map from `d+1` dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := SpaceTime d → EuclideanSpace ℝ (Fin d)

open IndexNotation
open realLorentzTensor

/-- The Field strength is a tensor `F^μ^ν` which is anti-symmetric.. -/
noncomputable abbrev FieldStrength (d : ℕ := 3) := SpaceTime d →
  {F : ℝT[d, .up, .up] | {F | μ ν = - (F | ν μ)}ᵀ}

end Electromagnetism
