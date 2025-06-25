/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.TODO.Basic
/-!

# Temperature

In this module we define the type `Temperature`, and give basic properties thereof.

-/
open NNReal

/-- The type of temperatures. -/
def Temperature : Type := ℝ≥0

namespace Temperature
open Constants

noncomputable instance : LinearOrder Temperature :=
  Subtype.instLinearOrder _

/-- The underlying real-number associated with the tempature. -/
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T

noncomputable instance : Coe Temperature ℝ := ⟨toReal⟩

/-- The inverse temperature. -/
noncomputable def β (T : Temperature) : ℝ := 1 / (kB * T)

TODO "EQTKM" "Define the function from `Temperature` to `ℝ` which gives the temperature in
  Kelvin, based on axiomized constants. "

end Temperature
