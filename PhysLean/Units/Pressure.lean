/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
import PhysLean.Units.WithDim
/-!

# Pressure

In this module we define the dimensionful type corresponding to an pressure.
We define specific insances of pressure.

-/
open Dimension
open NNReal

/-- Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`.. -/
abbrev DimPressure : Type := Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

namespace DimPressure
open UnitChoices Dimensionful CarriesDimension

/-- The dimensional pressure corresponding to 1 pascal, Pa. -/
noncomputable def pascal : DimPressure := toDimensionful SI ⟨1⟩

/-- The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals). -/
noncomputable def millimeterOfMercury : DimPressure := toDimensionful SI ⟨133.322387415⟩

/-- The dimensional pressure corresponding to 1 bar (100,000 pascals). -/
noncomputable def bar : DimPressure := toDimensionful SI ⟨100000⟩

/-- The dimensional pressure corresponding to 1 standard atmosphere (101,325 pascals). -/
noncomputable def standardAtmosphere : DimPressure := toDimensionful SI ⟨101325⟩

/-- The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure). -/
noncomputable def torr : DimPressure := (1/760 : ℝ≥0) • standardAtmosphere

/-- The dimensional pressure corresponding to 1 pound per square inch. -/
noncomputable def psi : DimPressure := toDimensionful ({SI with
  mass := MassUnit.pounds,
  length := LengthUnit.inches} : UnitChoices) ⟨1⟩

end DimPressure
