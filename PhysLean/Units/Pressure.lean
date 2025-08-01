/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
/-!

# Pressure

In this module we define the dimensionful type corresponding to an pressure.
We define specific insances of pressure.

-/
open Dimension
open NNReal

/-- Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`.. -/
abbrev DimPressure : Type := Dimensionful (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ

namespace DimPressure
open UnitChoices Dimensionful

/-- The dimensional pressure corresponding to 1 pascal, Pa. -/
noncomputable def pascal : DimPressure := ofUnit _ 1 SI

/-- The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals). -/
noncomputable def millimeterOfMercury : DimPressure := ofUnit _ (133.322387415) SI

/-- The dimensional pressure corresponding to 1 bar (100,000 pascals). -/
noncomputable def bar : DimPressure := ofUnit _ 100000 SI

/-- The dimensional pressure corresponding to 1 standard atmosphere (101,325 pascals). -/
noncomputable def standardAtmosphere : DimPressure := ofUnit _ (101325) SI

/-- The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure). -/
noncomputable def torr : DimPressure := (1/760) • standardAtmosphere

/-- The dimensional pressure corresponding to 1 pound per square inch. -/
noncomputable def psi : DimPressure := ofUnit _ 1 ({SI with
  mass := MassUnit.pounds,
  length := LengthUnit.inches} : UnitChoices)

end DimPressure
