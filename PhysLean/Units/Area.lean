/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
/-!

# Area

In this module we define the dimensionful type corresponding to an area.
We define specific insances of areas, such as square meters, square feet, etc.

-/
open Dimension
open NNReal

/-- An area in a specific (but arbitary) choice of units. -/
abbrev Area : Type := Measured (L𝓭 * L𝓭) ℝ≥0

/-- The type of areas in the absence of a choice of unit. -/
abbrev DimArea : Type := Dimensionful (L𝓭 * L𝓭) ℝ≥0

namespace DimArea

open UnitChoices

/-!

## Basic areas

-/

/-- The dimensional area corresponding to 1 square meter. -/
noncomputable def squareMeter : DimArea := (⟨1⟩ : Area) • SI

/-- The dimensional area corresponding to 1 square foot. -/
noncomputable def squareFoot : DimArea := (⟨1⟩ : Area) • ({SI with
  length := LengthUnit.feet} : UnitChoices)

/-- The dimensional area corresponding to 1 square mile. -/
noncomputable def squareMile : DimArea := (⟨1⟩ : Area) • ({SI with
  length := LengthUnit.miles} : UnitChoices)

/-- The dimensional area corresponding to 1 are (100 square meters). -/
noncomputable def are : DimArea := (⟨100⟩ : Area) • SI

/-- The dimensional area corresponding to 1 hectare (10,000 square meters). -/
noncomputable def hectare : DimArea := (⟨10000⟩ : Area) • SI

/-- The dimensional area corresponding to 1 acre (1/640 square miles). -/
noncomputable def acre : DimArea := (⟨1/640⟩ : Area) • ({SI with
  length := LengthUnit.miles} : UnitChoices)

/-!

## Area in SI units

-/

@[simp]
lemma squareMeter_in_SI : squareMeter SI = ⟨1⟩ := by
  simp [squareMeter]
  ext
  simp

@[simp]
lemma squareFoot_in_SI : squareFoot SI = ⟨0.09290304⟩ := by
  simp [squareFoot, dimScale, LengthUnit.feet]
  ext
  simp only [Measured.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_mk, coe_rpow,
    NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma squareMile_in_SI : squareMile SI = ⟨2589988.110336⟩ := by
  simp [squareMile, dimScale, LengthUnit.miles]
  ext
  simp only [Measured.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_mk, coe_rpow,
    NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma are_in_SI : are SI = ⟨100⟩ := by
  simp [are]
  ext
  simp

@[simp]
lemma hectare_in_SI : hectare SI = ⟨10000⟩ := by
  simp [hectare]
  ext
  simp

@[simp]
lemma acre_in_SI : acre SI = ⟨4046.8564224⟩ := by
  simp [acre, dimScale, LengthUnit.miles]
  ext
  simp only [Measured.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_mk, coe_rpow,
    NNReal.coe_ofScientific]
  norm_num

/-!

## Relations between areas

-/

/-- One acre is exactly `43560` square feet. -/
lemma acre_eq_mul_squareFeet : acre = (43560 : ℝ≥0) • squareFoot := by
  apply Dimensionful.eq_of_SI
  simp
  ext
  norm_num

end DimArea
