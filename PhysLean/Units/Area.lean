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

/-- The type of areas in the absence of a choice of unit. -/
abbrev DimArea : Type := Dimensionful (L𝓭 * L𝓭) ℝ≥0

namespace DimArea

open UnitChoices

/-!

## Basic areas

-/

open Dimensionful

/-- The dimensional area corresponding to 1 square meter. -/
noncomputable def squareMeter : DimArea := ofUnit _ 1 SI

/-- The dimensional area corresponding to 1 square foot. -/
noncomputable def squareFoot : DimArea := ofUnit _ 1 ({SI with
  length := LengthUnit.feet} : UnitChoices)

/-- The dimensional area corresponding to 1 square mile. -/
noncomputable def squareMile : DimArea := ofUnit _ 1 ({SI with
  length := LengthUnit.miles} : UnitChoices)

/-- The dimensional area corresponding to 1 are (100 square meters). -/
noncomputable def are : DimArea := ofUnit _ 100 SI

/-- The dimensional area corresponding to 1 hectare (10,000 square meters). -/
noncomputable def hectare : DimArea := ofUnit _ 10000 SI

/-- The dimensional area corresponding to 1 acre (1/640 square miles). -/
noncomputable def acre : DimArea := ofUnit _ (1/640) ({SI with
  length := LengthUnit.miles} : UnitChoices)

/-!

## Area in SI units

-/

@[simp]
lemma squareMeter_in_SI : squareMeter SI = 1 := by
  simp [squareMeter]

@[simp]
lemma squareFoot_in_SI : squareFoot SI = 0.09290304 := by
  simp [squareFoot, dimScale, LengthUnit.feet, ofUnit_apply]
  ext
  simp only [Measured.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_mk, coe_rpow,
    NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma squareMile_in_SI : squareMile SI = 2589988.110336 := by
  simp [squareMile, dimScale, LengthUnit.miles, ofUnit_apply]
  ext
  simp only [Measured.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_mk, coe_rpow,
    NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma are_in_SI : are SI = 100 := by
  simp [are]

@[simp]
lemma hectare_in_SI : hectare SI = 10000 := by
  simp [hectare]

@[simp]
lemma acre_in_SI : acre SI = 4046.8564224 := by
  simp [acre, dimScale, LengthUnit.miles, ofUnit_apply]
  ext
  simp only [NNReal.coe_mul, coe_rpow, coe_mk, NNReal.coe_ofScientific]
  norm_num

/-!

## Relations between areas

-/

/-- One acre is exactly `43560` square feet. -/
lemma acre_eq_mul_squareFeet : acre = (43560 : ℝ≥0) • squareFoot := by
  apply Dimensionful.eq_of_SI
  simp only [acre_in_SI, Dimensionful.smul_apply, squareFoot_in_SI]
  ext
  norm_num

end DimArea
