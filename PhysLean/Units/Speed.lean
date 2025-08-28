/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
/-!

# Speed

In this module we define the dimensionful type corresponding to an speed.
We define specific insances of speed, such as miles per hour, kilometers per hour, etc.

-/
open Dimension
open NNReal

/-- The type of speeds in the absence of a choice of unit. -/
abbrev DimSpeed : Type := Dimensionful (L𝓭 * T𝓭⁻¹) ℝ≥0

namespace DimSpeed

open UnitChoices

/-!

## Basic speeds

-/
open Dimensionful
/-- The dimensional speed corresponding to 1 meter per second. -/
noncomputable def oneMeterPerSecond : DimSpeed := ofUnit _ 1 SI

/-- The dimensional speed corresponding to 1 mile per hour. -/
noncomputable def oneMilePerHour : DimSpeed := ofUnit _ 1 ({SI with
  length := LengthUnit.miles, time := TimeUnit.hours} : UnitChoices)

/-- The dimensional speed corresponding to 1 kilometer per hour. -/
noncomputable def oneKilometerPerHour : DimSpeed := ofUnit _ 1 ({SI with
  length := LengthUnit.kilometers, time := TimeUnit.hours} : UnitChoices)

/-- The dimensional speed corresponding to 1 knot, aka, one nautical mile per hour. -/
noncomputable def oneKnot : DimSpeed := ofUnit _ 1 ({SI with
  length := LengthUnit.nauticalMiles, time := TimeUnit.hours} : UnitChoices)

/-!

## Speed in SI units

-/

@[simp]
lemma oneMeterPerSecond_in_SI : oneMeterPerSecond SI = 1 := by
  simp [oneMeterPerSecond]

@[simp]
lemma oneMilePerHour_in_SI : oneMilePerHour SI = 0.44704 := by
  simp [oneMilePerHour, dimScale, LengthUnit.miles, TimeUnit.hours, ofUnit_apply]
  ext
  simp only [NNReal.coe_mul, coe_mk, coe_rpow, NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma oneKilometerPerHour_in_SI :
    oneKilometerPerHour SI = 5/18 := by
  simp [oneKilometerPerHour, dimScale, LengthUnit.kilometers, TimeUnit.hours, ofUnit_apply]
  ext
  simp only [NNReal.coe_mul, coe_mk, coe_rpow]
  norm_num

@[simp]
lemma oneKnot_in_SI : oneKnot SI = 463/900 := by
  simp [oneKnot, dimScale, LengthUnit.nauticalMiles, TimeUnit.hours, ofUnit_apply]
  ext
  simp only [NNReal.coe_mul, coe_mk, coe_rpow]
  norm_num

/-!

## Relations between speeds

-/

lemma oneKnot_eq_mul_oneKilometerPerHour :
    oneKnot = (1.852 : ℝ≥0) • oneKilometerPerHour := by
  apply Dimensionful.eq_of_SI
  simp [oneKnot_in_SI, oneKilometerPerHour_in_SI]
  ext
  norm_num

lemma oneKilometerPerHour_eq_mul_oneKnot:
    oneKilometerPerHour = (250/463 : ℝ≥0) • oneKnot := by
  apply Dimensionful.eq_of_SI
  simp [oneKilometerPerHour_in_SI]
  ext
  norm_num

lemma oneMeterPerSecond_eq_mul_oneMilePerHour :
    oneMeterPerSecond = (3125/1397 : ℝ≥0) • oneMilePerHour := by
  apply Dimensionful.eq_of_SI
  simp [oneMeterPerSecond_in_SI, oneMilePerHour_in_SI]
  ext
  norm_num

/-!

## Comparisons between speeds

-/
/-- One kilometer per hour is slower then one knot. -/
lemma oneKilometerPerHour_le_oneKnot : oneKilometerPerHour ≤ oneKnot := by
  apply Dimensionful.le_nnReals_of_unitChoice SI
  simp only [oneKilometerPerHour_in_SI, oneKnot_in_SI]
  refine coe_le_coe.mp ?_
  norm_num

lemma oneKilometerPerHour_le_oneMilPerHour : oneKilometerPerHour ≤ oneMilePerHour := by
  apply Dimensionful.le_nnReals_of_unitChoice SI
  simp only [oneKilometerPerHour_in_SI, oneMilePerHour_in_SI]
  refine coe_le_coe.mp ?_
  norm_num

lemma oneMilePerHour_le_oneKnot : oneMilePerHour ≤ oneKnot := by
  apply Dimensionful.le_nnReals_of_unitChoice SI
  simp only [oneMilePerHour_in_SI, oneKnot_in_SI]
  refine coe_le_coe.mp ?_
  norm_num

lemma oneMilePerHour_le_oneMeterPerSecond : oneMilePerHour ≤ oneMeterPerSecond := by
  apply Dimensionful.le_nnReals_of_unitChoice SI
  simp only [oneMilePerHour_in_SI, oneMeterPerSecond_in_SI]
  refine coe_le_coe.mp ?_
  norm_num

lemma oneMeterPerSecond_le_oneKnot : oneKnot ≤ oneMeterPerSecond := by
  apply Dimensionful.le_nnReals_of_unitChoice SI
  simp only [oneKnot_in_SI, oneMeterPerSecond_in_SI]
  refine coe_le_coe.mp ?_
  norm_num

end DimSpeed
