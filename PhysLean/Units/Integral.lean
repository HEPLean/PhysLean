/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!

# Dimensional invarance of the integral

-/

open UnitDependent NNReal
variable  (M : Type)
   [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
   [MeasurableSpace M] [self : MeasurableConstSMul ℝ M]

open MeasureTheory
noncomputable instance (M : Type)
   [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
   [MeasurableSpace M] [self : MeasurableConstSMul ℝ M]  :
     MulUnitDependent (MeasureTheory.Measure M) where
  changeUnits u1 μ u2 := μ.map (fun m => changeUnits u1 m u2)
  changeUnits_trans u1 u2 u3 μ := by
    rw [Measure.map_map]
    congr
    funext m
    simp [changeUnits_trans]
    simp [CarriesDimension.changeUnits_apply']
    · exact measurable_const_smul (α := M) ↑(u2.dimScale u3 (CarriesDimension.d M)).1
    · exact measurable_const_smul (α := M) ↑(u1.dimScale u2 (CarriesDimension.d M)).1
  changeUnits_trans' u1 u2 u3 μ := by
    rw [Measure.map_map]
    congr
    funext m
    simp [changeUnits_trans']
    simp [CarriesDimension.changeUnits_apply']
    · exact measurable_const_smul (α := M) ↑(u1.dimScale u2 (CarriesDimension.d M)).1
    · exact measurable_const_smul (α := M) ↑(u2.dimScale u3 (CarriesDimension.d M)).1
  changeUnits_id u μ := by
    simp [changeUnits_id]
  changeUnits_mul u1 u2 r μ := by
    simp


variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
    [MeasurableSpace M] [ MeasurableConstSMul ℝ M]
    {G : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [ModuleCarriesDimension G]

lemma changeUnits_measure  (u1 u2 : UnitChoices) (μ : MeasureTheory.Measure M)  :
    changeUnits u1 μ u2 = μ.map (fun m => changeUnits u1 m u2) := by rfl

lemma integral_isDimensionallyInvariant (d : Dimension) :
    IsDimensionallyInvariant (fun (μ : DimSet (MeasureTheory.Measure M) d)
      (f : DimSet (M → G) (CarriesDimension.d G * d⁻¹)) =>
        (MeasureTheory.integral (α := M) μ f : G)) := by
  intro u1 u2
  funext ⟨μ, hμ⟩ ⟨f, hf⟩
  calc _
    _ = changeUnits u1 (∫ x, (changeUnits u2 f u1) x ∂(changeUnits u2 μ u1)) u2  := by
      simp [instUnitDependentTwoSided]
      rfl
    _ = changeUnits u1 (u2.dimScale u1 d • ∫ (x : M), changeUnits u2 f u1 x ∂ μ) u2  := by
      rw [hμ, integral_smul_nnreal_measure]
    _ = changeUnits u1 (u2.dimScale u1 d •
      u2.dimScale u1 (CarriesDimension.d G * d⁻¹) • ∫ (x : M), f x ∂ μ) u2  := by
      rw [hf]
      congr
      erw [MeasureTheory.integral_smul]
      rfl
    _ = (u1.dimScale u2 (CarriesDimension.d G))  • ((u2.dimScale u1 d) •
        u2.dimScale u1 (CarriesDimension.d G * d⁻¹) • ∫ (x : M), f x ∂ μ)   := by
      rw [← CarriesDimension.changeUnits_apply]
    _ = (u1.dimScale u2 (CarriesDimension.d G)  * (u2.dimScale u1 d) *
        u2.dimScale u1 (CarriesDimension.d G * d⁻¹)) • ∫ (x : M), f x ∂ μ := by
      simp [smul_smul]
      ring_nf
    _ = ((u1.dimScale u2 (CarriesDimension.d G) * u2.dimScale u1 (CarriesDimension.d G))
        * (u2.dimScale u1 d * u1.dimScale u2 d)) • ∫ (x : M), f x ∂ μ := by
      congr 1
      conv_lhs => simp
      rw [UnitChoices.dimScale_of_inv_eq_swap]
      ring
    _ = ∫ (x : M), f x ∂ μ := by simp
