/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.UnitDependent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!

# Dimensional invarance of the integral

In this module we prove that the dimensional properties of the integral.

-/

open UnitDependent NNReal
variable (M : Type)
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
    [MeasurableSpace M] [self : MeasurableConstSMul ℝ M]

open MeasureTheory
noncomputable instance (M : Type)
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
    [MeasurableSpace M] [self : MeasurableConstSMul ℝ M] :
      MulUnitDependent (MeasureTheory.Measure M) where
  scaleUnit u1 u2 μ := μ.map (fun m => scaleUnit u1 u2 m)
  scaleUnit_trans u1 u2 u3 μ := by
    rw [Measure.map_map]
    congr
    funext m
    simp [scaleUnit_trans]
    simp [CarriesDimension.scaleUnit_apply']
    · exact measurable_const_smul (α := M) ↑(u2.dimScale u3 (CarriesDimension.d M)).1
    · exact measurable_const_smul (α := M) ↑(u1.dimScale u2 (CarriesDimension.d M)).1
  scaleUnit_trans' u1 u2 u3 μ := by
    rw [Measure.map_map]
    congr
    funext m
    simp [scaleUnit_trans']
    simp [CarriesDimension.scaleUnit_apply']
    · exact measurable_const_smul (α := M) ↑(u1.dimScale u2 (CarriesDimension.d M)).1
    · exact measurable_const_smul (α := M) ↑(u2.dimScale u3 (CarriesDimension.d M)).1
  scaleUnit_id u μ := by
    simp [scaleUnit_id]
  scaleUnit_mul u1 u2 r μ := by
    simp

variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [ModuleCarriesDimension M]
    [MeasurableSpace M] [MeasurableConstSMul ℝ M]
    {G : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [ModuleCarriesDimension G]

lemma scaleUnit_measure (u1 u2 : UnitChoices) (μ : MeasureTheory.Measure M) :
    scaleUnit u1 u2 μ = μ.map (fun m => scaleUnit u1 u2 m) := by rfl

/-- The statement that for a measure `μ` of dimension `d`, and a function
  `f : M → G` of dimension `(CarriesDimension.d G * d⁻¹)` (where `CarriesDimension.d G`
  is the dimension associated with terms of type `G`), then
  `∫ x, f x ∂μ `
  has the correct dimension, namely `CarriesDimension.d G`.

  In other words, the function:
```
fun (μ : DimSet (MeasureTheory.Measure M) d)
    (f : DimSet (M → G) (CarriesDimension.d G * d⁻¹)) ↦ ∫ x, f.1 x ∂μ.1
```
  is dimensionally invariant. -/
lemma integral_isDimensionallyInvariant (d : Dimension) :
    IsDimensionallyInvariant (fun (μ : DimSet (MeasureTheory.Measure M) d)
      (f : DimSet (M → G) (CarriesDimension.d G * d⁻¹)) ↦ ∫ x, f.1 x ∂μ.1) := by
  intro u1 u2
  funext ⟨μ, hμ⟩ ⟨f, hf⟩
  /- We have to prove that
    `scaleUnit u1 (fun μ f ↦ ∫ x, f x ∂μ) u2 ⟨μ, hμ⟩ ⟨f, hf⟩ = ∫ x, f x ∂μ` -/
  calc _
    /- By definition the LHS is equal to
    `scaleUnit u1 u2 (∫ x, (scaleUnit u2 u1 f) x ∂(scaleUnit u2 u1 μ)) `
    The statement says, suppose `f` and `μ` are in units `u2`, we change them to units `u1`,
    then do the integral, and then we take the result back to `u2`.
    If the integral is dimensionally invariant, this should be the same as just doing the
    original integral in `u2` units i.e. `∫ x, f x ∂μ`. -/
    _ = scaleUnit u1 u2 (∫ x, (scaleUnit u2 u1 f) x ∂(scaleUnit u2 u1 μ)) := by
      simp [instUnitDependentTwoSided]
    /- Since we have assumed `μ` has dimension `d`, `(scaleUnit u2 μ u1)`
      is equal to `(u2.dimScale u1 d) • μ` -/
    _ = scaleUnit u1 u2 (u2.dimScale u1 d • ∫ (x : M), scaleUnit u2 u1 f x ∂ μ) := by
      rw [hμ, integral_smul_nnreal_measure]
    /- Since we assumed `f` has dimension `CarriesDimension.d G * d⁻¹`, `(scaleUnit u2 f u1)`
      is equal to `u2.dimScale u1 (CarriesDimension.d G * d⁻¹) • f`. -/
    _ = scaleUnit u1 u2 (u2.dimScale u1 d •
      u2.dimScale u1 (CarriesDimension.d G * d⁻¹) • ∫ (x : M), f x ∂ μ) := by
      rw [hf]
      congr
      erw [MeasureTheory.integral_smul]
      rfl
    /- What remains is a simple cancellation of the dimensional scales. -/
    _ = (u1.dimScale u2 (CarriesDimension.d G)) • ((u2.dimScale u1 d) •
        u2.dimScale u1 (CarriesDimension.d G * d⁻¹) • ∫ (x : M), f x ∂ μ) := by
      rw [← CarriesDimension.scaleUnit_apply]
    _ = (u1.dimScale u2 (CarriesDimension.d G) * (u2.dimScale u1 d) *
        u2.dimScale u1 (CarriesDimension.d G * d⁻¹)) • ∫ (x : M), f x ∂ μ := by
      simp [smul_smul]
      ring_nf
    _ = ((u1.dimScale u2 (CarriesDimension.d G) * u2.dimScale u1 (CarriesDimension.d G))
        * (u2.dimScale u1 d * u1.dimScale u2 d)) • ∫ (x : M), f x ∂ μ := by
      congr 1
      conv_lhs => simp only [map_mul]
      rw [UnitChoices.dimScale_of_inv_eq_swap]
      ring
    _ = ∫ (x : M), f x ∂ μ := by simp
