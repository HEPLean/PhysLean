/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.UnitDependent
import PhysLean.Units.WithDim.Basic
/-!

# Dimensional invarance of fderiv

In this module we prove that the derivative is dimensionally correct.
That is to say for a function `f : M1 → M2` where `M1` carrys dimensions `d1` and `M2` carrys
dimension `d2` such that `f` has the correct dimension, then
`fderiv ℝ f : M1 → M1 →L[ℝ] M2` has the correct dimensions.

To give an explicit example let us say `M1` has dimension `L𝓭` and `M2` has dimension
`L𝓭 * L𝓭` and `f : M1 → M2 : x ↦ x ^ 2`, this is dimensionally correct.
The `fderiv` of this `fderiv ℝ f : M1 → M1 →L[ℝ] M2` takes
`x dx ↦ dx • (2 * x)` which is still dimensionally correct. Here `dx` is the direction
in which the derivative is taken.

-/

open UnitDependent CarriesDimension NNReal

variable {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
    [ContinuousConstSMul ℝ M1] [ModuleCarriesDimension M1]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2]
    [SMulCommClass ℝ ℝ M2] [ContinuousConstSMul ℝ M2]
    [ModuleCarriesDimension M2]

lemma fderiv_apply_scaleUnit (u1 u2 : UnitChoices)  (x dm : M1)
    (f : M1 → M2) (hf : IsDimensionallyCorrect f) (f_diff : Differentiable ℝ f) :
    fderiv ℝ f (scaleUnit u2 u1 x) dm =
    u2.dimScale u1 (d M2) • u1.dimScale u2 (d M1) • fderiv ℝ f x dm := by
  conv_lhs => rw [← hf u2 u1]
  change  (fderiv ℝ ((u2.dimScale u1 (d M2)).1 • fun mx => f
      ((u1.dimScale u2 (d M1)).1 • mx)) ((u2.dimScale u1 (d M1)).1 • x)) dm = _
  rw [fderiv_const_smul (by fun_prop), fderiv_comp_smul]
  simp [smul_smul]
  rfl

open ContinuousLinearUnitDependent in
/-- If a function is dimensionally valid then so is it's derivative. -/
lemma fderiv_isDimensionallyCorrect  (f : M1 → M2) (hf : IsDimensionallyCorrect f)
    (f_diff : Differentiable ℝ f) :
    IsDimensionallyCorrect (fderiv ℝ f) := by
  simp only [isDimensionallyCorrect_fun_iff]
  intro u1 u2 m
  ext m'
  simp only [ContinuousLinearUnitDependent.scaleUnit_apply_fun]
  rw [fderiv_apply_scaleUnit u1 u2 m (scaleUnit u2 u1 m') f hf f_diff]
  simp only [ModuleCarriesDimension.scaleUnit_apply, map_smul]
  simp only [← smul_def, smul_smul]
  trans (1 : ℝ≥0) • (fderiv ℝ f m) m'
  · congr
    trans (u1.dimScale u2 (d M2) * u2.dimScale u1 (d M2))
      * (u2.dimScale u1 (d M1) * u1.dimScale u2 (d M1))
    · simp
    simp
  simp

/-- The expression `fderiv ℝ f x dm = v.1` for a fixed `dm` and for
  `v` with dimension `d M2 * (d M1)⁻¹` is dimensionally correct. This is the
  ordinary manifestation of dimensions of a derivative, usually `dm` is taken as e.g. `1`.

  This result also shows that dimensional correctness does depend on what
  quantities are condsidered dimensionful. -/
lemma fderiv_dimension_const_direction (dm : M1)
    (f : M1 → M2) (hf : IsDimensionallyCorrect f) (f_diff : Differentiable ℝ f) :
    IsDimensionallyCorrect (fun x (v : WithDim (d M2 * (d M1)⁻¹) M2) =>
      fderiv ℝ f x dm = v.1) := by
  rw [isDimensionallyCorrect_fun_iff]
  intro u1 u2 m
  ext v
  simp [WithDim.scaleUnit_val, fderiv_apply_scaleUnit u1 u2 m dm f hf f_diff,
    ← smul_smul, ← UnitChoices.dimScale_symm]
