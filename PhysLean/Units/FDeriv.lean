/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic
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

open CarriesDimension NNReal
open ContinuousLinearUnitDependent in
/-- If a function is dimensionally valid then so is it's derivative. -/
lemma fderiv_isDimensionallyInvariant {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
    [ContinuousConstSMul ℝ M1] [ModuleCarriesDimension M1]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2]
    [SMulCommClass ℝ ℝ M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ModuleCarriesDimension M2]
    (f : M1 → M2) (hf : IsDimensionallyInvariant f) (f_diff : Differentiable ℝ f) :
    IsDimensionallyInvariant (fderiv ℝ f) := by
  rw [isDimensionallyInvariant_iff]
  intro u1 u2
  replace hf := hf u2 u1
  ext m m'
  simp [instUnitDependentTwoSided, instContinuousLinearUnitDependentMap]
  change (toDimensionful u1 ((fderiv ℝ f ((toDimensionful u2 m).1 u1))
      ((toDimensionful u2 m').1 u1))).1 u2 = (fderiv ℝ f m) m'
  simp [toDimensionful_apply_apply]
  conv_lhs =>
    rw [← hf]
    simp [instUnitDependentTwoSided]
    enter [2, 2, 1, 2, mx]
    change (toDimensionful u2 (f ((toDimensionful u1 mx).1 u2))).1 u1
    simp [toDimensionful_apply_apply]
    change (u2.dimScale u1 (d M2)).1 • f ((u1.dimScale u2 (d M1)).1 • mx)
  have h1 : (fderiv ℝ (fun mx => (u2.dimScale u1 (d M2)).1 • f
      ((u1.dimScale u2 (d M1)).1 • mx)) ((u2.dimScale u1 (d M1)).1 • m))
      = u2.dimScale u1 (d M2) • u1.dimScale u2 (d M1) • (fderiv ℝ f m) := by
    change (fderiv ℝ ((u2.dimScale u1 (d M2)).1 • fun mx => f
      ((u1.dimScale u2 (d M1)).1 • mx)) ((u2.dimScale u1 (d M1)).1 • m)) = _
    rw [fderiv_const_smul (by fun_prop)]
    rw [fderiv_comp_smul]
    simp only [val_eq_coe]
    congr
    rw [smul_smul]
    change ((u1.dimScale u2 (d M1)) * (u2.dimScale u1 (d M1))) • m = m
    simp
  erw [h1]
  simp [smul_smul]
  trans (1 : ℝ≥0) • (fderiv ℝ f m) m'
  · congr
    trans (u1.dimScale u2 (d M2) * u2.dimScale u1 (d M2))
      * (u2.dimScale u1 (d M1) * u1.dimScale u2 (d M1))
    · ring
    simp
  simp
