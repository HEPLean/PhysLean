/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.DistOfFunction
import PhysLean.SpaceAndTime.Space.Derivatives.Grad
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm
/-!

# The norm on space

## i. Overview

The main content of this file is defining `Space.normPowerSeries`, a power series which is
differentiable everywhere, and which tends to the norm in the limit as `n → ∞`.

## ii. Key results

- `normPowerSeries` : A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`.
- `normPowerSeries_differentiable` : The power series is differentiable everywhere.
- `normPowerSeries_tendsto` : The power series tends to the norm in the limit as `n → ∞`.

## iii. Table of contents

- A. The norm as a power series
  - A.1. Differentiability of the norm power series
  - A.2. The limit of the norm power series
  - A.3. The derivative of the norm power series
  - A.4. Limits of the derivative of the power series
  - A.5. The power series is AEStronglyMeasurable
  - A.6. Bounds on the norm power series
  - A.7. The `IsDistBounded` property of the norm power series
  - A.8. Differentiability of functions
  - A.9. Derivatives of functions
  - A.10. Gradients of distributions
- B. Distributions involving norms

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory
/-!

## A. The norm as a power series

-/

/-- A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`. -/
def normPowerSeries {d} : ℕ → Space d → ℝ := fun n x =>
  √(‖x‖ ^ 2 + 1/(n + 1))

lemma normPowerSeries_eq (n : ℕ) :
    normPowerSeries (d := d) n = fun x => √(‖x‖ ^ 2 + 1/(n + 1)) := rfl

lemma normPowerSeries_eq_rpow {d} (n : ℕ) :
    normPowerSeries (d := d) n = fun x => ((‖x‖ ^ 2 + 1/(n + 1))) ^ (1/2 : ℝ) := by
  rw [normPowerSeries_eq]
  funext x
  rw [← Real.sqrt_eq_rpow]

/-!

### A.1. Differentiability of the norm power series

-/

@[fun_prop]
lemma normPowerSeries_differentiable {d} (n : ℕ) :
    Differentiable ℝ (fun (x : Space d) => normPowerSeries n x) := by
  rw [normPowerSeries_eq_rpow]
  refine Differentiable.rpow_const ?_ ?_
  · refine (Differentiable.fun_add_iff_right ?_).mpr ?_
    · apply Differentiable.norm_sq ℝ
      fun_prop
    · fun_prop
  · intro x
    have h1 : 0 < ‖x‖ ^ 2 + 1 / (↑n + 1) := by positivity
    grind

/-!

### A.2. The limit of the norm power series

-/
open InnerProductSpace

open scoped Topology BigOperators FourierTransform

lemma normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => normPowerSeries n x) Filter.atTop (𝓝 (‖x‖)) := by
  conv => enter [1, n]; rw [normPowerSeries_eq_rpow]
  simp only [one_div]
  have hx_norm : ‖x‖ = (‖x‖ ^ 2 + 0) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    simp
  conv_rhs => rw [hx_norm]
  refine Filter.Tendsto.rpow ?_ ?_ ?_
  · apply Filter.Tendsto.add
    · exact tendsto_const_nhds
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  · simp
  · left
    simpa using hx

lemma normPowerSeries_inv_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => (normPowerSeries n x)⁻¹) Filter.atTop (𝓝 (‖x‖⁻¹)) := by
  apply Filter.Tendsto.inv₀
  · exact normPowerSeries_tendsto x hx
  · simpa using hx

/-!

### A.3. The derivative of the norm power series

-/
open Space

lemma deriv_normPowerSeries {d} (n : ℕ) (x : Space d) (i : Fin d) :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [deriv_eq_fderiv_basis]
  rw [normPowerSeries_eq]
  rw [fderiv_sqrt]
  simp only [one_div, mul_inv_rev, fderiv_add_const, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rw [← deriv_eq_fderiv_basis]
  rw [deriv_norm_sq]
  ring
  · simp
    apply DifferentiableAt.norm_sq ℝ
    fun_prop
  · positivity

lemma fderiv_normPowerSeries {d} (n : ℕ) (x y : Space d) :
    fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x)⁻¹ := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries]
  ring

/-!

### A.4. Limits of the derivative of the power series

-/

lemma deriv_normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) (i : Fin d) :
    Filter.Tendsto (fun n => ∂[i] (normPowerSeries n) x) Filter.atTop (𝓝 (x i * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [deriv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

lemma fderiv_normPowerSeries_tendsto {d} (x y : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y)
      Filter.atTop (𝓝 (⟪y, x⟫_ℝ * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [fderiv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

/-!

### A.5. The power series is AEStronglyMeasurable

-/

@[fun_prop]
lemma normPowerSeries_aestronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries n : Space d → ℝ) volume := by
  rw [normPowerSeries_eq_rpow]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

/-!

### A.6. Bounds on the norm power series

-/

@[simp]
lemma normPowerSeries_nonneg {d} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp

@[simp]
lemma normPowerSeries_pos {d} (n : ℕ) (x : Space d) :
    0 < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp only [one_div, Real.sqrt_pos]
  positivity

@[simp]
lemma normPowerSeries_ne_zero {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≠ 0 := by
  rw [normPowerSeries_eq]
  simp only [one_div, ne_eq]
  positivity

lemma normPowerSeries_le_norm_sq_add_one {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  trans √(‖x‖ ^ 2 + 1)
  · rw [normPowerSeries_eq]
    apply Real.sqrt_le_sqrt
    simp only [one_div, add_le_add_iff_left]
    refine inv_le_one_iff₀.mpr ?_
    right
    simp
  · refine (Real.sqrt_le_left (by positivity)).mpr ?_
    trans (‖x‖ ^ 2 + 1) + (2 * ‖x‖)
    · simp
    · ring_nf
      rfl

@[simp]
lemma norm_lt_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.lt_sqrt_of_sq_lt
  simp only [one_div, lt_add_iff_pos_right, inv_pos]
  positivity

lemma norm_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
  positivity

lemma normPowerSeries_zpow_le_norm_sq_add_one {d} (n : ℕ) (m : ℤ) (x : Space d)
    (hx : x ≠ 0) :
    (normPowerSeries n x) ^ m ≤ (‖x‖ + 1) ^ m + ‖x‖ ^ m := by
  match m with
  | .ofNat m =>
    trans (‖x‖ + 1) ^ m
    · simp
      refine pow_le_pow_left₀ (by simp) ?_ m
      exact normPowerSeries_le_norm_sq_add_one n x
    · simp
  | .negSucc m =>
    trans (‖x‖ ^ (m + 1))⁻¹; swap
    · simp
      positivity
    simp only [zpow_negSucc]
    refine inv_anti₀ ?_ ?_
    · positivity
    refine pow_le_pow_left₀ (by simp) ?_ (m + 1)
    exact norm_le_normPowerSeries n x

/-!

### A.7. The `IsDistBounded` property of the norm power series

-/

@[fun_prop]
lemma IsDistBounded.normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x) ^ m) := by
  match m with
  | .ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    apply IsDistBounded.mono (f := fun (x : Space d) => (‖x‖ + 1) ^ m)
    · fun_prop
    · fun_prop
    intro x
    simp only [norm_pow, Real.norm_eq_abs]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [abs_of_nonneg (by simp),abs_of_nonneg (by positivity)]
    exact normPowerSeries_le_norm_sq_add_one n x
  | .negSucc m =>
    simp only [zpow_negSucc]
    apply IsDistBounded.mono (f := fun (x : Space d) => ((√(1/(n + 1)) : ℝ) ^ (m + 1))⁻¹)
    · fun_prop
    · rw [normPowerSeries_eq_rpow]
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine stronglyMeasurable_iff_measurable.mpr ?_
      fun_prop
    · intro x
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, one_div]
      refine inv_anti₀ (by positivity) ?_
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by simp)).mpr ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by simp)]
      rw [normPowerSeries_eq]
      simp only [Real.sqrt_inv, one_div]
      rw [← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_single {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)) := by
  convert IsDistBounded.normPowerSeries_zpow (n := n) (m := 1) using 1
  simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_inv {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)⁻¹) := by
  convert normPowerSeries_zpow (n := n) (-1) using 1
  simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_deriv {d : ℕ} (n : ℕ) (i : Fin d) :
    IsDistBounded (d := d) (fun x => ∂[i] (normPowerSeries n) x) := by
  conv =>
    enter [1, x];
    rw [deriv_normPowerSeries]
  fun_prop

@[fun_prop]
lemma IsDistBounded.normPowerSeries_fderiv {d : ℕ} (n : ℕ) (y : Space d) :
    IsDistBounded (d := d) (fun x => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y) := by
  conv =>
    enter [1, x];
    rw [fderiv_eq_sum_deriv]
  apply IsDistBounded.sum_fun
  fun_prop

@[fun_prop]
lemma IsDistBounded.normPowerSeries_log {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => Real.log (normPowerSeries n x)) := by
  apply IsDistBounded.mono (f := fun x => (normPowerSeries n x)⁻¹ + (normPowerSeries n x))
  · fun_prop
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp only [Real.norm_eq_abs]
    conv_rhs => rw [abs_of_nonneg (by
      apply add_nonneg
      · simp
      · simp)]
    have h1 := Real.neg_inv_le_log (x := (normPowerSeries n x)) (by simp)
    have h2 := Real.log_le_rpow_div (x := (normPowerSeries n x)) (by simp) (ε := 1) (by positivity)
    simp_all
    rw [abs_le']
    generalize Real.log ‖x‖ = r at *
    apply And.intro
    · apply h2.trans
      simp
    · rw [neg_le]
      apply le_trans _ h1
      simp

/-!

### A.8. Differentiability of functions

-/

@[fun_prop]
lemma differentiable_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x) ^ m) := by
  refine Differentiable.zpow ?_ ?_
  · fun_prop
  · left
    exact normPowerSeries_ne_zero n

@[fun_prop]
lemma differentiable_normPowerSeries_inv {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x)⁻¹) := by
  convert differentiable_normPowerSeries_zpow (n := n) (m := -1) using 1
  funext x
  simp

@[fun_prop]
lemma differentiable_log_normPowerSeries {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => Real.log (normPowerSeries n x)) := by
  refine Differentiable.log ?_ ?_
  · fun_prop
  · intro x
    exact normPowerSeries_ne_zero n x
/-!

### A.9. Derivatives of functions

-/

lemma deriv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => (normPowerSeries n x) ^ m) x =
      m * x i * (normPowerSeries n x) ^ (m - 2) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ ((fun x => x ^ m) ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, deriv_zpow',
    smul_eq_mul]
  rw [fderiv_normPowerSeries]
  simp only [basis_inner]
  field_simp
  ring_nf
  have h1 : normPowerSeries n x ^ (-1 + m) = normPowerSeries n x ^ ((-2 + m) + 1) := by
    ring_nf
  rw [h1, zpow_add₀]
  simp only [Int.reduceNeg, zpow_one]
  ring
  · simp
  · refine DifferentiableAt.zpow ?_ ?_
    · fun_prop
    · left
      exact normPowerSeries_ne_zero n x
  · fun_prop

lemma fderiv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x y : Space d) :
    fderiv ℝ (fun x : Space d => (normPowerSeries n x) ^ m) x y =
      m * ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (m - 2) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries_zpow]
  ring

lemma deriv_log_normPowerSeries {d : ℕ} {n : ℕ} (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => Real.log (normPowerSeries n x)) x =
      x i * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ (Real.log ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp,]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
    Real.deriv_log', smul_eq_mul, Int.reduceNeg, zpow_neg]
  rw [fderiv_normPowerSeries]
  simp [zpow_ofNat, sq]
  ring
  · apply DifferentiableAt.log ?_ ?_
    · fun_prop
    exact normPowerSeries_ne_zero n x
  · fun_prop

lemma fderiv_log_normPowerSeries {d : ℕ} {n : ℕ} (x y : Space d) :
    fderiv ℝ (fun x : Space d => Real.log (normPowerSeries n x)) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_log_normPowerSeries]
  ring

/-!

### A.10. Gradients of distributions

-/

lemma gradient_dist_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    distGrad (distOfFunction (fun x : Space d => (normPowerSeries n x) ^ m) (by fun_prop)) =
    distOfFunction (fun x : Space d => (m * (normPowerSeries n x) ^ (m - 2)) • x)
    (by fun_prop) := by
  ext1 η
  apply ext_inner_right ℝ
  intro y
  simp [distGrad_inner_eq]
  rw [Distribution.fderivD_apply, distOfFunction_apply, distOfFunction_inner]
  calc _
    _ = - ∫ (x : Space d), fderiv ℝ η x y * normPowerSeries n x ^ m := by
      rfl
    _ = ∫ (x : Space d), η x * fderiv ℝ (normPowerSeries n · ^ m) x y := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · fun_prop
      · refine IsDistBounded.integrable_space_mul ?_ η
        conv => enter [1, x]; rw [fderiv_normPowerSeries_zpow]
        simp [mul_assoc]
        fun_prop
      · fun_prop
      · exact η.differentiable
      · fun_prop
    _ = ∫ (x : Space d), η x * (m * ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (m - 2)) := by
      congr
      funext x
      rw [fderiv_normPowerSeries_zpow]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm]
  ring

lemma gradient_dist_normPowerSeries_log {d : ℕ} {n : ℕ} :
    distGrad (distOfFunction (fun x : Space d => Real.log (normPowerSeries n x)) (by fun_prop)) =
    distOfFunction (fun x : Space d => ((normPowerSeries n x) ^ (- 2 : ℤ)) • x)
    (by fun_prop) := by
  ext1 η
  apply ext_inner_right ℝ
  intro y
  simp [distGrad_inner_eq]
  rw [Distribution.fderivD_apply, distOfFunction_apply, distOfFunction_inner]
  calc _
    _ = - ∫ (x : Space d), fderiv ℝ η x y * Real.log (normPowerSeries n x) := by
      rfl
    _ = ∫ (x : Space d), η x * fderiv ℝ (fun x => Real.log (normPowerSeries n x)) x y := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · fun_prop
      · refine IsDistBounded.integrable_space_mul ?_ η
        conv => enter [1, x]; rw [fderiv_log_normPowerSeries]
        fun_prop
      · fun_prop
      · exact η.differentiable
      · fun_prop
    _ = ∫ (x : Space d), η x * (⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (- 2 : ℤ)) := by
      congr
      funext x
      rw [fderiv_log_normPowerSeries]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm]
  ring

lemma gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm {d : ℕ} (m : ℤ)
    (hm : - (d.succ - 1 : ℕ) ≤ m) (η : 𝓢(Space d.succ, ℝ))
    (y : EuclideanSpace ℝ (Fin d.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction
    (fun x : Space d.succ => (normPowerSeries n x) ^ m) (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distGrad (distOfFunction (fun x : Space d.succ => ‖x‖ ^ m)
    (IsDistBounded.pow m hm)) η, y⟫_ℝ)) := by
  simp [distGrad_inner_eq, Distribution.fderivD_apply, distOfFunction_apply]
  change Filter.Tendsto (fun n => - ∫ (x : Space d.succ), fderiv ℝ η x y * normPowerSeries n x ^ m)
    Filter.atTop (𝓝 (- ∫ (x : Space d.succ), fderiv ℝ η x y * ‖x‖ ^ m))
  apply Filter.Tendsto.neg
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |fderiv ℝ η x y| * ((‖x‖ + 1) ^ m + ‖x‖ ^ m))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_fderiv_schwartzMap_smul (F := ℝ) ?_
    fun_prop
  · have h1 : Integrable (fun x => (fderiv ℝ (⇑η) x) y * ((‖x‖ + 1) ^ m + ‖x‖ ^ m)) volume := by
      apply IsDistBounded.integrable_space_fderiv ?_
      apply IsDistBounded.add
      · refine IsDistBounded.norm_add_pos_nat_zpow m 1 ?_
        simp
      · exact IsDistBounded.pow m hm
    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp only [Nat.succ_eq_add_one, norm_mul, Real.norm_eq_abs, mul_eq_mul_left_iff, abs_eq_zero]
    left
    rw [abs_of_nonneg (by positivity)]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n m x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    have h1 : Filter.Tendsto (fun x_1 => normPowerSeries x_1 x ^ (m : ℝ))
      Filter.atTop (𝓝 (‖x‖ ^ (m : ℝ))) := by
      refine Filter.Tendsto.rpow ?_ ?_ ?_
      · apply normPowerSeries_tendsto x hx
      · simp
      · left
        simpa using hx
    simpa using h1

lemma gradient_dist_normPowerSeries_zpow_tendsTo {d : ℕ} (m : ℤ) (hm : - (d.succ - 1 : ℕ) + 2 ≤ m)
    (η : 𝓢(Space d.succ, ℝ)) (y : EuclideanSpace ℝ (Fin d.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction (fun x : Space d.succ => (normPowerSeries n x) ^ m)
    (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distOfFunction (fun x : Space d.succ => (m * ‖x‖ ^ (m - 2)) • x) (by
    simp [← smul_smul]
    refine IsDistBounded.const_fun_smul ?_ ↑m
    apply IsDistBounded.zpow_smul_self
    simp_all
    grind) η, y⟫_ℝ)) := by
  conv =>
    enter [1, n];
    rw [gradient_dist_normPowerSeries_zpow]
  simp [distOfFunction_inner]
  have h1 (n : ℕ) (x : Space d.succ) :
    η x * ⟪(↑m * normPowerSeries n x ^ (m - 2)) • x, y⟫_ℝ =
    η x * (m * (⟪x, y⟫_ℝ * (normPowerSeries n x) ^ (m - 2))) := by
    simp [inner_smul_left]
    ring_nf
    left
    trivial
  conv =>
    enter [1, n, 2, x];
    rw [h1 n x]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |η x| * |m| * |⟪x, y⟫_ℝ| * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2)))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_schwartzMap_smul (F := ℝ) ?_ η
    apply IsDistBounded.const_mul_fun
    apply IsDistBounded.isDistBounded_mul_inner'
    fun_prop
  · have h1 : Integrable (fun x =>
        η x * (m * (⟪x, y⟫_ℝ * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2))))) volume := by
      apply IsDistBounded.integrable_space_mul ?_ η
      apply IsDistBounded.const_mul_fun
      apply IsDistBounded.isDistBounded_mul_inner'
      apply IsDistBounded.add
      · refine IsDistBounded.norm_add_pos_nat_zpow (m - 2) 1 ?_
        simp
      · apply IsDistBounded.pow (m - 2)
        simp_all
        grind
    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp [mul_assoc]
    rw [abs_of_nonneg (by positivity)]
    simp only [true_or]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp [mul_assoc]
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n (m - 2) x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    simp [inner_smul_left, mul_assoc]
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    ring_nf
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    have h1 : Filter.Tendsto (fun x_1 => normPowerSeries x_1 x ^ ((m - 2 : ℤ) : ℝ))
      Filter.atTop (𝓝 (‖x‖ ^ ((m - 2 : ℤ) : ℝ))) := by
      refine Filter.Tendsto.rpow ?_ ?_ ?_
      · apply normPowerSeries_tendsto x hx
      · simp
      · left
        simpa using hx
    simp [-Int.cast_sub, Real.rpow_intCast] at h1
    convert h1 using 3
    · ring
    · ring
/-!

## B. Distributions involving norms

-/

lemma distGrad_distOfFunction_norm_zpow {d : ℕ} (m : ℤ) (hm : - (d.succ - 1 : ℕ) + 2 ≤ m) :
    distGrad (distOfFunction (fun x : Space d.succ => ‖x‖ ^ m)
      (IsDistBounded.pow m (by simp_all; omega)))
    = distOfFunction (fun x : Space d.succ => (m * ‖x‖ ^ (m - 2)) • x) (by
      simp [← smul_smul]
      refine IsDistBounded.const_fun_smul ?_ ↑m
      apply IsDistBounded.zpow_smul_self
      simp_all
      omega) := by
  ext1 η
  apply ext_inner_right ℝ
  intro y
  apply tendsto_nhds_unique
    (gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm m (by simp_all; omega) η y)
    (gradient_dist_normPowerSeries_zpow_tendsTo m hm η y)

end Space
