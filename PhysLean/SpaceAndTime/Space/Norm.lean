/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.IsDistBounded
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm
/-!

# Distributions from functions on space

## i. Overview

In this module we define distributions on space constructed from functions
`f : Space d → F` satisfying the condition `IsDistBounded f`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## ii. Key results

- `distOfFunction f hf` : The distribution on space constructed from the function
  `f : Space d → F` satisfying the `IsDistBounded f` condition.

## iii. Table of contents

- A. Definition of a distribution from a function
- B. Linarity properties of getting distributions from functions
- C. Properties related to inner products

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
def normPowerSeries {d}  : ℕ → Space d → ℝ := fun n x =>
  √(‖x‖ ^ 2 + 1/(n + 1))

lemma normPowerSeries_eq (n : ℕ) :
    normPowerSeries (d := d) n = fun x => √(‖x‖ ^ 2 + 1/(n + 1)) := rfl

lemma normPowerSeries_eq_rpow {d} (n : ℕ) :
    normPowerSeries (d := d) n = fun x => ((‖x‖ ^ 2 + 1/(n + 1))) ^ (1/2 : ℝ) := by
  rw [normPowerSeries_eq]
  funext x
  rw [← Real.sqrt_eq_rpow]

/-!

## A.1. Differentiability of the norm power series

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

## A.2. The limit of the norm power series

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

## A.3. The derivative of the norm power series

-/
open Space

lemma deriv_normPowerSeries {d} (n : ℕ) (x : Space d) (i : Fin d)  :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [deriv_eq_fderiv_basis]
  rw [normPowerSeries_eq]
  rw [fderiv_sqrt]
  simp
  rw [← deriv_eq_fderiv_basis]
  rw [deriv_norm_sq]
  ring
  · simp
    apply DifferentiableAt.norm_sq ℝ
    fun_prop
  · positivity

lemma fderiv_normPowerSeries {d} (n : ℕ) (x y : Space d) :
    fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x)⁻¹  := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries]
  ring

/-!

## A.4. Limits of the derivative of the power series

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

## A.5. The power series is AEStronglyMeasurable

-/

@[fun_prop]
lemma normPowerSeries_aestronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries n : Space d → ℝ) volume := by
  rw [normPowerSeries_eq_rpow]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

/-!

## A.6. Bounds on the norm power series

-/

@[simp]
lemma normPowerSeries_nonneg {d} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp

lemma normPowerSeries_le_norm_sq_add_one {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  trans √(‖x‖ ^ 2 + 1)
  · rw [normPowerSeries_eq]
    apply Real.sqrt_le_sqrt
    simp
    refine inv_le_one_iff₀.mpr ?_
    right
    simp
  · refine (Real.sqrt_le_left (by positivity)).mpr ?_
    trans (‖x‖ ^ 2 + 1) + (2 * ‖x‖)
    · simp
    · ring_nf
      rfl
/-!

## A.7. The `IsDistBounded` property of the norm power series

-/

@[fun_prop]
lemma IsDistBounded.normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x) ^ m) := by
  match m with
  | .ofNat m =>
    simp
    apply IsDistBounded.mono (f := fun (x : Space d) => (‖x‖ + 1) ^ m)
    · fun_prop
    · fun_prop
    intro x
    simp
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [abs_of_nonneg (by simp),abs_of_nonneg (by positivity)]
    exact normPowerSeries_le_norm_sq_add_one n x
  | .negSucc m =>
    simp
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
      simp
      rw [← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_inv {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)⁻¹) := by
  convert normPowerSeries_zpow (n := n) (-1) using 1
  simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_deriv {d : ℕ} (n : ℕ) (i : Fin d):
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

end Space
