/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
import PhysLean.Mathematics.Distribution.Function.IsDistBounded
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
namespace Space

/-!

## The logarithmic distribution

-/
open Distribution SchwartzMap
open Space  MeasureTheory Real InnerProductSpace
open InnerProductSpace

open scoped Topology BigOperators FourierTransform

namespace Dist
/-!

## Norm power series
-/

noncomputable def normPowerSeries {d : ℕ} (n : ℕ) (x : Space d) : ℝ :=
  √(‖x‖ ^ 2 + 1 / (n + 1))

lemma normPowerSeries_eq {d : ℕ}:
    normPowerSeries = fun (n : ℕ) (x : Space d) =>  √(‖x‖ ^ 2 + 1 / (n + 1)) := by rfl

lemma normPowerSeries_eq_rpow {d : ℕ} :
    normPowerSeries = fun (n : ℕ) (x : Space d) => (‖x‖ ^ 2 + 1 / (n + 1)) ^ (1 / 2 : ℝ) := by
  rw [normPowerSeries_eq]
  ext n x
  simp
  rw [Real.sqrt_eq_rpow]
  simp

lemma normPowerSeries_neq_zero {d : ℕ} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≠ 0 := by
  rw [normPowerSeries_eq]
  positivity

@[simp]
lemma normPowerSeries_pos {d : ℕ} (n : ℕ) (x : Space d) :
    0 < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  positivity

@[simp]
lemma normPowerSeries_nonneg {d : ℕ} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  positivity

lemma normPowerSeries_tendsto {d : ℕ} (x : Space d) :
    Filter.Tendsto (normPowerSeries  · x) Filter.atTop (𝓝 (‖x‖)) := by
  rw [normPowerSeries_eq_rpow]
  have h1 : ‖x‖ = (‖x‖ ^ 2 + 0) ^ (1/2 : ℝ) := by
    simp only [add_zero]
    trans  (‖x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ); swap
    · simp
    rw [← Real.rpow_mul]
    simp
    exact norm_nonneg x
  rw [h1]
  refine Filter.Tendsto.rpow ?_ tendsto_const_nhds ?_
  · apply Filter.Tendsto.add
    · exact tendsto_const_nhds
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  simp

@[fun_prop]
lemma normPowerSeries_differentiable {d : ℕ} (n : ℕ) :
    Differentiable ℝ (normPowerSeries n : Space d → ℝ) := by
  rw [normPowerSeries_eq_rpow]
  refine Differentiable.rpow_const ?_ ?_
  · fun_prop
  · intro x
    left
    positivity

@[fun_prop]
lemma normPowerSeries_contDiff {d : ℕ} (n : ℕ) (k : WithTop ℕ∞)  :
    ContDiff ℝ k (normPowerSeries n : Space d → ℝ) := by
  rw [normPowerSeries_eq_rpow]
  simp
  apply ContDiff.rpow
  · apply ContDiff.add
    · apply contDiff_norm_sq (𝕜 := ℝ)
    · fun_prop
  · fun_prop
  intro x
  positivity

lemma norm_le_normPowerSeries {d : ℕ} (n : ℕ) (x : Space d) :
    ‖x‖ ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp
  refine (le_sqrt ?_ ?_).mpr ?_
  · positivity
  · positivity
  · simp
    positivity

lemma normPowerSeries_aeStronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries (d := d) n) := by
  rw [normPowerSeries_eq]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

/-!

## A.1. The power series of the derivative of the norm

-/
open Space

lemma deriv_normPowerSeries_eq {d : ℕ} (n : ℕ) (i : Fin d) (x : Space d) :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [normPowerSeries_eq]
  rw [deriv_eq]
  rw [fderiv_sqrt]
  simp
  rw [← deriv_eq]
  rw [deriv_norm_sq]
  ring
  · apply Differentiable.differentiableAt
    fun_prop
  · positivity

lemma deriv_normPowerSeries_tendsTo {d : ℕ}  (i : Fin d) (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => ∂[i] (normPowerSeries n) x) Filter.atTop (𝓝 (x i * ‖x‖⁻¹)) := by
  conv =>
    enter [1, n]
    rw [deriv_normPowerSeries_eq]
  apply Filter.Tendsto.mul
  · exact tendsto_const_nhds
  · suffices h1 : Filter.Tendsto (fun x_1 => (normPowerSeries x_1 x)^ (-1 : ℝ))
        Filter.atTop (𝓝 (‖x‖^ (-1 : ℝ))) by simpa [Real.rpow_neg] using h1
    refine Filter.Tendsto.rpow ?_ tendsto_const_nhds ?_
    exact normPowerSeries_tendsto x
    left
    simpa using hx


/-!

### A.2. Integrals with Schwartz functions

-/


lemma normPowerSeries_le_norm_add_one {d : ℕ} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  rw [normPowerSeries_eq]
  simp
  refine sqrt_le_iff.mpr (And.intro (by positivity) ?_)
  trans ‖x‖ ^ 2 + 1
  · simp
    refine inv_le_one_iff₀.mpr ?_
    right
    simp
  trans ‖x‖ ^ 2 + 2 * ‖x‖ + 1
  · simp
  apply le_of_eq
  ring

lemma normPowerSeries_pow_le_norm_add_one_pow {d : ℕ} (n : ℕ) (x : Space d) (m : ℕ) :
    (normPowerSeries n x) ^ m ≤ (‖x‖ + 1) ^ m := by
  refine pow_le_pow_left₀ (by simp) ?_ m
  exact normPowerSeries_le_norm_add_one n x


lemma normPowerSeries_isDistBounded_pow  {d : ℕ} (n : ℕ) (m : ℕ)   :
    IsDistBounded (dm1 := d) (fun x => (normPowerSeries n x) ^ m) := by

  sorry
lemma comp_normPowerSeries_isDistBounded_of_comp_norm {d : ℕ}  (f : ℝ → ℝ) (n : ℕ)
    (hf :  IsDistBounded (dm1 := d) (fun x => f ‖x‖)) :
    IsDistBounded (dm1 := d) (fun x => f (normPowerSeries n x)) := by
  obtain ⟨m, c, g, p, c_pos, h2, h3⟩ := hf
  use m, c, g, p
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · intro x
    simp
    sorry


lemma integral_fun_normPowerSeries_mul_deriv_schwartzmap {d : ℕ} (η : 𝓢(Space d, ℝ))
    (f  : ℝ → ℝ) (f' : ℝ → ℝ →L[ℝ] ℝ) (n : ℕ) (i : Fin d)
    (hf : ∀ x, x ≠ 0 → HasFDerivAt (𝕜 := ℝ) f (f' x) x):
    ∫ (x : Space d), f (normPowerSeries n x) * ∂[i] η x =
    - ∫ (x : Space d), f' (normPowerSeries n x) 1 * η x  := by

  sorry
open MeasureTheory Measure
lemma normPowerSeries_integral_tendsTo {d : ℕ} (η : 𝓢(Space d, ℝ))
    (f : ℝ → ℝ) :
    Filter.Tendsto (fun n => ∫ (x : Space d), f (normPowerSeries n x) * η x)
      Filter.atTop (𝓝 (∫ (x : Space d), f ‖x‖ * η x)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
  · intro n
    refine Continuous.comp_aestronglyMeasurable₂ ?_ ?_ ?_
    · fun_prop
    · sorry
    · fun_prop

  · sorry
  · sorry
  · sorry

/-!

## The logarithmic distribution
-/
noncomputable def log {d : ℕ} : (Space d.succ.succ) →d[ℝ] ℝ :=
  Distribution.ofFunction
    (fun x : Space d.succ.succ => Real.log ‖x‖)
    (by apply IsDistBounded.log)
    (AEMeasurable.aestronglyMeasurable <| by fun_prop)

lemma log_apply {d : ℕ} (η : 𝓢(Space d.succ.succ, ℝ)) :
    Dist.log η = ∫ (x : Space d.succ.succ), (Real.log ‖x‖) * η x := by
  simp [Dist.log, Distribution.ofFunction_apply]
  congr
  funext x
  ring


noncomputable def logPowerSeries  {d : ℕ} (n : ℕ) (x : Space d.succ.succ ) : ℝ :=
  Real.log (‖x‖ + 1 / (n + 1))

lemma logPowerSeries_eq {d : ℕ}:
    logPowerSeries = fun (n : ℕ) (x : Space d.succ.succ) =>  Real.log (‖x‖ + 1 / (n + 1)) := by rfl
open Filter

lemma logPowerSeries_tendsto {d : ℕ} (x : Space d.succ.succ) (hx : x ≠ 0) :
   Filter.Tendsto (logPowerSeries  · x) atTop (𝓝 (Real.log ‖x‖)) := by
  simp only [logPowerSeries]
  apply Filter.Tendsto.log
  suffices h : Tendsto (fun (n : ℕ) => ‖x‖ + 1 / (n + 1)) atTop (𝓝 (‖x‖ + 0)) by
    simpa using h
  apply Filter.Tendsto.add
  · exact tendsto_const_nhds
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using hx

lemma logPowerSeries_differentiable {d : ℕ} (n : ℕ) :
    Differentiable ℝ (logPowerSeries n : Space d.succ.succ → ℝ) := by
 rw [logPowerSeries_eq]
 apply Differentiable.log
 · simp
   apply Differentiable.norm (𝕜 := ℝ)
   fun_prop

lemma Dist.log_distDeriv {d : ℕ} (I : ℝ) (μ : Fin d.succ.succ)
    (η : 𝓢(Space d.succ.succ, ℝ)) :
    distDeriv μ Dist.log η = ∫ (x : Space d.succ.succ), (x μ / ‖x‖ ^ 2) * η x := by
  rw [distDeriv_apply, fderivD_apply, log_apply]
  change - ∫ (x : Space d.succ.succ), Real.log ‖x‖ * fderiv ℝ η x (basis μ) = _

  sorry

end Dist

end Space
