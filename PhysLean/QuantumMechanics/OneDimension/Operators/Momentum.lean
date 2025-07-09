/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Meta.TODO.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
/-!

# Momentum operator

In this module we define:
- The momentum operator on functions `ℝ → ℂ`
- The momentum operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that plane waves are generalized eigenvectors of the momentum operator.

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace

/-!

## The momentum operator on functions `ℝ → ℂ`

-/

/-- The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `- i ℏ ψ'`. -/
def momentumOperator (ψ : ℝ → ℂ) : ℝ → ℂ := fun x ↦ - Complex.I * ℏ * deriv ψ x

lemma momentumOperator_eq_smul (ψ : ℝ → ℂ) :
    momentumOperator ψ = fun x => (- Complex.I * ℏ) • deriv ψ x := by
  rfl

@[fun_prop]
lemma continuous_momentumOperator (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (momentumOperator ψ) := by
  rw [momentumOperator_eq_smul]
  fun_prop

lemma momentumOperator_smul {ψ : ℝ → ℂ} (hψ : Differentiable ℝ ψ) (c : ℂ) :
    momentumOperator (c • ψ) = c • momentumOperator ψ := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [neg_mul, Pi.smul_apply, mul_neg, neg_inj]
  rw [smul_comm]
  congr
  erw [deriv_smul]
  simp only [smul_eq_mul, deriv_const', zero_mul, add_zero]
  fun_prop
  fun_prop

lemma momentumOperator_add {ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : Differentiable ℝ ψ1) (hψ2 : Differentiable ℝ ψ2) :
    momentumOperator (ψ1 + ψ2) = momentumOperator ψ1 + momentumOperator ψ2 := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [neg_mul, Pi.add_apply]
  rw [deriv_add (hψ1 x) (hψ2 x)]
  simp only [smul_eq_mul, neg_mul]
  ring

/-!

## The momentum operator on Schwartz maps

-/

TODO "G4FTD" "Update the definition of `momentumOperatorSchwartz` to
  be a continuous linear map."

/-- The momentum operator on the Schwartz submodule is defined as the linear map from
  `schwartzSubmodule` to itself, such that `ψ` is taken to `fun x => - I ℏ ψ' (x)`. -/
def momentumOperatorSchwartz : Φ →ₗ[ℂ] Φ where
  toFun ψ := schwartzSubmoduleEquiv.symm <|
    (- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ)
  map_add' ψ1 ψ2 := by
    simp only [neg_mul, map_add, smul_add, neg_smul]
  map_smul' a ψ := by
    simp only [neg_mul, map_smul, neg_smul, RingHom.id_apply]
    rw [smul_comm]
    simp

lemma schwartzSubmoduleEquiv_momentumOperatorSchwartz (ψ : schwartzSubmodule) :
    schwartzSubmoduleEquiv (momentumOperatorSchwartz ψ) =
      (- Complex.I * ℏ) • (SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ)) := by
  change schwartzSubmoduleEquiv (schwartzSubmoduleEquiv.symm _) = _
  simp [momentumOperatorSchwartz]

lemma schwartzSubmoduleEquiv_momentumOperatorSchwartz_apply (ψ : schwartzSubmodule)
    (x : ℝ) :
    schwartzSubmoduleEquiv (momentumOperatorSchwartz ψ) x =
      (- Complex.I * ℏ) * (deriv (schwartzSubmoduleEquiv ψ) x) := by
  rw [schwartzSubmoduleEquiv_momentumOperatorSchwartz]
  rfl

/-- The unbounded momentum operator, whose domain is Schwartz maps. -/
def momentumOperatorUnbounded : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := schwartzSubmodule
  toFun := SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume ∘ₗ
    schwartzSubmoduleEquiv.toLinearMap ∘ₗ momentumOperatorSchwartz

lemma momentumOperatorUnbounded_apply (ψ : schwartzSubmodule) :
    momentumOperatorUnbounded ψ =
      ((- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ
      (schwartzSubmoduleEquiv ψ)).toLp 2 MeasureTheory.volume := by
  simp [momentumOperatorUnbounded, momentumOperatorSchwartz]

lemma momentumOperatorUnbounded_mem_schwartzSubmodule (ψ : schwartzSubmodule) :
    momentumOperatorUnbounded ψ ∈ schwartzSubmodule := by
  rw [momentumOperatorUnbounded_apply]
  use (- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ)
  simp

lemma momentumOperatorSchwartz_apply_eq_momentumOperatorUnbounded (ψ : schwartzSubmodule) :
    momentumOperatorSchwartz ψ = ⟨momentumOperatorUnbounded ψ,
      momentumOperatorUnbounded_mem_schwartzSubmodule ψ⟩ := by
  ext1
  change _ = (schwartzSubmoduleEquiv.symm (schwartzSubmoduleEquiv (momentumOperatorSchwartz ψ))).1
  simp

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma planeWaveFunctional_generalized_eigenvector_momentumOperatorSchwartz
    (k : ℝ) (ψ : schwartzSubmodule) :
    planewaveFunctional k (momentumOperatorSchwartz ψ) =
    (2 * Real.pi * ℏ * k) • (planewaveFunctional k ψ) := by
  conv_lhs =>
    rw [planewaveFunctional]
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe, Function.comp_apply]
    rw [schwartzSubmoduleEquiv_momentumOperatorSchwartz]
    simp only [neg_mul, neg_smul, map_neg, map_smul]
    change (-((Complex.I * ↑↑ℏ) •
      (SchwartzMap.fourierTransformCLM ℂ) ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ)) k))
    simp only [SchwartzMap.fourierTransformCLM_apply, smul_eq_mul]
    erw [Real.fourierIntegral_deriv (SchwartzMap.integrable (schwartzSubmoduleEquiv ψ))
      (SchwartzMap.differentiable (schwartzSubmoduleEquiv ψ))
      (SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ)))]
  simp [planewaveFunctional]
  ring_nf
  simp

open InnerProductSpace
lemma momentumOperatorSchwartz_hermitian (ψ1 ψ2 : schwartzSubmodule) :
    ⟪momentumOperatorSchwartz ψ1, ψ2⟫_ℂ = ⟪ψ1, momentumOperatorSchwartz ψ2⟫_ℂ := by
  rw [inner_schwartzSubmodule, inner_schwartzSubmodule]
  conv_rhs =>
    rw [schwartzSubmoduleEquiv_momentumOperatorSchwartz]
    change ∫ (x : ℝ), (starRingEnd ℂ) ((schwartzSubmoduleEquiv ψ1) x) *
      ((-Complex.I * ↑↑ℏ) * (SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ2) x)
    enter [2, x]
    rw [← mul_assoc]
    rw [mul_comm _ (-Complex.I * ↑↑ℏ)]
    rw [mul_assoc]
    simp only [SchwartzMap.derivCLM_apply]
    rw [← fderiv_deriv]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  conv_rhs =>
    rw [← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  congr
  funext x
  conv_rhs =>
    enter [2, 1, 1]
    change (fderiv ℝ (fun a => star ((schwartzSubmoduleEquiv ψ1) a)) x) 1
    rw [fderiv_star]
  simp [schwartzSubmoduleEquiv_momentumOperatorSchwartz_apply]
  ring
  · apply MeasureTheory.Integrable.mul_of_top_left
    · conv =>
        enter [1, x]
        change (fderiv ℝ (fun a => star ((schwartzSubmoduleEquiv ψ1) a)) x) 1
        rw [fderiv_star]
        change (starL' ℝ) (SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ1) x)
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ1))
    · exact SchwartzMap.memLp_top (schwartzSubmoduleEquiv ψ2) MeasureTheory.volume
  · apply MeasureTheory.Integrable.mul_of_top_left
    · change MeasureTheory.Integrable
        (fun x => (starL' ℝ : ℂ ≃L[ℝ] ℂ) ((schwartzSubmoduleEquiv ψ1) x)) MeasureTheory.volume
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable (schwartzSubmoduleEquiv ψ1)
    · change MeasureTheory.MemLp
        (fun x => SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ2) x) ⊤ MeasureTheory.volume
      exact SchwartzMap.memLp_top ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ2))
          MeasureTheory.volume
  · apply MeasureTheory.Integrable.mul_of_top_left
    · change MeasureTheory.Integrable
        (fun x => (starL' ℝ : ℂ ≃L[ℝ] ℂ) ((schwartzSubmoduleEquiv ψ1) x)) MeasureTheory.volume
      rw [ContinuousLinearEquiv.integrable_comp_iff]
      exact SchwartzMap.integrable (schwartzSubmoduleEquiv ψ1)
    · exact SchwartzMap.memLp_top (schwartzSubmoduleEquiv ψ2) MeasureTheory.volume
  · apply Differentiable.star
    exact SchwartzMap.differentiable (schwartzSubmoduleEquiv ψ1)
  · exact SchwartzMap.differentiable (schwartzSubmoduleEquiv ψ2)
end
end OneDimension
end QuantumMechanics
