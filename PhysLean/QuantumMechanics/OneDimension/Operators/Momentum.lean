/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Meta.TODO.Basic
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
  simp
  fun_prop
  fun_prop

lemma momentumOperator_add {ψ1 ψ2 : ℝ → ℂ}
    (hψ1 : Differentiable ℝ ψ1) (hψ2 : Differentiable ℝ ψ2) :
    momentumOperator (ψ1 + ψ2) = momentumOperator ψ1 + momentumOperator ψ2 := by
  rw [momentumOperator_eq_smul, momentumOperator_eq_smul, momentumOperator_eq_smul]
  funext x
  simp only [neg_mul, Pi.add_apply]
  rw [deriv_add (hψ1 x) (hψ2 x)]
  simp
  ring

/-!

## The momentum operator on Schwartz maps

-/

/-- The unbounded momentum operator, whose domain is square integrable functions
  which are differentiable and which have a square integrable derivative. -/
def momentumOperatorSchwartz : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := schwartzSubmodule
  toFun := {
    toFun ψ := ((- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ
      (schwartzSubmoduleEquiv ψ)).toLp 2 MeasureTheory.volume
    map_add' ψ1 ψ2 := by
      simp
      rfl
    map_smul' a ψ := by
      simp
      rw [smul_comm]
      change _ = (a • -((Complex.I * ↑↑ℏ) •
        (SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ))).toLp 2 MeasureTheory.volume
      simp}

lemma momentumOperatorSchwartz_apply (ψ : schwartzSubmodule) :
    momentumOperatorSchwartz ψ =
      ((- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ
      (schwartzSubmoduleEquiv ψ)).toLp 2 MeasureTheory.volume := by rfl

lemma momentumOperatorSchwartz_mem_schwartzSubmodule (ψ : schwartzSubmodule) :
    momentumOperatorSchwartz ψ ∈ schwartzSubmodule := by
  rw [momentumOperatorSchwartz_apply]
  use (- Complex.I * ℏ) • SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ)
  simp

lemma schwartzSubmoduleEquiv_momentumOperatorSchwartz (ψ : schwartzSubmodule) :
    schwartzSubmoduleEquiv ⟨momentumOperatorSchwartz ψ,
      momentumOperatorSchwartz_mem_schwartzSubmodule ψ⟩ =
      (- Complex.I * ℏ) • (SchwartzMap.derivCLM ℂ (schwartzSubmoduleEquiv ψ)) := by
  change schwartzSubmoduleEquiv (schwartzSubmoduleEquiv.symm _) = _
  simp

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma planeWaveFunctional_generalized_eigenvector_momentumOperatorSchwartz
    (k : ℝ) (ψ : schwartzSubmodule) :
    planewaveFunctional k ⟨momentumOperatorSchwartz ψ,
      momentumOperatorSchwartz_mem_schwartzSubmodule ψ⟩ =
    (2 * Real.pi * ℏ * k) • (planewaveFunctional k ψ) := by
  conv_lhs =>
    rw [planewaveFunctional]
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe, Function.comp_apply]
    rw [schwartzSubmoduleEquiv_momentumOperatorSchwartz]
    simp only [neg_mul, neg_smul, map_neg, map_smul]
    change (-((Complex.I * ↑↑ℏ) •
      (SchwartzMap.fourierTransformCLM ℂ) ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ)) k))
    simp
    erw [Real.fourierIntegral_deriv (SchwartzMap.integrable (schwartzSubmoduleEquiv ψ))
      (SchwartzMap.differentiable (schwartzSubmoduleEquiv ψ))
      (SchwartzMap.integrable ((SchwartzMap.derivCLM ℂ) (schwartzSubmoduleEquiv ψ)))]
  simp [planewaveFunctional]
  ring_nf
  simp

end
end OneDimension
end QuantumMechanics
