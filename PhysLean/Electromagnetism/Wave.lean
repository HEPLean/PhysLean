/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Homogeneous
import PhysLean.ClassicalMechanics.WaveEquation.Basic
/-!
# Electromagnetism wave equation

The electromagnetic wave eqaution as a consequence of the charge and current free
Maxwell's Equations in homogeneous isotropic medium.

-/

namespace Electromagnetism

open Space
open Time
open ClassicalMechanics

variable (OM : OpticalMedium)

local notation "ε" => OM.ε
local notation "μ" => OM.μ

/-- The electromagnetic wave equation for electric field. -/
theorem waveEquation_electricField_of_freeMaxwellEquations
    (E : ElectricField) (B : MagneticField) (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation E t x (Real.sqrt (μ • ε)⁻¹) := by
  rw [WaveEquation]
  rw [Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    simp only [smul_eq_mul, mul_inv_rev, ← smul_assoc, mul_assoc, ne_eq, OM.mu_ge_zero, ne_of_gt,
      not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => E t x) t) t =
      ∂ₜ (fun t => (μ • ε)⁻¹ • (∇ × B t) x) t := by
    congr
    funext t
    rw [hdt]
  rw [hdt2]
  have hd0 : (∇ ⬝ (E t)) = 0 := by
    ext x
    simp only [Pi.zero_apply]
    rw [OM.gaussLawElectric_of_free E B]
    exact h
  have hlpE : Δ (E t) = - ((fun x => ∇ (∇ ⬝ (E t)) - Δ (E t)) x) := by
    simp only [hd0, grad_zero, zero_sub, neg_neg]
  rw [hlpE]
  rw [← curl_of_curl]
  have hcE : curl (E t) = fun x => - ∂ₜ (fun t => B t x) t := by
    funext x
    rw [OM.faradayLaw_of_free E B]
    exact h
  rw [hcE]
  have hcn : curl (fun x => -∂ₜ (fun t => B t x) t) =
      - curl (fun x => ∂ₜ (fun t => B t x) t) := by
    trans - (1:ℝ) • curl (fun x => ∂ₜ (fun t => B t x) t)
    rw [← curl_smul]
    simp only [neg_smul, one_smul]
    rfl
    · unfold Time.deriv
      intro x
      apply fderiv_curry_differentiableAt_fst_comp_snd (hf := hB)
    simp
  rw [hcn]
  simp only [smul_eq_mul, mul_inv_rev, Pi.neg_apply, neg_neg]
  rw [← time_deriv_curl_commute]
  have hdt_smul : ∂ₜ (fun t => (OM.ε⁻¹ * OM.μ⁻¹) • curl (B t) x) t =
      (OM.ε⁻¹ * OM.μ⁻¹) • ∂ₜ (fun t => curl (B t) x) t := by
    rw [deriv_smul]
    · unfold curl Space.deriv coord basis
      simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
        EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      apply differentiable_pi''
      intro i t
      fin_cases i <;>
      · simp only [Fin.isValue]
        apply DifferentiableAt.sub
        repeat
          apply differentiableAt_fderiv_coord_single
          exact hB
  rw [hdt_smul]
  rw [sub_self]
  exact hB
  exact hE.uncurry (x := t)
  rw [inv_nonneg]
  exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)

/-- The electromagnetic wave equation for magnetic field. -/
theorem waveEquation_magneticField_of_freeMaxwellEquations
    (E : ElectricField) (B : MagneticField) (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation B t x (Real.sqrt (μ • ε)⁻¹) := by
  rw [WaveEquation]
  rw [Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => B t x) t) = - (∇ × E t) x := by
    intro t
    rw [OM.faradayLaw_of_free E B]
    simp only [neg_neg]
    exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => B t x) t) t =
      - ∂ₜ (fun t => (∇ × E t) x) t := by
    trans - (1:ℝ) • ∂ₜ (fun t => (∇ × E t) x) t
    rw [← deriv_smul]
    simp only [neg_smul, one_smul]
    congr
    funext t
    rw [hdt]
    · unfold curl Space.deriv coord basis
      simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
        EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      apply differentiable_pi''
      intro i t
      fin_cases i <;>
      · simp only [Fin.isValue]
        apply DifferentiableAt.sub
        repeat
          apply differentiableAt_fderiv_coord_single
          exact hE
    simp only [neg_smul, one_smul]
  rw [hdt2]
  have hd0 : (∇ ⬝ (B t)) = 0 := by
    ext x
    simp only [Pi.zero_apply]
    rw [OM.gaussLawMagnetic_of_free E B]
    exact h
  have hlpB : Δ (B t) = - ((fun x => ∇ (∇ ⬝ (B t)) - Δ (B t)) x) := by
    simp only [hd0, grad_zero, zero_sub, neg_neg]
  rw [hlpB]
  rw [← curl_of_curl]
  have hcB : curl (B t) = OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t := by
    funext x
    rw [OM.ampereLaw_of_free E B]
    rfl
    exact h
  rw [hcB]
  have hcn : (OM.μ • OM.ε)⁻¹ • (-(fun x =>
      curl (OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t)) x) x =
      - curl (fun x => ∂ₜ (fun t => E t x) t) x := by
    simp only [smul_eq_mul, mul_inv_rev, Pi.neg_apply, smul_neg, neg_inj]
    change ((OM.ε⁻¹ * OM.μ⁻¹) • (curl (OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t))) x = _
    rw [← curl_smul]
    simp only [← smul_assoc, smul_eq_mul, mul_assoc, ne_eq, OM.mu_ge_zero, ne_of_gt,
      not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    · unfold Time.deriv
      rw [← smul_assoc]
      change Differentiable ℝ (fun x => (OM.μ • OM.ε) • (fderiv ℝ (fun t => E t x) t) 1)
      apply Differentiable.const_smul
      apply fderiv_curry_differentiableAt_fst_comp_snd (hf := hE)
  rw [time_deriv_curl_commute]
  rw [hcn]
  rw [sub_self]
  exact hE
  exact hB.uncurry (x := t)
  rw [inv_nonneg]
  exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)
