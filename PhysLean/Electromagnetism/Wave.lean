/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Homogeneous
import PhysLean.ClassicalMechanics.WaveEquation.Basic
import PhysLean.ClassicalMechanics.Space.VectorIdentities
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
    WaveEquation E t x ((√(μ • ε))⁻¹) := by
  rw [WaveEquation, ← Real.sqrt_inv, Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    · simp [← smul_assoc, mul_assoc, OM.mu_ge_zero, ne_of_gt, OM.eps_ge_zero, h]
    · exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => E t x) t) t =
      ∂ₜ (fun t => (μ • ε)⁻¹ • (∇ × B t) x) t := by aesop
  rw [hdt2]
  have hd0 : (∇ ⬝ (E t)) = 0 := by
    ext x
    simp [OM.gaussLawElectric_of_free E B, h]
  have hlpE : Δ (E t) = - ((fun x => ∇ (∇ ⬝ (E t)) - Δ (E t)) x) := by simp [hd0]
  rw [hlpE, ← curl_of_curl]
  have hcE : curl (E t) = fun x => - ∂ₜ (fun t => B t x) t := by
    funext x
    simp [OM.faradayLaw_of_free E B, h]
  rw [hcE]
  have hcn : curl (fun x => -∂ₜ (fun t => B t x) t) =
      - curl (fun x => ∂ₜ (fun t => B t x) t) := by
    trans - (1:ℝ) • curl (fun x => ∂ₜ (fun t => B t x) t)
    rw [← curl_smul, neg_smul, one_smul]
    rfl
    · exact fun x ↦ fderiv_curry_differentiableAt_fst_comp_snd (hf := hB) ..
    · exact neg_one_smul ..
  simp only [smul_eq_mul, mul_inv_rev, hcn, Pi.neg_apply, neg_neg]
  rw [← time_deriv_curl_commute]
  have hdt_smul : ∂ₜ (fun t => (OM.ε⁻¹ * OM.μ⁻¹) • curl (B t) x) t =
      (OM.ε⁻¹ * OM.μ⁻¹) • ∂ₜ (fun t => curl (B t) x) t := by
    rw [deriv_smul]
    unfold curl Space.deriv coord basis
    simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
      EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply differentiable_pi''
    intro i
    fin_cases i <;> fun_prop
  rw [hdt_smul, sub_self]
  · exact hB
  · exact hE.uncurry ..
  · rw [inv_nonneg]
    exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)

/-- The electromagnetic wave equation for magnetic field. -/
theorem waveEquation_magneticField_of_freeMaxwellEquations
    (E : ElectricField) (B : MagneticField) (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation B t x ((√(μ • ε))⁻¹) := by
  rw [WaveEquation, ← Real.sqrt_inv, Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => B t x) t) = - (∇ × E t) x := by
    intro t
    rwa [OM.faradayLaw_of_free E B, neg_neg]
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
      intro i
      fin_cases i <;> fun_prop
    simp
  rw [hdt2]
  have hd0 : (∇ ⬝ (B t)) = 0 := by
    ext x
    simp [Pi.zero_apply, OM.gaussLawMagnetic_of_free E B, h]
  have hlpB : Δ (B t) = - ((fun x => ∇ (∇ ⬝ (B t)) - Δ (B t)) x) := by simp [hd0]
  rw [hlpB, ← curl_of_curl]
  have hcB : curl (B t) = OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t := by
    funext x
    rw [OM.ampereLaw_of_free E B]
    · rfl
    · exact h
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
      fun_prop
  rw [time_deriv_curl_commute, hcn, sub_self]
  · exact hE
  · exact hB.uncurry (x := t)
  · rw [inv_nonneg]
    exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)

/-- An electric plane wave travelling in the direction of `s` with propagation speed `c`. -/
@[nolint unusedArguments]
noncomputable def electricPlaneWave (E₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Space) (hs : inner ℝ s s = (1:ℝ)) : ElectricField :=
    planeWave E₀ c s hs

/-- A magnetic plane wave travelling in the direction of `s` with propagation speed `c`. -/
@[nolint unusedArguments]
noncomputable def magneticPlaneWave (B₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Space) (hs : inner ℝ s s = (1:ℝ)) : MagneticField :=
    planeWave B₀ c s hs

/-- An electric plane wave minus a constant field is transverse for all x. -/
lemma transverse_upto_time_fun_of_eq_electricPlaneWave {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Space} {hs : inner ℝ s s = 1} {E : ElectricField}
    {B : MagneticField} (hEwave : E = electricPlaneWave E₀ c s hs)
    (h' : Differentiable ℝ E₀) (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : Time → EuclideanSpace ℝ (Fin 3)), ∀ t x, inner ℝ (E t x - c t) s = 0 := by
  have E'eqdivE : ∀ t x y, inner ℝ (fderiv ℝ (E t) x y) s = inner ℝ y s * (∇ ⬝ (E t)) x := by
    intro t x y
    rw [hEwave, electricPlaneWave]
    unfold planeWave div coord basis Space.deriv
    rw [PiLp.inner_apply]
    simp [-PiLp.inner_apply]
    conv_lhs =>
      enter [2, i]
      rw [wave_fderiv_inner_eq_inner_fderiv_proj h']
    rw [← Finset.mul_sum]
    simp
  have E'eqzero : ∀ t x, fderiv ℝ (fun x => (inner ℝ (E t x) s)) x = 0 := by
    intro t x
    ext y
    rw [fderiv_inner_apply]
    simp [-PiLp.inner_apply]
    rw [E'eqdivE]
    rw [OM.gaussLawElectric_of_free E B]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_zero]
    exact hm
    rw [hEwave, electricPlaneWave]
    unfold planeWave
    apply Differentiable.comp
    fun_prop
    exact fun x => wave_differentiable
    fun_prop
  use fun t => E t 0
  intro t x
  have hx' := E'eqzero t
  apply is_const_of_fderiv_eq_zero at hx'
  rw [inner_sub_left, hx' x 0]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sub_self]
  apply Differentiable.inner
  rw [hEwave, electricPlaneWave]
  unfold planeWave
  apply Differentiable.comp
  fun_prop
  exact fun x => wave_differentiable
  fun_prop

/-- An magnetic plane wave minus a constant field is transverse for all x. -/
lemma transverse_upto_time_fun_of_eq_magneticPlaneWave {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Space} {hs : inner ℝ s s = 1} {E : ElectricField}
    {B : MagneticField} (hBwave : B = magneticPlaneWave B₀ c s hs)
    (h' : Differentiable ℝ B₀) (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : Time → EuclideanSpace ℝ (Fin 3)), ∀ t x, inner ℝ (B t x - c t) s = 0 := by
  have B'eqdivB : ∀ t x y, inner ℝ (fderiv ℝ (B t) x y) s = inner ℝ y s * (∇ ⬝ (B t)) x := by
    intro t x y
    rw [hBwave, magneticPlaneWave]
    unfold planeWave div coord basis Space.deriv
    rw [PiLp.inner_apply]
    simp [-PiLp.inner_apply]
    conv_lhs =>
      enter [2, i]
      rw [wave_fderiv_inner_eq_inner_fderiv_proj h']
    rw [← Finset.mul_sum]
    simp
  have B'eqzero : ∀ t x, fderiv ℝ (fun x => (inner ℝ (B t x) s)) x = 0 := by
    intro t x
    ext y
    rw [fderiv_inner_apply]
    simp [-PiLp.inner_apply]
    rw [B'eqdivB]
    rw [OM.gaussLawMagnetic_of_free E B]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_zero]
    exact hm
    rw [hBwave, magneticPlaneWave]
    unfold planeWave
    apply Differentiable.comp
    fun_prop
    exact fun x => wave_differentiable
    fun_prop
  use fun t => B t 0
  intro t x
  have hx' := B'eqzero t
  apply is_const_of_fderiv_eq_zero at hx'
  rw [inner_sub_left, hx' x 0]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sub_self]
  apply Differentiable.inner
  rw [hBwave, magneticPlaneWave]
  unfold planeWave
  apply Differentiable.comp
  fun_prop
  exact fun x => wave_differentiable
  fun_prop

/-- The time derivative of a magnetic planewave induces an electric field with
time derivative equal to `- s ⨯ₑ₃ B'`. -/
lemma time_deriv_electricPlaneWave_eq_cross_time_deriv_magneticPlaneWave
    {t : Time} {x : Space} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Space} {hs : inner ℝ s s = 1} {E : ElectricField} {B : MagneticField}
    (hc : c = (√(μ • ε))⁻¹) (hBwave : B = magneticPlaneWave B₀ c s hs)
    (h' : Differentiable ℝ B₀) (hm : OM.FreeMaxwellEquations E B) :
    (√(μ • ε)) • ∂ₜ (fun t => E t x) t = - (s ⨯ₑ₃ (∂ₜ (fun t => B t x) t)) := by
  have h : (√(μ • ε)) = ((√(μ • ε))⁻¹) • (μ • ε) := by
    nth_rw 3 [← Real.sq_sqrt (le_of_lt (smul_pos OM.mu_ge_zero OM.eps_ge_zero))]
    rw [pow_two]
    simp [← mul_assoc]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    simp only [smul_eq_mul, _root_.mul_inv_rev, ← smul_assoc, mul_assoc, ne_eq, OM.mu_ge_zero,
      ne_of_gt, not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    exact hm
  rw [h, smul_assoc, hdt, hBwave, magneticPlaneWave, ← hc, crossProduct]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · simp [-PiLp.inner_apply, ← mul_assoc, OM.mu_ge_zero, OM.eps_ge_zero, ne_of_gt]
    rw [mul_sub, space_fderiv_of_inner_product_wave_eq_space_fderiv h',
      space_fderiv_of_inner_product_wave_eq_space_fderiv h']
    ring

/-- The time derivative of an electric planewave induces a magnetic field with
time derivative equal to `s ⨯ₑ₃ E'`. -/
lemma time_deriv_magneticPlaneWave_eq_cross_time_deriv_electricPlaneWave
    {t : Time} {x : Space} {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Space} {hs : inner ℝ s s = 1} {E : ElectricField} {B : MagneticField}
    (hc : c = (√(μ • ε))⁻¹) (hEwave : E = electricPlaneWave E₀ c s hs)
    (h' : Differentiable ℝ E₀) (hm : OM.FreeMaxwellEquations E B) :
    (√(μ • ε))⁻¹ • ∂ₜ (fun t => B t x) t = s ⨯ₑ₃ (∂ₜ (fun t => E t x) t) := by
  rw [← neg_neg (∂ₜ (fun t => B t x) t),
      ← OM.faradayLaw_of_free E B, hEwave, electricPlaneWave, ← hc, crossProduct]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · simp [-PiLp.inner_apply]
    rw [mul_sub, space_fderiv_of_inner_product_wave_eq_space_fderiv h',
      space_fderiv_of_inner_product_wave_eq_space_fderiv h']
    ring
  exact hm

/-- A magnetic planewave induces an electric field equal to `- s ⨯ₑ₃ B` plus a constant field. -/
lemma electricPlaneWave_eq_cross_magneticPlaneWave_upto_space_fun
    {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Space} {hs : inner ℝ s s = 1}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hBwave : B = magneticPlaneWave B₀ c s hs) (h' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) (hE : ContDiff ℝ 2 ↿E) :
    ∃ (c : Space → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (√(μ • ε)) • (E t x) = - (s ⨯ₑ₃ (B t x)) + c x := by
  have h : ∀ t x, ∂ₜ (fun t => (√(μ • ε)) • (E t x)) t + ∂ₜ (fun t => s ⨯ₑ₃ (B t x)) t = 0 := by
    intro t x
    rw [deriv_smul, time_deriv_electricPlaneWave_eq_cross_time_deriv_magneticPlaneWave
        OM hc hBwave h' hm]
    rw [time_deriv_cross_commute]
    simp only [neg_add_cancel]
    · exact time_differentiable_of_eq_planewave h' hBwave
    · exact fun x => function_differentiableAt_fst (hf := hE.two_differentiable) ..
  unfold Time.deriv at h
  have hderiv : ∀ t x, _root_.deriv (fun t => ((√(μ • ε)) • (E t x)) +
      s ⨯ₑ₃ (B t x)) t = 0 := by
    intro t x
    rw [_root_.deriv_add]
    simp_all
    · apply DifferentiableAt.const_smul
      exact function_differentiableAt_fst (hf := hE.two_differentiable) ..
    · exact crossProduct_differentiable_of_right_eq_planewave h' hBwave
  use fun x => (√(μ • ε)) • (E 0 x) + (s ⨯ₑ₃ B 0 x)
  intro t x
  have ht' := fun t => hderiv t x
  apply is_const_of_deriv_eq_zero at ht'
  simp only
  rw [ht' 0 t]
  simp only [smul_eq_mul, neg_add_cancel_comm_assoc]
  · intro x
    apply DifferentiableAt.add
    · apply DifferentiableAt.const_smul
      exact function_differentiableAt_fst (hf := hE.two_differentiable) ..
    · exact crossProduct_differentiable_of_right_eq_planewave h' hBwave

/-- An electric planewave induces an magnetic field equal to `s ×₃ E` plus a constant field. -/
lemma magneticPlaneWave_eq_cross_electricPlaneWave_upto_space_fun
    {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Space} {hs : inner ℝ s s = (1:ℝ)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s hs) (h' : Differentiable ℝ E₀)
    (hm : OM.FreeMaxwellEquations E B) (hB : ContDiff ℝ 2 ↿B) :
    ∃ (c : Space → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (√(μ • ε))⁻¹ • (B t x) = s ⨯ₑ₃ (E t x) + c x := by
  have h : ∀ t x, ∂ₜ (fun t => (√(μ • ε))⁻¹ • (B t x)) t -
      ∂ₜ (fun t => s ⨯ₑ₃ (E t x)) t = 0 := by
    intro t x
    rw [deriv_smul, time_deriv_magneticPlaneWave_eq_cross_time_deriv_electricPlaneWave
        OM hc hEwave h' hm]
    rw [time_deriv_cross_commute]
    simp [sub_self]
    · exact time_differentiable_of_eq_planewave h' hEwave
    · exact fun x => function_differentiableAt_fst (hf := hB.two_differentiable) ..
  unfold Time.deriv at h
  have hderiv : ∀ t x, fderiv ℝ (fun t => ((√(μ • ε))⁻¹ • (B t x)) -
      s ⨯ₑ₃ (E t x)) t = 0 := by
    intro t x
    ext y
    rw [fderiv_sub]
    change (fderiv ℝ (fun t => (√(μ • ε))⁻¹ • B t x) t 1 -
        fderiv ℝ (fun t => s ⨯ₑ₃ (E t x)) t 1) y = _
    rw [h]
    simp only [PiLp.zero_apply, ContinuousLinearMap.zero_apply]
    · apply DifferentiableAt.const_smul
      exact function_differentiableAt_fst (hf := hB.two_differentiable) ..
    · exact crossProduct_differentiable_of_right_eq_planewave h' hEwave
  use fun x => (√(μ • ε))⁻¹ • (B 0 x) - (s ⨯ₑ₃ E 0 x)
  intro t x
  have ht' := fun t => hderiv t x
  apply is_const_of_fderiv_eq_zero at ht'
  simp only
  rw [ht' 0 t]
  simp only [smul_eq_mul, add_sub_cancel]
  · intro x
    apply DifferentiableAt.sub
    · apply DifferentiableAt.const_smul
      exact function_differentiableAt_fst (hf := hB.two_differentiable) ..
    · exact crossProduct_differentiable_of_right_eq_planewave h' hEwave
