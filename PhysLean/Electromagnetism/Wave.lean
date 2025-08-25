/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Homogeneous
import PhysLean.ClassicalMechanics.WaveEquation.Basic
import PhysLean.SpaceAndTime.Space.VectorIdentities
/-!

# Electromagnetic wave equation

The electromagnetic wave eqaution as a consequence of the charge and current free
Maxwell's Equations in homogeneous isotropic medium.

-/

namespace Electromagnetism

open Space Module
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
noncomputable def electricPlaneWave (E₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Direction) : ElectricField :=
    planeWave E₀ c s

/-- A magnetic plane wave travelling in the direction of `s` with propagation speed `c`. -/
noncomputable def magneticPlaneWave (B₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Direction) : MagneticField :=
    planeWave B₀ c s

/-- An electric plane wave minus a constant field is transverse for all x. -/
lemma transverse_upto_time_fun_of_eq_electricPlaneWave {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Direction} {E : ElectricField} {B : MagneticField}
    (hEwave : E = electricPlaneWave E₀ c s)
    (h' : Differentiable ℝ E₀) (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : Time → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    inner ℝ (E t x) s.unit = inner ℝ (c t) s.unit := by
  have E'eqdivE : ∀ t x y, inner ℝ (fderiv ℝ (E t) x y) s.unit =
      inner ℝ y s.unit * (∇ ⬝ (E t)) x := by
    intro t x y
    rw [hEwave, electricPlaneWave]
    unfold planeWave div coord basis Space.deriv
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, EuclideanSpace.basisFun_apply]
    conv_lhs =>
      enter [2, i]
      rw [wave_fderiv_inner_eq_inner_fderiv_proj h']
    rw [← Finset.mul_sum]
    simp [PiLp.inner_apply]
  have E'eqzero : ∀ t x, fderiv ℝ (fun x => (inner ℝ (E t x) s.unit)) x = 0 := by
    intro t x
    ext y
    rw [fderiv_inner_apply]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      zero_add]
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
  rw [hx' x 0]
  apply Differentiable.inner
  rw [hEwave, electricPlaneWave]
  unfold planeWave
  apply Differentiable.comp
  fun_prop
  exact fun x => wave_differentiable
  fun_prop

/-- An magnetic plane wave minus a constant field is transverse for all x. -/
lemma transverse_upto_time_fun_of_eq_magneticPlaneWave {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Direction} {E : ElectricField} {B : MagneticField}
    (hBwave : B = magneticPlaneWave B₀ c s)
    (h' : Differentiable ℝ B₀) (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : Time → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    inner ℝ (B t x) s.unit = inner ℝ (c t) s.unit := by
  have B'eqdivB : ∀ t x y, inner ℝ (fderiv ℝ (B t) x y) s.unit =
      inner ℝ y s.unit * (∇ ⬝ (B t)) x := by
    intro t x y
    rw [hBwave, magneticPlaneWave]
    unfold planeWave div coord basis Space.deriv
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, EuclideanSpace.basisFun_apply]
    conv_lhs =>
      enter [2, i]
      rw [wave_fderiv_inner_eq_inner_fderiv_proj h']
    rw [← Finset.mul_sum]
    simp [PiLp.inner_apply]
  have B'eqzero : ∀ t x, fderiv ℝ (fun x => (inner ℝ (B t x) s.unit)) x = 0 := by
    intro t x
    ext y
    rw [fderiv_inner_apply]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      zero_add]
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
  rw [hx' x 0]
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
    {s : Direction} {E : ElectricField} {B : MagneticField}
    (hc : c = (√(μ • ε))⁻¹) (hBwave : B = magneticPlaneWave B₀ c s)
    (h' : Differentiable ℝ B₀) (hm : OM.FreeMaxwellEquations E B) :
    ∂ₜ (fun t => E t x) t = - (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (∂ₜ (fun t => B t x) t)) := by
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    simp only [smul_eq_mul, _root_.mul_inv_rev, ← smul_assoc, mul_assoc, ne_eq, OM.mu_ge_zero,
      ne_of_gt, not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    exact hm
  rw [hdt, hBwave, magneticPlaneWave, ← hc, crossProduct]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · rw [← Real.sq_sqrt (inv_nonneg_of_nonneg (le_of_lt (smul_pos OM.mu_ge_zero OM.eps_ge_zero))),
      Real.sqrt_inv, ← hc]
    simp [← mul_assoc, OM.mu_ge_zero, OM.eps_ge_zero, ne_of_gt]
    rw [mul_sub, pow_two,
      mul_assoc, space_fderiv_of_inner_product_wave_eq_space_fderiv h',
      mul_assoc, space_fderiv_of_inner_product_wave_eq_space_fderiv h']
    ring

/-- The time derivative of an electric planewave induces a magnetic field with
time derivative equal to `s ⨯ₑ₃ E'`. -/
lemma time_deriv_magneticPlaneWave_eq_cross_time_deriv_electricPlaneWave
    {t : Time} {x : Space} {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {s : Direction} {E : ElectricField} {B : MagneticField}
    (hc : c = (√(μ • ε))⁻¹) (hEwave : E = electricPlaneWave E₀ c s)
    (h' : Differentiable ℝ E₀) (hm : OM.FreeMaxwellEquations E B) :
    ∂ₜ (fun t => B t x) t = (√(μ • ε)) • (s.unit ⨯ₑ₃ (∂ₜ (fun t => E t x) t)) := by
  have h : (√(μ • ε)) = c⁻¹ := by
    rw [hc]
    simp
  have hc_non_zero : c ≠ 0 := by
    rw [hc]
    simp [ne_of_gt, OM.mu_ge_zero, OM.eps_ge_zero]
  rw [← neg_neg (∂ₜ (fun t => B t x) t),
      ← OM.faradayLaw_of_free E B, hEwave, electricPlaneWave, h, crossProduct]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · simp
    rw [← mul_right_inj' hc_non_zero, mul_sub,
      space_fderiv_of_inner_product_wave_eq_space_fderiv h',
      space_fderiv_of_inner_product_wave_eq_space_fderiv h',
      ← mul_assoc, mul_inv_cancel₀ hc_non_zero]
    ring
  exact hm

/-- A magnetic planewave induces an electric field equal to `- s ⨯ₑ₃ B` plus a constant field. -/
lemma electricPlaneWave_eq_cross_magneticPlaneWave_upto_space_fun
    {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Direction}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hBwave : B = magneticPlaneWave B₀ c s) (h' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) (hE : Differentiable ℝ ↿E) :
    ∃ (c : Space → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (E t x) = - (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x)) + c x := by
  have h : ∀ t x, ∂ₜ (fun t => (E t x)) t + (√(μ • ε))⁻¹ •
      ∂ₜ (fun t => s.unit ⨯ₑ₃ (B t x)) t = 0 := by
    intro t x
    rw [time_deriv_electricPlaneWave_eq_cross_time_deriv_magneticPlaneWave
        OM hc hBwave h' hm]
    rw [time_deriv_cross_commute]
    simp only [smul_eq_mul, neg_smul, neg_add_cancel]
    · exact time_differentiable_of_eq_planewave h' hBwave
  unfold Time.deriv at h
  have hderiv' : ∀ t x, fderiv ℝ (fun t => (E t x) +
      (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x))) t 1 = 0 := by
    intro t x
    rw [fderiv_fun_add, fderiv_fun_smul]
    simp_all
    · fun_prop
    · exact crossProduct_time_differentiable_of_right_eq_planewave h' hBwave
    · exact function_differentiableAt_fst (hf := by fun_prop) ..
    · apply DifferentiableAt.fun_const_smul
      exact crossProduct_time_differentiable_of_right_eq_planewave h' hBwave
  have hderiv : ∀ t x, fderiv ℝ (fun t => (E t x) +
      (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x))) t = 0 := by
    intro t x
    ext1 r
    conv_lhs =>
      enter [2]
      rw [Time.eq_one_smul r]
    simp only [smul_eq_mul, WithLp.equiv_apply, WithLp.equiv_symm_apply, map_smul,
      ContinuousLinearMap.zero_apply, smul_eq_zero, eq_zero_iff]
    right
    exact hderiv' t x
  use fun x => (E 0 x) + (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ B 0 x)
  intro t x
  have ht' := fun t => hderiv t x
  apply is_const_of_fderiv_eq_zero at ht'
  simp only
  rw [ht' 0 t]
  simp only [smul_eq_mul, neg_smul, neg_add_cancel_comm_assoc]
  · intro x
    apply DifferentiableAt.add
    · exact function_differentiableAt_fst (hf := by fun_prop) ..
    · apply DifferentiableAt.fun_const_smul
      exact crossProduct_time_differentiable_of_right_eq_planewave h' hBwave

/-- An electric planewave induces an magnetic field equal to `s ×₃ E` plus a constant field. -/
lemma magneticPlaneWave_eq_cross_electricPlaneWave_upto_space_fun
    {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Direction}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s) (h' : Differentiable ℝ E₀)
    (hm : OM.FreeMaxwellEquations E B) (hB : Differentiable ℝ ↿B) :
    ∃ (c : Space → EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (B t x) = (√(μ • ε)) • (s.unit ⨯ₑ₃ (E t x)) + c x := by
  have h : ∀ t x, ∂ₜ (fun t => (B t x)) t -
      (√(μ • ε)) • ∂ₜ (fun t => s.unit ⨯ₑ₃ (E t x)) t = 0 := by
    intro t x
    rw [time_deriv_magneticPlaneWave_eq_cross_time_deriv_electricPlaneWave
        OM hc hEwave h' hm]
    rw [time_deriv_cross_commute]
    simp only [smul_eq_mul, sub_self]
    · exact time_differentiable_of_eq_planewave h' hEwave
  unfold Time.deriv at h
  have hderiv : ∀ t x, fderiv ℝ (fun t => (B t x) -
      (√(μ • ε)) • (s.unit ⨯ₑ₃ (E t x))) t = 0 := by
    intro t x
    ext1 r
    conv_lhs =>
      enter [2]
      rw [Time.eq_one_smul r]
    simp only [smul_eq_mul, WithLp.equiv_apply, WithLp.equiv_symm_apply, map_smul,
      ContinuousLinearMap.zero_apply, smul_eq_zero, eq_zero_iff]
    right
    rw [fderiv_fun_sub]
    rw [fderiv_fun_const_smul]
    change (fderiv ℝ (fun t => B t x) t 1) -
        ((√(μ • ε)) • fderiv ℝ (fun t => (s.unit ⨯ₑ₃ (E t x))) t 1) = _
    rw [h]
    · exact crossProduct_time_differentiable_of_right_eq_planewave h' hEwave
    · exact function_differentiableAt_fst (hf := by fun_prop) ..
    · apply DifferentiableAt.fun_const_smul
      exact crossProduct_time_differentiable_of_right_eq_planewave h' hEwave
  use fun x => (B 0 x) - (√(μ • ε)) • (s.unit ⨯ₑ₃ E 0 x)
  intro t x
  have ht' := fun t => hderiv t x
  apply is_const_of_fderiv_eq_zero at ht'
  simp only
  rw [ht' 0 t]
  simp only [smul_eq_mul, WithLp.equiv_apply, WithLp.equiv_symm_apply, add_sub_cancel]
  · intro x
    apply DifferentiableAt.sub
    · exact function_differentiableAt_fst (hf := by fun_prop) ..
    · apply DifferentiableAt.fun_const_smul
      exact crossProduct_time_differentiable_of_right_eq_planewave h' hEwave

/-- The electric field of an EMwave minus a constant field is transverse. -/
theorem electricField_transverse_upto_const_of_EMwave {s : Direction}
    {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s)
    (hBwave : B = magneticPlaneWave B₀ c s)
    (hE' : Differentiable ℝ E₀) (hB' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : EuclideanSpace ℝ (Fin 3)), ∀ t x, inner ℝ (E t x - c) s.unit = 0 := by
  have hdifferentiableE := differentiable_uncurry_of_eq_planewave hEwave hE'
  have hct := transverse_upto_time_fun_of_eq_electricPlaneWave OM hEwave hE' hm
  have hcx' := electricPlaneWave_eq_cross_magneticPlaneWave_upto_space_fun
    OM hc hBwave hB' hm hdifferentiableE
  obtain ⟨ct, hct⟩ := hct
  obtain ⟨cx, hcx'⟩ := hcx'
  have hcx : ∀ t x, inner ℝ (E t x) s.unit = inner ℝ (cx x) s.unit := by
    intro t x
    rw [hcx']
    simp only [smul_eq_mul, neg_smul, PiLp.inner_apply, PiLp.add_apply, PiLp.neg_apply,
      PiLp.smul_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    rw [crossProduct, Finset.sum, Finset.sum]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, LinearMap.mk₂_apply,
      WithLp.equiv_apply, PiLp.ofLp_apply, Fin.univ_val_map, List.ofFn_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.succ_zero_eq_one, Matrix.cons_val_fin_one, Fin.succ_one_eq_two,
      List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
    ring
  use cx 0
  intro t x
  rw [inner_sub_left]
  rw [hct]
  rw [← hcx t 0, ← hct t 0]
  simp

/-- The magnetic field of an EMwave minus a constant field is transverse. -/
theorem magneticField_transverse_upto_const_of_EMwave {s : Direction}
    {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s)
    (hBwave : B = magneticPlaneWave B₀ c s)
    (hE' : Differentiable ℝ E₀) (hB' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) :
    ∃ (c : EuclideanSpace ℝ (Fin 3)), ∀ t x, inner ℝ (B t x - c) s.unit = 0 := by
  have hdifferentiableB := differentiable_uncurry_of_eq_planewave hBwave hB'
  have hct := transverse_upto_time_fun_of_eq_magneticPlaneWave OM hBwave hB' hm
  have hcx' := magneticPlaneWave_eq_cross_electricPlaneWave_upto_space_fun
    OM hc hEwave hE' hm hdifferentiableB
  obtain ⟨ct, hct⟩ := hct
  obtain ⟨cx, hcx'⟩ := hcx'
  have hcx : ∀ t x, inner ℝ (B t x) s.unit = inner ℝ (cx x) s.unit := by
    intro t x
    rw [hcx']
    simp only [smul_eq_mul, neg_smul, PiLp.inner_apply, PiLp.add_apply, PiLp.neg_apply,
      PiLp.smul_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    rw [crossProduct, Finset.sum, Finset.sum]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
      LinearMap.mk₂_apply, PiLp.ofLp_apply, Fin.univ_val_map, List.ofFn_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.succ_zero_eq_one, Matrix.cons_val_fin_one, Fin.succ_one_eq_two,
      List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
    ring
  use cx 0
  intro t x
  rw [inner_sub_left]
  rw [hct]
  rw [← hcx t 0, ← hct t 0]
  simp

/-- `E + s ⨯ₑ₃ B` is constant for an EMwave. -/
lemma electricField_add_cross_magneticField_eq_const_of_planeWave
    {s : Direction} {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s)
    (hBwave : B = magneticPlaneWave B₀ c s)
    (hE' : Differentiable ℝ E₀) (hB' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) :
    ∃ (Ec : EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (E t x) + (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x)) = Ec := by
  have hc_non_zero : c ≠ 0 := by
    rw [hc]
    simp [ne_of_gt, OM.mu_ge_zero, OM.eps_ge_zero]
  have hcuE' : ∃ (Ecu : ℝ → EuclideanSpace ℝ (Fin 3)), ∀ t x,
      (E t x) + (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x)) = Ecu (inner ℝ x s.unit - c * t) := by
    use fun u => E₀ u + (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ B₀ u)
    intro t x
    rw [hEwave, hBwave, electricPlaneWave, magneticPlaneWave, planeWave, planeWave]
  have hdifferentiableE := differentiable_uncurry_of_eq_planewave hEwave hE'
  have hcxE' := electricPlaneWave_eq_cross_magneticPlaneWave_upto_space_fun
    OM hc hBwave hB' hm hdifferentiableE
  obtain ⟨Ecx, hcxE''⟩ := hcxE'
  obtain ⟨Ecu, hcuE⟩ := hcuE'
  have hcxE : ∀ t x, (E t x) + (√(μ • ε))⁻¹ • (s.unit ⨯ₑ₃ (B t x)) = Ecx x := by
    simp [hcxE'']
  use Ecu 0
  intro t x
  rw [hcxE]
  have hu : inner ℝ x s.unit - c * (c⁻¹ * inner ℝ x s.unit) = 0 := by
    rw [← mul_assoc]
    simp [hc_non_zero]
  rw [← hu, ← hcuE _ x, hcxE]

/-- `B - s ⨯ₑ₃ E` is constant for an EMwave. -/
lemma magneticField_sub_cross_electricField_eq_const_of_planeWave
    {s : Direction} {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s)
    (hBwave : B = magneticPlaneWave B₀ c s)
    (hE' : Differentiable ℝ E₀) (hB' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) :
    ∃ (Ec : EuclideanSpace ℝ (Fin 3)), ∀ t x,
    (B t x) - (√(μ • ε)) • (s.unit ⨯ₑ₃ (E t x)) = Ec := by
  have hc_non_zero : c ≠ 0 := by
    rw [hc]
    simp [ne_of_gt, OM.mu_ge_zero, OM.eps_ge_zero]
  have hcuB' : ∃ (Ecu : ℝ → EuclideanSpace ℝ (Fin 3)), ∀ t x,
      (B t x) - (√(μ • ε)) • (s.unit ⨯ₑ₃ (E t x)) = Ecu (inner ℝ x s.unit - c * t) := by
    use fun u => B₀ u - (√(μ • ε)) • (s.unit ⨯ₑ₃ E₀ u)
    intro t x
    rw [hEwave, hBwave, electricPlaneWave, magneticPlaneWave, planeWave, planeWave]
  have hdifferentiableB := differentiable_uncurry_of_eq_planewave hBwave hB'
  have hcxB' := magneticPlaneWave_eq_cross_electricPlaneWave_upto_space_fun
    OM hc hEwave hE' hm hdifferentiableB
  obtain ⟨Bcx, hcxB''⟩ := hcxB'
  obtain ⟨Bcu, hcuB⟩ := hcuB'
  have hcxB : ∀ t x, (B t x) - (√(μ • ε)) • (s.unit ⨯ₑ₃ (E t x)) = Bcx x := by
    simp [hcxB'']
  use Bcu 0
  intro t x
  rw [hcxB]
  have hu : inner ℝ x s.unit - c * (c⁻¹ * inner ℝ x s.unit) = 0 := by
    rw [← mul_assoc]
    simp [hc_non_zero]
  rw [← hu, ← hcuB _ x, hcxB]

/-- Unit vectors in the direciton of `B`, `E` and `s` form an orthonormal traid for an EMwave
after subtracting the appropriate constant fields. -/
theorem orthonormal_triad_of_electromagneticplaneWave {s : Direction}
    {E₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {B₀ : ℝ → EuclideanSpace ℝ (Fin 3)}
    {E : ElectricField} {B : MagneticField} (hc : c = (√(μ • ε))⁻¹)
    (hEwave : E = electricPlaneWave E₀ c s)
    (hBwave : B = magneticPlaneWave B₀ c s)
    (hE' : Differentiable ℝ E₀) (hB' : Differentiable ℝ B₀)
    (hm : OM.FreeMaxwellEquations E B) :
    ∃ (Ep Bp : EuclideanSpace ℝ (Fin 3)), ∀ t x,
    E t x - Ep ≠ 0 ∧ B t x - Bp ≠ 0 →
    Orthonormal ℝ ![((‖E t x - Ep‖)⁻¹) • (E t x - Ep),
    ((‖B t x - Bp‖)⁻¹) • (B t x - Bp), s.unit] := by
  obtain ⟨Ec, hEc⟩ := electricField_transverse_upto_const_of_EMwave OM hc hEwave hBwave hE' hB' hm
  obtain ⟨Bcdiff, hBcdiff⟩ := magneticField_sub_cross_electricField_eq_const_of_planeWave
      OM hc hEwave hBwave hE' hB' hm
  use Ec, Bcdiff + (√(μ • ε)) • (s.unit ⨯ₑ₃ Ec)
  intro t x h
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul, orthonormal_vecCons_iff,
    Fin.forall_fin_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, forall_const, IsEmpty.forall_iff, Orthonormal.of_isEmpty, and_self,
    and_true]
  repeat' constructor
  · exact norm_smul_inv_norm h.1
  · /- E orthogonal to B. -/
    rw [inner_smul_left, inner_smul_right]
    simp only [map_inv₀, conj_trivial, mul_eq_zero, inv_eq_zero, norm_eq_zero]
    right
    right
    rw [← hBcdiff t x]
    simp only [smul_eq_mul, sub_add, sub_sub_cancel]
    rw [← smul_sub, inner_smul_right]
    simp only [WithLp.equiv_symm_apply, WithLp.equiv_apply]
    rw [← WithLp.toLp_sub, ← LinearMap.map_sub, ← WithLp.ofLp_sub]
    conv_lhs =>
      enter [2]
      erw [inner_cross_self]
    simp
  · /- E orthogonal to s. -/
    rw [inner_smul_left]
    simp only [map_inv₀, conj_trivial, mul_eq_zero, inv_eq_zero, norm_eq_zero]
    right
    rw [hEc]
  · exact norm_smul_inv_norm h.2
  · /- B orthogonal to s. -/
    rw [inner_smul_left]
    simp only [map_inv₀, conj_trivial, mul_eq_zero, inv_eq_zero, norm_eq_zero]
    right
    rw [← hBcdiff t x]
    simp only [smul_eq_mul, sub_add, sub_sub_cancel]
    rw [← smul_sub, inner_smul_left]
    simp only [WithLp.equiv_symm_apply, WithLp.equiv_apply]
    rw [← WithLp.toLp_sub, ← LinearMap.map_sub, ← WithLp.ofLp_sub]
    rw [real_inner_comm]
    erw [inner_self_cross (s.unit) (E t x - Ec)]
    simp
  · exact s.norm

end Electromagnetism
