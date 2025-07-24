/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.StarOrdered
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# Solutions to the classical harmonic oscillator

-/

namespace ClassicalMechanics
open Real

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

/-!

## The solution for given initial conditions

-/

/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity. -/
structure InitialConditions where
  /-- The initial time. -/
  t₀ : Time
  /-- The initial position of the harmonic oscillator. -/
  x₀ : Space 1
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : Space 1


TODO "6VZME" "Implement other initial condtions. For example:
- initial conditions at a given time.
- Two positions at different times.
- Two velocities at different times.
And convert them into the type `InitialConditions` above (which may need generalzing a bit
to make this possible)."

@[ext]
lemma InitialConditions.ext {IC₁ IC₂ : InitialConditions} (ht : IC₁.t₀ = IC₂.t₀)
    (h1 : IC₁.x₀ = IC₂.x₀) (h2 : IC₁.v₀ = IC₂.v₀) : IC₁ = IC₂ := by
  cases IC₁
  cases IC₂
  simp_all

/-!

## The zero initial condition

-/

/-- The zero initial condition. -/
def zeroIC (t₀ : Time) : InitialConditions := ⟨t₀, 0, 0⟩

/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zeroIC (t₀ : Time) : (zeroIC t₀).x₀ = 0 := rfl

/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zeroIC (t₀ : Time) : (zeroIC t₀).v₀ = 0 := rfl

/-!

## The solution

-/

/-- Given initial conditions, the solution to the classical harmonic oscillator. -/
noncomputable def sol (IC : InitialConditions) : Time → Space 1 := fun t =>
  cos (S.ω * (t - IC.t₀)) • IC.x₀ + (sin (S.ω * (t - IC.t₀))/S.ω) • IC.v₀

lemma sol_eq (IC : InitialConditions) :
    S.sol IC = fun t => cos (S.ω * (t - IC.t₀)) • IC.x₀ +
    (sin (S.ω * (t - IC.t₀))/S.ω) • IC.v₀ := rfl

/-- For zero initial conditions, the solution is zero. -/
lemma sol_zeroIC (t₀ : Time) : S.sol (zeroIC t₀) = fun _ => 0 := by
  simp [sol_eq]

/-- Given initial conditions, the amplitude of the classical harmonic oscillator. -/
noncomputable def amplitude (IC : InitialConditions) : ℝ :=
  (polarCoord (‖IC.x₀‖, ‖IC.v₀‖/S.ω)).1

lemma amplitude_eq (IC : InitialConditions) :
    S.amplitude IC = √(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) := by rfl

/-- The amplitude of the classical harmonic oscillator is non-negative. -/
@[simp]
lemma amplitude_nonneg (IC : InitialConditions) : 0 ≤ S.amplitude IC := by
  simp [amplitude_eq]

open Complex in
lemma amplitude_eq_norm (IC : InitialConditions) :
    S.amplitude IC = ‖((IC.x₀ 0) - (1 / S.ω) * (IC.v₀ 0) * Complex.I)‖ := by
  rw [amplitude_eq]
  trans √(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2)
  · ring
  · simp only [Complex.norm_add_mul_I, norm_eq_sqrt_sq_add_sq]
    simp only [Fin.isValue, one_div, real_smul, smul_eq_mul, sub_re, ofReal_re, mul_re, inv_re,
      normSq_ofReal, div_self_mul_self', I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, inv_im,
      neg_zero, zero_div, mul_im, add_zero, zero_mul, sub_zero, sub_im, zero_sub, even_two,
      Even.neg_pow]
    field_simp
    rw [@PiLp.norm_sq_eq_of_L2, @PiLp.norm_sq_eq_of_L2]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, norm_eq_abs, sq_abs,
      Finset.sum_singleton]

lemma amplitude_sq (IC : InitialConditions) :
    S.amplitude IC ^ 2 = ‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2 := by
  simp [amplitude_eq, sq_nonneg, add_nonneg]

@[simp]
lemma amplitude_zeroIC (t₀ : Time) : S.amplitude (zeroIC t₀) = 0 := by
  simp [amplitude_eq]

/-- The amplitude is zero if and only if the inital conditions are zero. -/
lemma amplitude_eq_zero_iff_IC_eq_zeroIC (IC : InitialConditions) :
    S.amplitude IC = 0 ↔ IC = zeroIC IC.t₀ := by
  rw [amplitude_eq]
  apply Iff.intro <;> intro h
  · rw [← Complex.norm_add_mul_I, norm_eq_zero, ← Complex.mk_eq_add_mul_I, Complex.ext_iff] at h
    simp only [Complex.zero_re, Complex.zero_im, div_eq_zero_iff, ω_neq_zero, or_false] at h
    aesop
  · rw [h, h]
    simp

/-- Given initial conditions, the phase of the classical harmonic oscillator. -/
noncomputable def phase (IC : InitialConditions) : ℝ :=
  (polarCoord (IC.x₀ 0, - (IC.v₀ 0)/S.ω)).2

lemma phase_le_pi (IC : InitialConditions) : (S.phase IC) ≤ π := by
  simp [phase, Complex.arg_le_pi]

lemma neg_pi_lt_phase (IC : InitialConditions) : -π < S.phase IC := by
  simp [phase, Complex.neg_pi_lt_arg]

@[simp]
lemma phase_zeroIC (t₀ : Time) : S.phase (zeroIC t₀) = 0 := by
  simp [phase]

lemma amplitude_mul_cos_phase (IC : InitialConditions) :
    S.amplitude IC * cos (S.phase IC) = IC.x₀ 0 := by
  simp only [phase, amplitude_eq_norm, polarCoord_apply, Complex.equivRealProd_symm_apply,
    smul_eq_mul, Complex.ofReal_div, Complex.ofReal_neg]
  group
  simp

lemma amplitude_mul_sin_phase (IC : InitialConditions) :
    S.amplitude IC * sin (S.phase IC) = - (1/S.ω) • IC.v₀ 0 := by
  simp only [phase, amplitude_eq_norm, polarCoord_apply, Complex.equivRealProd_symm_apply,
    smul_eq_mul, Complex.ofReal_div, Complex.ofReal_neg]
  group
  simp

lemma sol_eq_amplitude_mul_cos_phase (IC : InitialConditions) :
    S.sol IC = fun t => S.amplitude IC • (fun _ => cos (S.ω * (t - IC.t₀) + S.phase IC)) := by
  funext t
  rw [cos_add]
  trans fun _ => (S.amplitude IC • cos (S.phase IC)) • cos (S.ω * (t - IC.t₀)) -
    (S.amplitude IC • sin (S.phase IC)) • sin (S.ω * (t - IC.t₀))
  · simp_rw [sol, smul_eq_mul, amplitude_mul_cos_phase, amplitude_mul_sin_phase]
    simp only [Fin.isValue, one_div, smul_eq_mul, neg_mul, sub_neg_eq_add]
    rw [@PiLp.ext_iff]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.isValue]
    intro i
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue]
    group
  · simp only [smul_eq_mul]
    rw [@funext_iff]
    simp only [Pi.smul_apply, smul_eq_mul, forall_const]
    group

/-- For any time the position of the harmonic oscillator is less then the
  amplitude. -/
lemma abs_sol_le_amplitude (IC : InitialConditions) (t : ℝ) : ‖S.sol IC t‖ ≤ S.amplitude IC := by
  rw [sol_eq_amplitude_mul_cos_phase]
  rw [norm_smul, norm_of_nonneg (S.amplitude_nonneg IC)]
  trans S.amplitude IC * 1
  · apply mul_le_mul_of_nonneg
    · exact Preorder.le_refl (S.amplitude IC)
    · simp only [@PiLp.norm_eq_of_L2, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_singleton, one_smul, sqrt_le_one,
        sq_le_one_iff_abs_le_one]
      exact abs_cos_le_one (S.ω * (t - IC.t₀) + S.phase IC)
    · exact amplitude_nonneg S IC
    · exact zero_le_one' ℝ
  · simp

/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma sol_t₀ (IC : InitialConditions) : S.sol IC IC.t₀ = IC.x₀ := by
  simp [sol]

/-- The solutions are differentiable. -/
@[fun_prop]
lemma sol_differentiable (IC : InitialConditions) : Differentiable ℝ (S.sol IC) := by
  rw [sol_eq]
  fun_prop

lemma sol_velocity (IC : InitialConditions) : deriv (S.sol IC) =
    fun t => -S.ω • sin (S.ω * (t - IC.t₀)) • IC.x₀ + cos (S.ω * (t - IC.t₀)) • IC.v₀ := by
  funext t
  rw [sol_eq, deriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [differentiableAt_const, deriv_const_mul_field']
  rw [deriv_smul_const (by fun_prop), deriv_smul_const (by fun_prop)]
  simp only [deriv_div_const, neg_smul]
  rw [deriv_cos (by fun_prop), deriv_sin (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp
  ring_nf
  rw [← mul_smul, add_right_inj, mul_rotate, NonUnitalRing.mul_assoc]
  field_simp [mul_div_assoc, div_self, mul_one, S.ω_neq_zero]

lemma sol_velocity_amplitude_phase (IC : InitialConditions) : deriv (S.sol IC) =
    fun t => - S.amplitude IC • (fun _ => S.ω • sin (S.ω * (t - IC.t₀) + S.phase IC)) := by
  funext t i
  rw [sol_eq_amplitude_mul_cos_phase]
  simp only [differentiableAt_const, deriv_const_mul_field']
  rw [@deriv_fun_const_smul']
  simp only [deriv_div_const, neg_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.smul_apply]
  rw [deriv_pi, deriv_cos (by fun_prop), deriv_add_const', neg_mul, mul_neg,
    deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add, neg_inj, mul_eq_mul_left_iff]
  left
  · simp
    exact Lean.Grind.CommSemiring.mul_comm _ S.ω
  · fun_prop

@[simp]
lemma sol_velocity_t₀ (IC : InitialConditions) : deriv (S.sol IC) IC.t₀ = IC.v₀ := by
  simp [sol_velocity]

lemma sol_potentialEnergy (IC : InitialConditions) (t : Time) : S.potentialEnergy (S.sol IC t) =
    1/2 * (S.k * ‖IC.x₀‖ ^ 2 + S.m * ‖IC.v₀‖ ^2) * cos (S.ω * (t - IC.t₀)  + S.phase IC) ^ 2 := by
  trans 1/2 * S.k * (‖IC.x₀‖ ^ 2 + (1 / S.ω) ^ 2 * ‖IC.v₀‖ ^ 2) *
    cos (S.ω * (t - IC.t₀) + S.phase IC) ^ 2
  · rw [potentialEnergy, sol_eq_amplitude_mul_cos_phase]
    ring_nf
    simp only [one_div, PiLp.inner_apply, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Pi.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial, Finset.sum_const,
      Finset.card_singleton, one_smul, inv_pow]
    rw [@mul_mul_mul_comm, ← pow_two (S.amplitude IC), amplitude_sq]
    ring_nf
  simp only [one_div, inv_pow, inverse_ω_sq, mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  field_simp
  left
  ring

lemma sol_kineticEnergy (IC : InitialConditions) : S.kineticEnergy (S.sol IC) =
    fun t => 1/2 * (S.k * ‖IC.x₀‖ ^ 2 + S.m * ‖IC.v₀‖ ^2) *
      sin (S.ω * (t - IC.t₀) + S.phase IC) ^ 2 := by
  funext t
  trans 1/2 * S.m * (‖IC.x₀‖ ^ 2 + (1 / S.ω) ^ 2 * ‖IC.v₀‖ ^ 2) * S.ω ^ 2
    * sin (S.ω * (t - IC.t₀) + S.phase IC) ^ 2
  · rw [kineticEnergy, sol_velocity_amplitude_phase]
    ring_nf
    simp only [smul_eq_mul, neg_smul, inner_neg_right, inner_neg_left, PiLp.inner_apply,
      Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Pi.smul_apply, RCLike.inner_apply,
      conj_trivial, Finset.sum_const, Finset.card_singleton, one_smul, neg_neg, one_div, inv_pow]
    rw [@mul_mul_mul_comm, ← pow_two (S.amplitude IC), amplitude_sq]
    ring
  simp only [one_div, inv_pow, inverse_ω_sq, mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  simp only [ω_sq]
  left
  field_simp
  ring

lemma sol_energy (IC : InitialConditions) : S.energy (S.sol IC) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy, sol_kineticEnergy, sol_potentialEnergy]
  trans 1/2 * (S.k * ‖IC.x₀‖ ^ 2 + S.m * ‖IC.v₀‖ ^2) *
    (cos (S.ω * (t - IC.t₀) + S.phase IC) ^ 2 + sin (S.ω * (t - IC.t₀) + S.phase IC) ^ 2)
  · ring_nf
  rw [cos_sq_add_sin_sq]
  simp only [one_div, mul_one, mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
  ring

lemma sol_lagrangian (IC : InitialConditions) : S.lagrangian (S.sol IC) =
    fun t => - 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) *
      cos (2 * (S.ω * (t - IC.t₀) + S.phase IC)) := by
  funext t
  rw [lagrangian, sol_kineticEnergy, sol_potentialEnergy, Real.cos_two_mul']
  ring

open MeasureTheory in
lemma sol_action (IC : InitialConditions) (t1 t2 : ℝ) :
    ∫ t' in t1..t2, S.lagrangian (S.sol IC) t' = - 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) *
      (S.ω⁻¹ * 2⁻¹ * (sin (2 * (S.ω * (t2 - IC.t₀) + S.phase IC)) -
        sin (2 * (S.ω * (t1 - IC.t₀) + S.phase IC)))) := by
  rw [sol_lagrangian]
  simp only [intervalIntegral.integral_const_mul, mul_eq_mul_left_iff, mul_eq_zero, div_eq_zero_iff,
    neg_eq_zero, one_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
  left
  calc ∫ (x : ℝ) in t1..t2, cos (2 * (S.ω * (x - IC.t₀) + S.phase IC))
    _ = ∫ (x : ℝ) in t1..t2, cos ((2 * S.ω) * ((x - IC.t₀) + S.phase IC/S.ω)) := by
      congr
      funext t
      congr 1
      field_simp [S.ω_neq_zero]
      ring
    _ = ∫ (x : ℝ) in t1..t2, cos ((2 * S.ω) * (x + (- IC.t₀ + S.phase IC/S.ω))) := by
      congr
      funext t
      congr 1
      ring
    _ = ∫ (x : ℝ) in (t1 + (- IC.t₀ + S.phase IC/S.ω))..(t2 + (- IC.t₀ + S.phase IC/S.ω)),
        cos (2 * S.ω * x) := by
      rw [intervalIntegral.integral_comp_add_right (b := t2) (a := t1) (fun x => cos (2 * S.ω * x))
        (- IC.t₀ + S.phase IC/S.ω)]
    _ = S.ω⁻¹ * 2⁻¹ * (sin (2 * (S.ω * (t2 - IC.t₀) + S.phase IC)) -
        sin (2 * (S.ω * (t1 - IC.t₀) + S.phase IC))) := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ω_neq_zero, or_self, not_false_eq_true,
        intervalIntegral.integral_comp_mul_left, mul_inv_rev, integral_cos, smul_eq_mul,
        mul_eq_mul_left_iff, inv_eq_zero, or_false]
      congr 2
      · field_simp [S.ω_neq_zero]
        ring
      · field_simp [S.ω_neq_zero]
        ring

/-!

## Some semi-formal results

-/

TODO "6VZI3" "For the classical harmonic oscillator find the time for which it returns to
  it's initial position and velocity."

TODO "6VZJB" "For the classical harmonic oscillator find the times for
  which it passes through zero."

TODO "6VZJH" "For the classical harmonic oscillator find the velocity when it passes through
  zero."

/-- The solutions for any initial condition solve the equation of motion. -/
@[sorryful]
lemma sol_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion (S.sol IC) := by sorry

/-- The solutions to the equation of motion for a given set of initial conditions
  are unique.

  Semiformal implmentation:
  - One may needed the added condition of smoothness on `x` here.
  - `EquationOfMotion` needs defining before this can be proved. -/
@[sorryful]
lemma sol_unique (IC : InitialConditions) (x : Time → Space 1) :
    EquationOfMotion x ∧ x 0 = IC.x₀ ∧ deriv x 0 = IC.v₀ →
    x = S.sol IC := by sorry

end HarmonicOscillator

end ClassicalMechanics
