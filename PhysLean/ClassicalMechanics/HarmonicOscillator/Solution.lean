/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
import PhysLean.Meta.Informal.SemiFormal
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
  /-- The initial position of the harmonic oscillator. -/
  x₀ : ℝ
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : ℝ

TODO "6VZME" "Implement other initial condtions. For example:
- initial conditions at a given time.
- Two positions at different times.
- Two velocities at different times.
And convert them into the type `InitialConditions` above (which may need generalzing a bit
to make this possible)."

@[ext]
lemma InitialConditions.ext {IC₁ IC₂ : InitialConditions} (h1 : IC₁.x₀ = IC₂.x₀)
    (h2 : IC₁.v₀ = IC₂.v₀) : IC₁ = IC₂ := by
  cases IC₁
  cases IC₂
  simp_all

/-!

## The zero initial condition

-/

/-- The zero initial condition. -/
def zeroIC : InitialConditions := ⟨0, 0⟩

/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zeroIC : zeroIC.x₀ = 0 := rfl

/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zeroIC : zeroIC.v₀ = 0 := rfl

/-!

## The solution

-/

/-- Given initial conditions, the solution to the classical harmonic oscillator. -/
noncomputable def sol (IC : InitialConditions) : Time → ℝ := fun t =>
  IC.x₀ * cos (S.ω * t) + IC.v₀/S.ω * sin (S.ω * t)

lemma sol_eq (IC : InitialConditions) :
    S.sol IC = fun t => IC.x₀ * cos (S.ω * t) + IC.v₀/S.ω * sin (S.ω * t) := rfl

/-- For zero initial conditions, the solution is zero. -/
lemma sol_zeroIC : S.sol zeroIC = fun _ => 0 := by
  rw [sol_eq]
  funext t
  simp

/-- Given initial conditions, the amplitude of the classical harmonic oscillator. -/
noncomputable def amplitude (IC : InitialConditions) : ℝ :=
  (polarCoord (IC.x₀, IC.v₀/S.ω)).1

lemma amplitude_eq (IC : InitialConditions) :
    S.amplitude IC = sqrt (IC.x₀ ^ 2 + (IC.v₀ / S.ω) ^ 2) := rfl

/-- The amplitude of the classical harmonic oscillator is non-negative. -/
@[simp]
lemma amplitude_nonneg (IC : InitialConditions) : 0 ≤ S.amplitude IC := by
  rw [amplitude_eq]
  exact sqrt_nonneg _

open Complex in
lemma amplitude_eq_norm (IC : InitialConditions) :
    S.amplitude IC = ‖(↑IC.x₀ + -↑IC.v₀ / ↑S.ω * Complex.I)‖ := by
  rw [amplitude_eq]
  trans √(IC.x₀ ^ 2 + (- IC.v₀ / S.ω) ^ 2)
  · ring_nf
  · rw[← Complex.norm_add_mul_I]
    simp

lemma amplitude_sq (IC : InitialConditions) :
    S.amplitude IC ^ 2 = IC.x₀ ^ 2 + (IC.v₀ / S.ω) ^ 2 := by
  rw [amplitude_eq, sq_sqrt]
  apply add_nonneg
  · exact sq_nonneg IC.x₀
  · exact sq_nonneg (IC.v₀ / S.ω)

@[simp]
lemma amplitude_zeroIC : S.amplitude zeroIC = 0 := by
  rw [amplitude_eq]
  simp

/-- The amplitude is zero if and only if the inital conditions are zero. -/
lemma amplitude_eq_zero_iff_IC_eq_zeroIC (IC : InitialConditions) :
    S.amplitude IC = 0 ↔ IC = zeroIC := by
  rw [amplitude_eq]
  apply Iff.intro
  · intro h
    rw [← Complex.norm_add_mul_I, norm_eq_zero] at h
    rw [← Complex.mk_eq_add_mul_I, Complex.ext_iff] at h
    simp only [Complex.zero_re, Complex.zero_im, div_eq_zero_iff, ω_neq_zero, or_false] at h
    ext <;> simp [h]
  · intro h
    subst h
    simp

/-- Given initial conditions, the phase of the classical harmonic oscillator. -/
noncomputable def phase (IC : InitialConditions) : ℝ :=
  (polarCoord (IC.x₀, - IC.v₀/S.ω)).2

lemma phase_le_pi (IC : InitialConditions) : (S.phase IC) ≤ π := by
  rw [phase, polarCoord]
  simp only [Complex.equivRealProd_symm_apply, ne_eq, PartialHomeomorph.mk_coe, Complex.ofReal_div,
    Complex.ofReal_neg]
  exact Complex.arg_le_pi (↑IC.x₀ + -↑IC.v₀ / ↑S.ω * Complex.I)

lemma neg_pi_lt_phase (IC : InitialConditions) : -π < S.phase IC := by
  rw [phase, polarCoord]
  simp only [Complex.equivRealProd_symm_apply, ne_eq, PartialHomeomorph.mk_coe, Complex.ofReal_div]
  exact Complex.neg_pi_lt_arg (↑IC.x₀ + ↑(-IC.v₀) / ↑S.ω * Complex.I)

@[simp]
lemma phase_zeroIC : S.phase zeroIC = 0 := by
  rw [phase, polarCoord]
  simp

lemma amplitude_mul_cos_phase (IC : InitialConditions) :
    S.amplitude IC * cos (S.phase IC) = IC.x₀ := by
  rw [phase, amplitude_eq_norm]
  simp

lemma amplitude_mul_sin_phase (IC : InitialConditions) :
    S.amplitude IC * sin (S.phase IC) = - IC.v₀ / S.ω := by
  rw [phase, amplitude_eq_norm]
  simp

lemma sol_eq_amplitude_mul_cos_phase (IC : InitialConditions) :
    S.sol IC = fun t => S.amplitude IC * cos (S.ω * t + S.phase IC) := by
  funext t
  rw [cos_add]
  trans (S.amplitude IC * cos (S.phase IC)) * cos (S.ω * t) -
    (S.amplitude IC * sin (S.phase IC)) * sin (S.ω * t)
  · rw [amplitude_mul_cos_phase, amplitude_mul_sin_phase]
    rw [sol]
    field_simp
    ring
  · ring

/-- For any time the position of the harmonic oscillator is less then the
  amplitude. -/
lemma abs_sol_le_amplitude (IC : InitialConditions) (t : ℝ) :
    abs (S.sol IC t) ≤ S.amplitude IC := by
  rw [sol_eq_amplitude_mul_cos_phase]
  simp only
  rw [abs_mul]
  rw [abs_of_nonneg (S.amplitude_nonneg IC)]
  have h1 : abs (cos (S.ω * t + S.phase IC)) ≤ 1 := abs_cos_le_one (S.ω * t + S.phase IC)
  trans S.amplitude IC * 1
  · exact mul_le_mul_of_nonneg (Preorder.le_refl (S.amplitude IC)) h1
      (amplitude_nonneg S IC) (zero_le_one' ℝ)
  · simp

/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma sol_t_zero (IC : InitialConditions) : S.sol IC 0 = IC.x₀ := by
  simp [sol]

/-- The solutions are differentiable. -/
@[fun_prop]
lemma sol_differentiable (IC : InitialConditions) : Differentiable ℝ (S.sol IC) := by
  rw [sol_eq]
  fun_prop

lemma sol_velocity (IC : InitialConditions) : deriv (S.sol IC) =
    fun t => - IC.x₀ * S.ω * sin (S.ω * t) + IC.v₀ * cos (S.ω * t) := by
  funext t
  rw [sol_eq, deriv_add (by fun_prop) (by fun_prop)]
  simp only [differentiableAt_const, deriv_const_mul_field']
  rw [deriv_cos (by fun_prop), deriv_sin (by fun_prop), deriv_mul (by fun_prop) (by fun_prop)]
  field_simp [S.ω_neq_zero]
  ring_nf

lemma sol_velocity_amplitude_phase (IC : InitialConditions) : deriv (S.sol IC) =
    fun t => - S.amplitude IC * S.ω * sin (S.ω * t + S.phase IC) := by
  funext t
  rw [sol_eq_amplitude_mul_cos_phase]
  simp only [differentiableAt_const, deriv_const_mul_field']
  rw [deriv_cos (by fun_prop)]
  simp only [deriv_add_const', neg_mul, mul_neg]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  field_simp
  ring

@[simp]
lemma sol_velocity_t_zero (IC : InitialConditions) : deriv (S.sol IC) 0 = IC.v₀ := by
  rw [sol_velocity]
  simp

lemma sol_potentialEnergy (IC : InitialConditions) : S.potentialEnergy (S.sol IC) =
    fun t => 1/2 * (S.k * IC.x₀ ^ 2 + S.m * IC.v₀ ^2) * cos (S.ω * t + S.phase IC) ^ 2 := by
  funext t
  trans 1/2 * S.k * (IC.x₀ ^ 2 + (1 / S.ω) ^ 2 * IC.v₀ ^ 2) * cos (S.ω * t + S.phase IC) ^ 2
  · rw [potentialEnergy, sol_eq_amplitude_mul_cos_phase]
    ring_nf
    rw [amplitude_sq]
    ring_nf
  simp only [one_div, inv_pow, inverse_ω_sq, mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  field_simp
  left
  ring

lemma sol_kineticEnergy (IC : InitialConditions) : S.kineticEnergy (S.sol IC) =
    fun t => 1/2 * (S.k * IC.x₀ ^ 2 + S.m * IC.v₀ ^2) * sin (S.ω * t + S.phase IC) ^ 2 := by
  funext t
  trans 1/2 * S.m * (IC.x₀ ^ 2 + (1 / S.ω) ^ 2 * IC.v₀ ^ 2) * S.ω ^ 2
    * sin (S.ω * t + S.phase IC) ^ 2
  · rw [kineticEnergy, sol_velocity_amplitude_phase]
    ring_nf
    rw [amplitude_sq]
    ring
  simp only [one_div, inv_pow, inverse_ω_sq, mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  simp only [ω_sq]
  left
  field_simp
  ring

lemma sol_energy (IC : InitialConditions) : S.energy (S.sol IC) =
    fun _ => 1/2 * (S.m * IC.v₀ ^2 + S.k * IC.x₀ ^ 2) := by
  funext t
  rw [energy, sol_kineticEnergy, sol_potentialEnergy]
  trans 1/2 * (S.k * IC.x₀ ^ 2 + S.m * IC.v₀ ^2) *
    (cos (S.ω * t + S.phase IC) ^ 2 + sin (S.ω * t + S.phase IC) ^ 2)
  · ring_nf
  rw [cos_sq_add_sin_sq]
  simp only [one_div, mul_one, mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
  ring

lemma sol_lagrangian (IC : InitialConditions) : S.lagrangian (S.sol IC) =
    fun t => - 1/2 * (S.m * IC.v₀ ^2 + S.k * IC.x₀ ^ 2) * cos (2 * (S.ω * t + S.phase IC)) := by
  funext t
  rw [lagrangian, sol_kineticEnergy, sol_potentialEnergy]
  rw [Real.cos_two_mul']
  ring

open MeasureTheory in
lemma sol_action (IC : InitialConditions) (t1 t2 : ℝ) :
    ∫ t' in t1..t2, S.lagrangian (S.sol IC) t' = - 1/2 * (S.m * IC.v₀ ^2 + S.k * IC.x₀ ^ 2) *
      (S.ω⁻¹ * 2⁻¹ * (sin (2 * (S.ω * t2 + S.phase IC)) - sin (2 * (S.ω * t1 + S.phase IC)))) := by
  rw [sol_lagrangian]
  simp only [intervalIntegral.integral_const_mul, mul_eq_mul_left_iff, mul_eq_zero, div_eq_zero_iff,
    neg_eq_zero, one_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
  left
  calc ∫ (x : ℝ) in t1..t2, cos (2 * (S.ω * x + S.phase IC))
    _ = ∫ (x : ℝ) in t1..t2, cos ((2 * S.ω) * (x + S.phase IC/S.ω)) := by
      congr
      funext t
      congr 1
      field_simp [S.ω_neq_zero]
      ring
    _ = ∫ (x : ℝ) in (t1 + S.phase IC/S.ω)..(t2 + S.phase IC/S.ω), cos (2 * S.ω * x) := by
      rw [intervalIntegral.integral_comp_add_right (b := t2) (a := t1) (fun x => cos (2 * S.ω * x))
        (S.phase IC/S.ω)]
    _ = S.ω⁻¹ * 2⁻¹ * (sin (2 * (S.ω * t2 + S.phase IC)) - sin (2 * (S.ω * t1 + S.phase IC))) := by
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

/- This variable should be removed once the the corresponding `semiformal_result`
  is implemented. -/
variable (EquationOfMotion : (x : Time → ℝ) → Prop)

TODO "6VZI3" "For the classical harmonic oscillator find the time for which it returns to
  it's initial position and velocity."

TODO "6VZJB" "For the classical harmonic oscillator find the times for
  which it passes through zero."

TODO "6VZJH" "For the classical harmonic oscillator find the velocity when it passes through
  zero."

/-- The solutions for any initial condition solve the equation of motion. -/
semiformal_result "6YATB" sol_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion (S.sol IC)

/-- The solutions to the equation of motion for a given set of initial conditions
  are unique.

  Semiformal implmentation:
  - One may needed the added condition of smoothness on `x` here.
  - `EquationOfMotion` needs defining before this can be proved. -/
semiformal_result "6VZJO" sol_unique (IC : InitialConditions) (x : Time → ℝ) :
    EquationOfMotion x ∧ x 0 = IC.x₀ ∧ deriv x 0 = IC.v₀ →
    x = S.sol IC

end HarmonicOscillator

end ClassicalMechanics
