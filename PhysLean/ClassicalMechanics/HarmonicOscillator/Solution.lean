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
import PhysLean.Units.Basic
/-!

# Solutions to the classical harmonic oscillator

-/

namespace ClassicalMechanics
open Real Time

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

/-!

## The solution for given initial conditions

-/

/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity. -/
structure InitialConditions where
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
noncomputable def sol (IC : InitialConditions) : Time → Space 1 := fun t =>
  cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀

lemma sol_eq (IC : InitialConditions) :
    S.sol IC = fun t : Time => cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀ := rfl

/-- For zero initial conditions, the solution is zero. -/
lemma sol_zeroIC : S.sol zeroIC = fun _ => 0 := by
  simp [sol_eq]

/-!

## Differentiability of the solution

-/

@[fun_prop]
lemma sol_contDiff (S : HarmonicOscillator) (IC : InitialConditions) {n : WithTop ℕ∞} :
    ContDiff ℝ n (S.sol IC) := by
  rw [sol_eq]
  apply ContDiff.add
  apply ContDiff.smul  _ contDiff_const
  · change  ContDiff ℝ _ (((fun x => cos x) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
    refine ContDiff.comp_continuousLinearMap (ContDiff.comp contDiff_cos ?_)
    fun_prop
  apply ContDiff.smul _ contDiff_const
  · have hx := contDiff_sin (n := n)
    change ContDiff ℝ _ (((fun x => sin x / S.ω) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
    refine ContDiff.comp_continuousLinearMap (ContDiff.comp ?_ ?_)
    · fun_prop
    · fun_prop
/-!

## Derivatives of the solution

-/

lemma sol_velocity (IC : InitialConditions) : ∂ₜ (S.sol IC) =
    fun t : Time => - S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [sol_eq, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  simp only
  rw [fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  have h1 : (fderiv ℝ (fun t => sin (S.ω * t.val) / S.ω) t) =
    (1/ S.ω) • (fderiv ℝ (fun t => sin (S.ω * t.val)) t) := by
    rw [← fderiv_mul_const]
    congr
    funext t
    field_simp
    fun_prop
  simp [h1]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp
  ring_nf
  rw [← mul_smul, mul_rotate, NonUnitalRing.mul_assoc]
  field_simp [mul_div_assoc, div_self, mul_one, S.ω_neq_zero]


lemma sol_acceleration (IC : InitialConditions) : ∂ₜ (∂ₜ (S.sol IC)) =
    fun t : Time => - S.ω^2 • cos (S.ω * t.val) • IC.x₀ - S.ω • sin (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [sol_velocity, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  simp only
  rw [fderiv_smul_const (by fun_prop), fderiv_fun_const_smul (by fun_prop),
    fderiv_smul_const (by fun_prop)]
  simp
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp [smul_smul]
  ring_nf
  module

/-!

## The initial conditions of the solution

-/

/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma sol_apply_zero (IC : InitialConditions) : S.sol IC 0 = IC.x₀ := by
  simp [sol]


@[simp]
lemma sol_velocity_apply_zero (IC : InitialConditions) : ∂ₜ (S.sol IC) 0 = IC.v₀ := by
  simp [sol_velocity]

/-!

## Equation of motion

The solution satisfies the equation of motion.

-/

lemma sol_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion S (S.sol IC) := by
  rw [EquationOfMotion, eulerLagrangeOp_eq_force]
  funext t
  simp
  rw [sol_acceleration, force_eq_linear]
  simp [sol_eq]
  funext i
  simp
  rw [ω_sq]
  have h : S.ω ≠ 0 := by exact ω_neq_zero S
  field_simp
  ring_nf
  rw [ω_sq]
  field_simp
  fun_prop


/-!

## Velocity equal to zero

-/

lemma tan_time_eq_of_sol_velocity_eq_zero (IC : InitialConditions) (t : Time)
   (h : ∂ₜ (S.sol IC) t = 0) (hx : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    tan (S.ω * t) = IC.v₀ 0 / (S.ω * IC.x₀ 0) := by
  rw [sol_velocity] at h
  simp at h
  have hx : S.ω ≠ 0 := by exact ω_neq_zero S
  by_cases h1 : IC.x₀ ≠ 0
  by_cases h2 : IC.v₀ ≠ 0
  have h1' : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply h1
    funext i
    fin_cases i
    simp [hn]
  have hcos : cos (S.ω * t.val)  ≠ 0 := by
    by_contra hn
    rw [hn] at h
    rw [Real.cos_eq_zero_iff_sin_eq] at hn
    simp_all
  rw [tan_eq_sin_div_cos]
  field_simp
  trans (sin (S.ω * t.val) * (S.ω * IC.x₀ 0)) +
    (-(S.ω • sin (S.ω * t.val) • IC.x₀) + cos (S.ω * t.val) • IC.v₀) 0
  · rw [h]
    simp
  · simp
    ring
  simp at h2
  rw [h2] at h ⊢
  simp_all
  simp [tan_eq_sin_div_cos, h]
  simp at h1
  rw [h1] at h ⊢
  simp_all
  simp [tan_eq_sin_div_cos, h]


lemma sol_velocity_eq_zero_at_arctan (IC : InitialConditions) (hx : IC.x₀ ≠ 0) :
    (∂ₜ (S.sol IC)) (arctan (IC.v₀ 0 / (S.ω * IC.x₀ 0)) / S.ω) = 0  := by
  rw [sol_velocity]
  simp
  have hx' : S.ω ≠ 0 := by exact ω_neq_zero S
  field_simp
  rw [Real.sin_arctan, Real.cos_arctan]
  funext i
  fin_cases i
  simp
  trans  (-(S.ω * (IC.v₀ 0 / (S.ω * IC.x₀ 0)  * IC.x₀ 0)) + IC.v₀ 0) *  (√(1 + (IC.v₀ 0 / (S.ω * IC.x₀ 0)) ^ 2))⁻¹
  · ring
  simp
  left
  field_simp
  have hx : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply hx
    funext i
    fin_cases i
    simp [hn]
  field_simp
  ring

@[sorryful]
lemma sol_velocity_eq_zero_iff (IC : InitialConditions) (t : Time)
    (hx : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    ∂ₜ (S.sol IC) t = 0 ↔ (S.sol IC) t = √(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) • Space.basis 0 := by
  sorry

/-!

## The energy of the solution

-/

@[sorryful]
lemma sol_energy (IC : InitialConditions) : S.energy (S.sol IC) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  sorry

/-!

## Some semi-formal results

-/

TODO "6VZI3" "For the classical harmonic oscillator find the time for which it returns to
  it's initial position and velocity."

TODO "6VZJB" "For the classical harmonic oscillator find the times for
  which it passes through zero."


/-- The solutions to the equation of motion for a given set of initial conditions
  are unique.

  Semiformal implmentation:
  - One may needed the added condition of smoothness on `x` here.
  - `EquationOfMotion` needs defining before this can be proved. -/
@[sorryful]
lemma sol_unique (IC : InitialConditions) (x : Time → Space 1) :
    S.EquationOfMotion x ∧ x 0 = IC.x₀ ∧ ∂ₜ x 0 = IC.v₀ →
    x = S.sol IC := by sorry

end HarmonicOscillator

end ClassicalMechanics
