/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.ClassicalMechanics.EulerLagrange
/-!

# The Classical Harmonic Oscillator

## Description

The classical harmonic oscillator is a classical mechanics system.
It physically corresponds to a particle of mass `m` attached to a spring providing a force of
`- k x`.

## Current status

**Basic**

The main components of the basic module (this module) are:
- The structure `HarmonicOscillator` containing the physical parameters of the system.
- The definition of the lagrangian `lagrangian` of the system.

**Solution**

The main components of the `Solution` module are:
- The structure `InitialConditions` containing the initial conditions of the system.
- The definition `sol` which given a set of initial conditions is the solution
  to the Harmonic Oscillator.
- The energy `sol_energy` of each solution.
- The action `sol_action` of each solution.

## TODOs

There are a number of TODOs related to the classical harmonic oscillator. These include:
- 6VZG4: Deriving the Euler-Lagrange equations.
- 6YATB: Show that the solutions satisfy the equations of motion (the Euler-Lagrange equations).
- 6VZHC: Include damping into the harmonic oscillator.

Note the item TODO 6YATB. In particular it is yet to be shown that the solutions satisfy
the equation of motion.

-/

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

/-- The classical harmonic oscillator is specified by a mass `m`, and a spring constant `k`.
  Both the mass and the string constant are assumed to be positive. -/
structure HarmonicOscillator where
  /-- The mass of the harmonic Oscillator. -/
  m : ℝ
  /-- The spring constant of the harmonic oscillator. -/
  k : ℝ
  m_pos : 0 < m
  k_pos : 0 < k

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

@[simp]
lemma k_neq_zero : S.k ≠ 0 := Ne.symm (ne_of_lt S.k_pos)

@[simp]
lemma m_neq_zero : S.m ≠ 0 := Ne.symm (ne_of_lt S.m_pos)

/-- The angular frequence of the classical harmonic osscilator, `ω`, is defined
  as `√(k/m)`. -/
noncomputable def ω : ℝ := √(S.k / S.m)

/-- The angular frequence of the classical harmonic osscilator is positive. -/
@[simp]
lemma ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

/-- The square of the angular frequence of the classical harmonic osscilator is equal to `k/m`. -/
lemma ω_sq : S.ω^2 = S.k / S.m := by
  rw [ω, sq_sqrt]
  exact div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)

/-- The angular frequence of the classical harmonic osscilator is not equal to zero. -/
lemma ω_neq_zero : S.ω ≠ 0 := Ne.symm (ne_of_lt S.ω_pos)

/-- The inverse of the square of the angular frequence of the classical harmonic osscilator
  is `m/k`. -/
lemma inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.m/S.k := by
  rw [ω_sq]
  field_simp

open Time

/-!

## The energies of the harmonic oscillator

We define the kinetic energy, potential energy, total energy of the harmonic oscillator.

-/

/-- The kinetic energy of the harmonic oscillator is `1/2 m ‖dx/dt‖^2`. -/
noncomputable def kineticEnergy (xₜ : Time → Space 1) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

/-- The potential energy of the harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : Space 1) : ℝ :=
  (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ

/-- The energy of the harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (xₜ : Time → Space 1) : Time → ℝ := fun t =>
  kineticEnergy S xₜ t + potentialEnergy S (xₜ t)

/-!

## The force

-/

/-- The force of the classical harmonic oscillator defined as `- dU(x)/dx` where `U(x)`
  is the potential energy. -/
noncomputable def force (S : HarmonicOscillator) (x : Space 1) : EuclideanSpace ℝ (Fin 1) :=
  - ∇ (potentialEnergy S) x

/-- The force on the classical harmonic oscillator is `- k x`. -/
lemma force_eq_linear (x : Space 1) : force S x = - S.k • x := by
  unfold force potentialEnergy
  change -∇ ((1 / (2 : ℝ)) • S.k • (fun (x : Space 1) => ⟪x, x⟫_ℝ)) x = -S.k • x
  rw [grad_smul, grad_smul]
  · rw [grad_inner]
    simp only [Pi.smul_apply, neg_smul, neg_inj, smul_smul]
    simp only [mul_smul]
    rw [smul_comm]
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀]
  · simp only [inner_differentiable]
  · simp only [Differentiable.const_smul, inner_differentiable]

/-!

## The equation of motion

-/

open MeasureTheory ContDiff InnerProductSpace Time

set_option linter.unusedVariables false in
/-- The lagrangian of the harmonic oscillator is the kinetic energy minus the potential energy. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x :  Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
   ℝ :=
  1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ

set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lagrangian_eq :
   lagrangian S  = fun t x v =>
  1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ := by rfl

@[fun_prop]
lemma contDiff_lagrangian : ContDiff ℝ ∞ ↿S.lagrangian  := by
  rw [lagrangian_eq]
  fun_prop

/-- The Euler-Lagrange operator for the classical harmonic osscilator. -/
noncomputable def eulerLagrangeOp (xₜ : Time → Space 1) : Time → Space 1 :=
  ClassicalMechanics.eulerLagrangeOp (lagrangian S) xₜ

lemma eulerLagrangeOp_eq (xₜ : Time → Space 1) :
    eulerLagrangeOp S xₜ = fun t => gradient (S.lagrangian t · (∂ₜ xₜ t)) (xₜ t)
    - ∂ₜ (fun t' => gradient (S.lagrangian t' (xₜ t') ·) (∂ₜ xₜ t')) t := by
  rw [eulerLagrangeOp, ClassicalMechanics.eulerLagrangeOp_eq]

/-- The Euler lagrange operator corresponds to Newton's second law. -/
lemma eulerLagrangeOp_eq_force (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    eulerLagrangeOp S xₜ = fun t => force S (xₜ t) - S.m • ∂ₜ (∂ₜ xₜ) t := by
  funext t
  rw [eulerLagrangeOp_eq]
  simp [lagrangian_eq]
  congr
  · rw [← grad_eq_gradiant, grad_eq_sum]
    simp [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
    simp
    rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self, force_eq_linear]
    have hx : xₜ t =  xₜ t 0 • basis 0 := by
      ext i
      fin_cases i
      simp
    rw [hx]
    simp [smul_smul]
    congr 1
    field_simp
    ring
  · rw [← Time.deriv_smul _ _ (by fun_prop)]
    congr
    funext t
    rw [← grad_eq_gradiant, grad_eq_sum]
    simp [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
    simp
    rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
    have hx : ∂ₜ xₜ t =  ∂ₜ xₜ t 0 • basis 0 := by
      ext i
      fin_cases i
      simp
    rw [hx]
    simp [smul_smul]
    congr 1
    field_simp
    ring

lemma variational_gradient_action (xₜ : Time → Space 1) (hq : ContDiff ℝ ∞ xₜ) :
    (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = eulerLagrangeOp S xₜ :=
  euler_lagrange_varGradient S.lagrangian xₜ hq S.contDiff_lagrangian

/-- THe equation of motion for the Harmonic oscillator. -/
def EquationOfMotion (xₜ : Time → Space 1) : Prop :=
  eulerLagrangeOp S xₜ = 0


TODO "6VZHC" "Create a new folder for the damped harmonic oscillator, initially as a place-holder."

end HarmonicOscillator

end ClassicalMechanics
