/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.ClassicalMechanics.EulerLagrange
import PhysLean.ClassicalMechanics.HamiltonsEquations
import Mathlib.Tactic.TFAE
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

TODO "6VZHC" "Create a new folder for the damped harmonic oscillator, initially as a place-holder."

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

open MeasureTheory ContDiff InnerProductSpace Time

/-- The kinetic energy of the harmonic oscillator is `1/2 m ‖dx/dt‖^2`. -/
noncomputable def kineticEnergy (xₜ : Time → Space 1) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

@[fun_prop]
lemma kineticEnergy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (kineticEnergy S xₜ) := by
  unfold kineticEnergy
  change Differentiable ℝ ((fun x => (1 / (2 : ℝ)) * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t))
  apply Differentiable.comp
  · fun_prop
  · exact deriv_differentiable_of_contDiff xₜ hx

lemma kineticEnergy_deriv (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (kineticEnergy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  conv_lhs => simp [Time.deriv]
  change (fderiv ℝ ((fun x => 2⁻¹ * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop)]
  simp
  rw [fderiv_inner_apply]
  simp
  rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right]
  congr 1
  simp
  module
  repeat fun_prop


/-- The potential energy of the harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : Space 1) : ℝ :=
  (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ

@[fun_prop]
lemma potentialEnergy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (fun t => potentialEnergy S (xₜ t)) := by
  unfold potentialEnergy
  change Differentiable ℝ ((fun x => (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ) ∘ xₜ)
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv] at hx
    exact hx.1

lemma potentialEnergy_deriv  (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
     ∂ₜ (fun t => potentialEnergy S (xₜ t)) = fun t => ⟪∂ₜ xₜ t, S.k • xₜ t⟫_ℝ := by
  funext t
  unfold potentialEnergy
  conv_lhs => simp [Time.deriv]
  change (fderiv ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ (fun t => xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp
  rw [fderiv_inner_apply]
  simp
  trans S.k * ⟪xₜ t, ∂ₜ xₜ t⟫_ℝ
  · rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right,
      ← inner_smul_right, ← inner_smul_right]
    congr 1
    module
  rw [real_inner_comm, ← inner_smul_right]
  repeat fun_prop
  apply Differentiable.differentiableAt
  rw [contDiff_infty_iff_fderiv] at hx
  exact hx.1

/-- The energy of the harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (xₜ : Time → Space 1) : Time → ℝ := fun t =>
  kineticEnergy S xₜ t + potentialEnergy S (xₜ t)

lemma energy_eq (xₜ : Time → Space 1) :
    energy S xₜ = fun t => kineticEnergy S xₜ t + potentialEnergy S (xₜ t) := by rfl

@[fun_prop]
lemma energy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (energy S xₜ) := by
  rw [energy_eq]
  fun_prop

lemma energy_deriv  (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (energy S xₜ) = fun t => ⟪∂ₜ xₜ t,  S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq]
  rw [fderiv_fun_add (by fun_prop) (by apply S.potentialEnergy_differentiable xₜ hx)]
  simp
  rw [← Time.deriv_eq, ← Time.deriv_eq]
  rw [potentialEnergy_deriv, kineticEnergy_deriv]
  simp
  rw [← inner_add_right]
  fun_prop
  fun_prop

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

set_option linter.unusedVariables false in
/-- The lagrangian of the harmonic oscillator is the kinetic energy minus the potential energy. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x :  Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    ℝ := 1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - S.potentialEnergy x

set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lagrangian_eq : lagrangian S  = fun t x v =>
    1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ := by
  ext t x v
  simp [lagrangian, potentialEnergy]
  ring

lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time) (xₜ : Time → Space 1)  :
    lagrangian S t (xₜ t) (∂ₜ xₜ t) = kineticEnergy S xₜ t - potentialEnergy S (xₜ t) := by
  rw [lagrangian_eq, kineticEnergy, potentialEnergy]
  simp only [one_div, smul_eq_mul, sub_right_inj]
  ring

lemma gradient_lagrangian_velocity_eq (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    gradient (lagrangian S t x) v = S.m • v := by
  simp [lagrangian_eq]
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : v =  v 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp [smul_smul]
  congr 1
  field_simp
  ring

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
  simp
  congr
  · simp [lagrangian_eq]
    rw [← grad_eq_gradiant, grad_eq_sum]
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
    rw [gradient_lagrangian_velocity_eq]

lemma variational_gradient_action (xₜ : Time → Space 1) (hq : ContDiff ℝ ∞ xₜ) :
    (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = eulerLagrangeOp S xₜ :=
  euler_lagrange_varGradient S.lagrangian xₜ hq S.contDiff_lagrangian

/-- THe equation of motion for the Harmonic oscillator. -/
def EquationOfMotion (xₜ : Time → Space 1) : Prop :=
  eulerLagrangeOp S xₜ = 0

lemma equationOfMotion_iff_eulerLagrangeOp (xₜ : Time → Space 1) :
  S.EquationOfMotion xₜ ↔ eulerLagrangeOp S xₜ = 0 := by rfl

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)) := by
  rw [EquationOfMotion, eulerLagrangeOp_eq_force S xₜ hx, funext_iff]
  simp
  conv_lhs =>
    enter [x]
    rw [sub_eq_zero, eq_comm]

lemma energy_conservation_of_equationOfMotion (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) : ∂ₜ (S.energy xₜ) = 0 := by
  rw [energy_deriv _ _ hx]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx] at h
  funext x
  simp
  rw [h]
  simp [force_eq_linear]

lemma energy_conservation_of_equationOfMotion' (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) (t  : Time) : S.energy xₜ t = S.energy xₜ 0 := by
  have h1 := S.energy_conservation_of_equationOfMotion xₜ hx h
  unfold Time.deriv at h1
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ)
  · exact energy_differentiable S xₜ hx
  intro t
  ext p
  simp
  have hp : p = p.val • 1 := by ext; simp
  rw [hp]
  simp
  right
  rw [funext_iff] at h1
  simpa using h1 t

/-!

## Hamiltonian formulation

-/

noncomputable def toCanonicalMomentum (t : Time) (x : Space 1) :
    EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun v := gradient (S.lagrangian t x ·) v
  invFun p := (1 / S.m) • p
  left_inv v := by
    simp [gradient_lagrangian_velocity_eq]
  right_inv p := by
    simp [gradient_lagrangian_velocity_eq]
  map_add' v1 v2 := by
    simp [gradient_lagrangian_velocity_eq]
  map_smul' c v := by
    simp [gradient_lagrangian_velocity_eq]
    module

lemma toCanonicalMomentum_eq (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    toCanonicalMomentum S t x v = S.m • v := by
  simp [toCanonicalMomentum, gradient_lagrangian_velocity_eq]

noncomputable def hamiltonian (t : Time) (p : EuclideanSpace ℝ (Fin 1))  (x : Space 1) : ℝ :=
  ⟪p, (toCanonicalMomentum S t x).symm p⟫_ℝ - S.lagrangian t x ((toCanonicalMomentum S t x).symm p)

lemma hamiltonian_eq :
    hamiltonian S  = fun _ p x => (1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ + (1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ := by
  funext t x p
  simp [hamiltonian, lagrangian_eq, toCanonicalMomentum, inner_smul_right, inner_smul_left]
  have hm : S.m ≠ 0 := by exact m_neq_zero S
  field_simp
  ring

@[fun_prop]
lemma hamiltonian_contDiff (n : WithTop ℕ∞): ContDiff ℝ n ↿S.hamiltonian := by
  rw [hamiltonian_eq]
  fun_prop

lemma gradient_hamiltonian_momentum_eq (t : Time) (x : Space 1) (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t · x) p = (1 / S.m) • p := by
  rw [hamiltonian_eq]
  simp
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : p =  p 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp
  module

lemma gradient_hamiltonian_position_eq (t : Time) (x : Space 1) (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t p) x = S.k • x := by
  rw [hamiltonian_eq]
  simp
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : x =  x 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp
  module

lemma hamiltonian_eq_energy (xₜ : Time → Space 1) :
    (fun t => hamiltonian S t (toCanonicalMomentum S t (xₜ t) (∂ₜ xₜ t)) (xₜ t)) = energy S xₜ := by
  funext t
  rw [hamiltonian]
  simp [toCanonicalMomentum_eq, lagrangian, energy, kineticEnergy]
  simp [toCanonicalMomentum, inner_smul_left]
  ring

noncomputable def hamiltonEqOp  (p : Time → EuclideanSpace ℝ (Fin 1)) (q : Time → Space 1)  :=
  ClassicalMechanics.hamiltonEqOp (hamiltonian S) p q

lemma equationOfMotion_iff_hamiltonEqOp_eq_zero (xₜ : Time → Space 1)  (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0 := by
  rw [hamiltonEqOp, hamiltonEqOp_eq_zero_iff_hamiltons_equations]
  simp [toCanonicalMomentum_eq, gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx]
  conv_rhs => enter[t]; rw [Time.deriv_smul _ _ (by fun_prop)]
  simp [force_eq_linear]


/-!

## Results equivalent to EquationOfMotion

-/

lemma equationOfMotion_tfae  (xₜ : Time → Space 1)  (hx : ContDiff ℝ ∞ xₜ) :
    List.TFAE [S.EquationOfMotion xₜ,
      (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)),
      hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0,
      (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = 0,
      (δ (pq':= fun t => (S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t), xₜ t)),
        ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - S.hamiltonian t (pq' t).1 (pq' t).2) = 0] := by
  rw [← equationOfMotion_iff_hamiltonEqOp_eq_zero, ← equationOfMotion_iff_newtons_2nd_law]
  rw [hamiltons_equations_varGradient, euler_lagrange_varGradient]
  simp
  erw [← equationOfMotion_iff_eulerLagrangeOp]
  simp
  erw [← equationOfMotion_iff_hamiltonEqOp_eq_zero]
  simp
  repeat fun_prop
  simp [toCanonicalMomentum_eq]
  repeat fun_prop


end HarmonicOscillator

end ClassicalMechanics
