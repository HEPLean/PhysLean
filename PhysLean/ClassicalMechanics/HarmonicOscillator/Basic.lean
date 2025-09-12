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

## i. Description

The classical harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a force `- k x` where `k` is the spring constant and `x` is the position.

## ii. Summary of the key results

The key results in the study of the classical harmonic oscillator are the follows:

In the `Basic` module:
- `HarmonicOscillator` contains the input data to the problem.
- `EquationOfMotion` defines the equation of motion for the harmonic oscillator.
- `energy_conservation_of_equationOfMotion` proves that a trajectory satisfying the
  equation of motion conserves energy.
- `equationOfMotion_tfae` proves that the equation of motion of motion is equivalent to
  - Newton's second law,
  - Hamilton's equations,
  - the variational principal for the action,
  - the Hamilton variation principal.

In the `Solution` module:
- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `sol` is the solution to the harmonic oscillator for given initial conditions.
- `sol_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of content for this module

- A. The input data
- B. The angular frequency
- C. The energies
- D. Lagrangian and the equation of motion
- E. Newton's second law
- F. Energy conservation
- G. Hamiltonian formulation
- H. Equivalences between the different formulations of the equations of motion

## iiv. References

References for the classical harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 58, section 21.

-/

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

TODO "6VZHC" "Create a new folder for the damped harmonic oscillator, initially as a place-holder."

/-!

## A. The input data

We start by defining a structure containing the input data of the harmonic oscillator, and
proving basic properties thereof. The input data consists of the mass `m`
of the particle and the spring constant `k`.

-/

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

/-!

## B. The angular frequency

From the input data, it is possible to define the angular frequency `ω` of the harmonic oscillator,
as `√(k/m)`.

The angular frequency appears in the solutions to the equations of motion of the harmonic
oscillator.

Here we both define and proof properties related to the angular frequency.

-/

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

/-!

## C. The energies

The harmonic oscillator has a kinetic energy determined by it's velocity and
a potential energy deetermined by it's position.
These combine to give the total energy of the harmonic oscillator.

Here we state and prove a number of properties of these energies.

-/

open MeasureTheory ContDiff InnerProductSpace Time

/-!

### C.1. The definitions of the energies

We define the three energies, it is these energies which will control the dynamics
of the harmonic oscillator, through the lagrangian.

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

### C.2. Simple equalties for the energies

-/

lemma kineticEnergy_eq (xₜ : Time → Space 1) :
    kineticEnergy S xₜ = fun t => (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ:= by rfl

lemma potentialEnergy_eq (x : Space 1) :
    potentialEnergy S x = (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ:= by rfl

lemma energy_eq (xₜ : Time → Space 1) :
    energy S xₜ = fun t => kineticEnergy S xₜ t + potentialEnergy S (xₜ t) := by rfl
/-!

### C.2. Differentiability of the energies

On smooth trajectories the energies are differentiable.

-/
@[fun_prop]
lemma kineticEnergy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (kineticEnergy S xₜ) := by
  rw [kineticEnergy_eq]
  change Differentiable ℝ ((fun x => (1 / (2 : ℝ)) * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t))
  apply Differentiable.comp
  · fun_prop
  · exact deriv_differentiable_of_contDiff xₜ hx

@[fun_prop]
lemma potentialEnergy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (fun t => potentialEnergy S (xₜ t)) := by
  simp [potentialEnergy_eq]
  change Differentiable ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ xₜ)
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv] at hx
    exact hx.1

@[fun_prop]
lemma energy_differentiable (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (energy S xₜ) := by
  rw [energy_eq]
  fun_prop

/-!

### C.3. Time derivatives of the energies

For a general smooth trajectory (which may not satisfy the equations of motion) we can compute
the time derivatives of the energies.

-/

lemma kineticEnergy_deriv (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (kineticEnergy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  conv_lhs => simp [Time.deriv]
  change (fderiv ℝ ((fun x => 2⁻¹ * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
  rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right]
  congr 1
  simp only [smul_add]
  module
  repeat fun_prop

lemma potentialEnergy_deriv (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (fun t => potentialEnergy S (xₜ t)) = fun t => ⟪∂ₜ xₜ t, S.k • xₜ t⟫_ℝ := by
  funext t
  unfold potentialEnergy
  conv_lhs => simp [Time.deriv]
  change (fderiv ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ (fun t => xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
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

lemma energy_deriv (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (energy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq]
  rw [fderiv_fun_add (by fun_prop) (by apply S.potentialEnergy_differentiable xₜ hx)]
  simp only [ContinuousLinearMap.add_apply]
  rw [← Time.deriv_eq, ← Time.deriv_eq]
  rw [potentialEnergy_deriv, kineticEnergy_deriv]
  simp only
  rw [← inner_add_right]
  fun_prop
  fun_prop

/-!

## D. Lagrangian and the equation of motion

We state the lagrangian, and derive from that the equation of motion for the harmonic oscillator.

-/

/-!
### D.1. The Lagrangian

We define the lagrangian of the harmonic oscillator, as a function of phase-space.

In theory this definition is the kinetic energy minus the potential energy, however
to make the lagrangian a function on phase-space we reserve this result for a lemma.

-/

set_option linter.unusedVariables false in
/-- The lagrangian of the harmonic oscillator is the kinetic energy minus the potential energy. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    ℝ := 1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - S.potentialEnergy x

/-!

#### Part D.1.I

Equalitites for the lagrangian. We prove some simple equalities for the lagrangian,
in particular that when applied to a trajectory it is the kinetic energy minus the potential energy.

-/

set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lagrangian_eq : lagrangian S = fun t x v =>
    1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ := by
  ext t x v
  simp [lagrangian, potentialEnergy]
  ring

lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time) (xₜ : Time → Space 1) :
    lagrangian S t (xₜ t) (∂ₜ xₜ t) = kineticEnergy S xₜ t - potentialEnergy S (xₜ t) := by
  rw [lagrangian_eq, kineticEnergy, potentialEnergy]
  simp only [one_div, smul_eq_mul, sub_right_inj]
  ring

/-!

#### Part D.1.II

The lagrangian is smooth in all its arguments.

-/

@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  rw [lagrangian_eq]
  fun_prop

/-!

#### Part D.1.III

We now show results related to the gradients of the lagrangian with respect to the
position and velocity.

-/

lemma gradient_lagrangian_position_eq (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => lagrangian S t x v) x = - S.k • x := by
  simp [lagrangian_eq]
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_sub, Fin.isValue, ContinuousLinearMap.neg_apply,
    neg_smul, neg_inj]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : x = x 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp [smul_smul]
  congr 1
  field_simp
  ring

lemma gradient_lagrangian_velocity_eq (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    gradient (lagrangian S t x) v = S.m • v := by
  simp [lagrangian_eq]
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, sub_zero, Fin.isValue]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : v = v 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp [smul_smul]
  congr 1
  field_simp
  ring

/-!

### D.2. The Euler-Lagrange operator

We now write down the Euler-Lagrange operator for the harmonic oscillator.
Setting this equal to zero corresponds to the Euler-Lagrange equations, and thereby the
equation of motion.

-/

/-- The Euler-Lagrange operator for the classical harmonic osscilator. -/
noncomputable def eulerLagrangeOp (xₜ : Time → Space 1) : Time → Space 1 :=
  ClassicalMechanics.eulerLagrangeOp (lagrangian S) xₜ

/-!

#### Part D.2.I

Basic equaltities for the Euler-Lagrange operator.

-/

lemma eulerLagrangeOp_eq (xₜ : Time → Space 1) :
    eulerLagrangeOp S xₜ = fun t => gradient (S.lagrangian t · (∂ₜ xₜ t)) (xₜ t)
    - ∂ₜ (fun t' => gradient (S.lagrangian t' (xₜ t') ·) (∂ₜ xₜ t')) t := by
  rw [eulerLagrangeOp, ClassicalMechanics.eulerLagrangeOp_eq]

/-!

#### Part D.2.II

Relation of the Euler-Lagrange operator to variational derivative of the action.

-/

lemma variational_gradient_action (xₜ : Time → Space 1) (hq : ContDiff ℝ ∞ xₜ) :
    (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = eulerLagrangeOp S xₜ :=
  euler_lagrange_varGradient S.lagrangian xₜ hq (S.contDiff_lagrangian _)

/-!

### Part D.3. The equation of motion

The equation of motion for the harmonic oscillator is given by setting the
Euler-Lagrange operator equal to zero.

-/

/-- THe equation of motion for the Harmonic oscillator. -/
def EquationOfMotion (xₜ : Time → Space 1) : Prop :=
  eulerLagrangeOp S xₜ = 0

/-!

#### Part D.3.I.

We write a simple iff statment for the definition of the equation of motions.

-/

lemma equationOfMotion_iff_eulerLagrangeOp (xₜ : Time → Space 1) :
    S.EquationOfMotion xₜ ↔ eulerLagrangeOp S xₜ = 0 := by rfl

/-!

## E. Newton's second law

We define the force of the harmonic oscillator, and show that the equation of
motion is equivalent to Newton's second law.

-/

/-!

### E.1. The force

We define the force of the harmoic oscillator as the negative gradient of the potential energy,
and show that this is equal to `- k x`.

-/

/-- The force of the classical harmonic oscillator defined as `- dU(x)/dx` where `U(x)`
  is the potential energy. -/
noncomputable def force (S : HarmonicOscillator) (x : Space 1) : EuclideanSpace ℝ (Fin 1) :=
  - ∇ (potentialEnergy S) x

/-!

#### part E.1.I

We now show that the force is equal to `- k x`.

-/

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

### E.2. Euler-Lagrange operator and force

We relate the Euler-Lagrange operator to the force, and show the relation
to Newton's second law.

-/

/-- The Euler lagrange operator corresponds to Newton's second law. -/
lemma eulerLagrangeOp_eq_force (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    eulerLagrangeOp S xₜ = fun t => force S (xₜ t) - S.m • ∂ₜ (∂ₜ xₜ) t := by
  funext t
  rw [eulerLagrangeOp_eq]
  simp only
  congr
  · simp [lagrangian_eq]
    rw [← grad_eq_gradiant, grad_eq_sum]
    simp [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_sub, Fin.isValue,
      ContinuousLinearMap.neg_apply, neg_smul]
    rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self, force_eq_linear]
    have hx : xₜ t = xₜ t 0 • basis 0 := by
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

/-!

### E.3. Equation of motion if and only if Newton's second law

We show that the equation of motion is equivalent to Newton's second law.

-/

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)) := by
  rw [EquationOfMotion, eulerLagrangeOp_eq_force S xₜ hx, funext_iff]
  simp only [Pi.zero_apply]
  conv_lhs =>
    enter [x]
    rw [sub_eq_zero, eq_comm]

/-!

### F. Energy conservation

In this section we show that any trajectory satisfying the equation of motion
conserves energy. This result simply follows from the definition of the energies,
and their derivatives, as well as the statement that the equations of motion are equivalent
to Newton's second law.

-/

/-!

#### F.1. Energy conservation in terms of time derivatives

We prove that the time derivative of the energy is zero for any trajectory satisfying
the equation of motion.

-/

lemma energy_conservation_of_equationOfMotion (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) : ∂ₜ (S.energy xₜ) = 0 := by
  rw [energy_deriv _ _ hx]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx] at h
  funext x
  simp only [Pi.zero_apply]
  rw [h]
  simp [force_eq_linear]

/-!

#### F.1. Energy conservation in terms of constant energy

We prove that the energy is constant for any trajectory satisfying the equation of motion.

-/

lemma energy_conservation_of_equationOfMotion' (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) (t : Time) : S.energy xₜ t = S.energy xₜ 0 := by
  have h1 := S.energy_conservation_of_equationOfMotion xₜ hx h
  unfold Time.deriv at h1
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ)
  · exact energy_differentiable S xₜ hx
  intro t
  ext p
  simp only [ContinuousLinearMap.zero_apply]
  have hp : p = p.val • 1 := by ext; simp
  rw [hp]
  simp only [map_smul, smul_eq_mul, mul_eq_zero]
  right
  rw [funext_iff] at h1
  simpa using h1 t

/-!

## G. Hamiltonian formulation

We now turn to the Hamiltonian formulation of the harmonic oscillator.
We define the canonical momentum, the Hamiltonian, and show that the equations of
motion are equivalent to Hamilton's equations.

-/

/-!

### G.1. The canonical momentum

We define the canonical momentum as the gradient of the lagrangian with respect to
the velocity.

-/

/-- The equivalence between velocity and canonical momentum. -/
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

/-!

#### Part G.1.I.

An simple equality for the canonical momentum.

-/

lemma toCanonicalMomentum_eq (t : Time) (x : Space 1) (v : EuclideanSpace ℝ (Fin 1)) :
    toCanonicalMomentum S t x v = S.m • v := by
  simp [toCanonicalMomentum, gradient_lagrangian_velocity_eq]

/-!

### G.2. The Hamiltonian

THe hamiltonian is defined as a function of time, canonical momentum and position, as
```
H = ⟪p, v⟫ - L(t, x, v)
```
where `v` is a function of `p` and `x` through the canonical momentum.

-/

/-- The hamiltonian as a function of time, momentum and position. -/
noncomputable def hamiltonian (t : Time) (p : EuclideanSpace ℝ (Fin 1)) (x : Space 1) : ℝ :=
  ⟪p, (toCanonicalMomentum S t x).symm p⟫_ℝ - S.lagrangian t x ((toCanonicalMomentum S t x).symm p)

/-!

#### Part G.2.I.

We prove a simple equality for the Hamiltonian, to help in computations.

-/

lemma hamiltonian_eq :
    hamiltonian S = fun _ p x => (1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ +
      (1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ := by
  funext t x p
  simp [hamiltonian, lagrangian_eq, toCanonicalMomentum, inner_smul_right, inner_smul_left]
  have hm : S.m ≠ 0 := by exact m_neq_zero S
  field_simp
  ring

/-!

#### Part G.2.II.

We show that the Hamiltonian is smooth in all its arguments.

-/

@[fun_prop]
lemma hamiltonian_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.hamiltonian := by
  rw [hamiltonian_eq]
  fun_prop

/-!

#### Part G.2.II.

We now write down the graidents of the Hamiltonian with respect to the momentum and position.

-/

lemma gradient_hamiltonian_position_eq (t : Time) (x : Space 1) (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t p) x = S.k • x := by
  rw [hamiltonian_eq]
  simp only [one_div]
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : x = x 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp only [Fin.isValue, PiLp.smul_apply, basis_self, smul_eq_mul, mul_one]
  module

lemma gradient_hamiltonian_momentum_eq (t : Time) (x : Space 1) (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t · x) p = (1 / S.m) • p := by
  rw [hamiltonian_eq]
  simp only [one_div]
  rw [← grad_eq_gradiant, grad_eq_sum]
  simp [Space.deriv_eq_fderiv_basis]
  rw [fderiv_const_mul (by fun_prop)]
  simp [← Space.deriv_eq_fderiv_basis, deriv_eq_inner_self]
  have hx : p = p 0 • basis 0 := by
    ext i
    fin_cases i
    simp
  rw [hx]
  simp only [Fin.isValue, PiLp.smul_apply, basis_self, smul_eq_mul, mul_one]
  module

/-!

### G.3. Relation between Hamiltonian and energy

We show that the Hamiltonian, when evaluated on any trajectory, is equal to the energy.
This is independent of whether the trajectory satisfies the equations of motion or not.

-/

lemma hamiltonian_eq_energy (xₜ : Time → Space 1) :
    (fun t => hamiltonian S t (toCanonicalMomentum S t (xₜ t) (∂ₜ xₜ t)) (xₜ t)) = energy S xₜ := by
  funext t
  rw [hamiltonian]
  simp [toCanonicalMomentum_eq, lagrangian, energy, kineticEnergy]
  simp [toCanonicalMomentum, inner_smul_left]
  ring

/-!

### G.3. Hamilton equation operator

We define the operator on momentum-position phase-space whose vanishing is equivalent
to Hamilton's equations.

-/

/-- The operator on the momentum-position phase-space whose vanishing is equivalent to the
  hamilton's equations between the momentum and position. -/
noncomputable def hamiltonEqOp (p : Time → EuclideanSpace ℝ (Fin 1)) (q : Time → Space 1) :=
  ClassicalMechanics.hamiltonEqOp (hamiltonian S) p q

/-!

### G.4. Equation of motion if and only if Hamilton's equations

We show that the equation of motion is equivalent to Hamilton's equations, that is
to the vanishing of the Hamilton equation operator.

-/

lemma equationOfMotion_iff_hamiltonEqOp_eq_zero (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0 := by
  rw [hamiltonEqOp, hamiltonEqOp_eq_zero_iff_hamiltons_equations]
  simp [toCanonicalMomentum_eq, gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx]
  conv_rhs => enter[t]; rw [Time.deriv_smul _ _ (by fun_prop)]
  simp [force_eq_linear]

/-!

## H. Equivalences between the different formulations of the equations of motion

We show that the following are equivalent statements for a smooth trajectory `xₜ`:
- The equation of motion holds. (aka the Euler-Lagrange equations hold.)
- Newton's second law holds.
- Hamilton's equations hold.
- The variational principle for the action holds.
- The Hamilton variational principle holds.

-/

lemma equationOfMotion_tfae (xₜ : Time → Space 1) (hx : ContDiff ℝ ∞ xₜ) :
    List.TFAE [S.EquationOfMotion xₜ,
      (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)),
      hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0,
      (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = 0,
      (δ (pq':= fun t => (S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t), xₜ t)),
        ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - S.hamiltonian t (pq' t).1 (pq' t).2) = 0] := by
  rw [← equationOfMotion_iff_hamiltonEqOp_eq_zero, ← equationOfMotion_iff_newtons_2nd_law]
  rw [hamiltons_equations_varGradient, euler_lagrange_varGradient]
  simp only [List.tfae_cons_self]
  erw [← equationOfMotion_iff_eulerLagrangeOp]
  simp only [List.tfae_cons_self]
  erw [← equationOfMotion_iff_hamiltonEqOp_eq_zero]
  simp only [List.tfae_cons_self, List.tfae_singleton]
  repeat fun_prop
  simp [toCanonicalMomentum_eq]
  repeat fun_prop

end HarmonicOscillator

end ClassicalMechanics
