/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
import PhysLean.Units.Basic
/-!

# Solutions to the classical harmonic oscillator

## i. Overview

In this module we define the solutions to the classical harmonic oscillator,
prove that they satisfy the equation of motion, and prove some properties of the solutions.

## ii. Key results

- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `trajectories` is the trajectories to the harmonic oscillator for given initial conditions.
- `trajectories_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of contents

- A. The initial conditions
  - A.1. Definition of the initial conditions
    - A.1.1. Extensionality lemma
  - A.2. Relation to other types of initial conditions
  - A.3. The zero initial conditions
    - A.3.1. Simple results for the zero initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. The trajectory associated with the initial conditions
    - B.1.1. Definitional equality for the trajectory
  - B.2. The trajectory for zero initial conditions
  - B.3. Smoothness of the trajectories
  - B.4. Velocity of the trajectories
  - B.5. Acceleration of the trajectories
  - B.6. The initial conditions of the trajectories
- C. Trajectories and Equation of motion
  - C.1. Uniqueness of the solutions
- D. The energy of the trajectories
- E. The trajectories at zero velocity
  - E.1. The times at which the velocity is zero
  - E.2. A time when the velocity is zero
  - E.3. The position when the velocity is zero
- F. Some open TODOs

## iv. References

References for the classical harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 58, section 21.

-/

namespace ClassicalMechanics
open Real Time ContDiff

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

/-!

## A. The initial conditions

We define the type of initial conditions for the harmonic oscillator.
The initial conditions are currently defined as an initial position and an initial velocity,
that is the values of the solution and its time derivative at time `0`.

-/
/-!

### A.1. Definition of the initial conditions

We start by defining the type of initial conditions for the harmonic oscillator.

-/

/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity. -/
structure InitialConditions where
  /-- The initial position of the harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!

#### A.1.1. Extensionality lemma

We prove an extensionality lemma for `InitialConditions`.
That is, a lemma which states that two initial conditions are equal if their
initial positions and initial velocities are equal.

-/

@[ext]
lemma InitialConditions.ext {IC₁ IC₂ : InitialConditions} (h1 : IC₁.x₀ = IC₂.x₀)
    (h2 : IC₁.v₀ = IC₂.v₀) : IC₁ = IC₂ := by
  cases IC₁
  cases IC₂
  simp_all

/-!

### A.2. Relation to other types of initial conditions

We relate the initial condition given by an initial position and an initial velocity
to other specifications of initial conditions. This is currently not implemented,
and is a TODO.

-/

TODO "6VZME" "Implement other initial conditions. For example:
- initial conditions at a given time.
- Two positions at different times.
- Two velocities at different times.
And convert them into the type `InitialConditions` above (which may need generalzing a bit
to make this possible)."

/-!

### A.3. The zero initial conditions

The zero initial conditions are the initial conditions with zero initial position
and zero initial velocity.

In the end, we will see that this corresponds to the solution which is identically zero,
i.e. the particle remains at rest at the origin.

-/

namespace InitialConditions

/-- The zero initial condition. -/
instance : Zero InitialConditions := ⟨0, 0⟩

/-!

#### A.3.1. Simple results for the zero initial conditions

Some simple results about the zero initial conditions.

-/
/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zero : x₀ 0 = 0 := rfl

/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zero : v₀ 0 = 0 := rfl

end InitialConditions
/-!

## B. Trajectories associated with the initial conditions

To each initial condition we association a trajectory. We will prove some basic properties
of these trajectories.

Eventually we will show that these trajectories satisfy the equation of motion, for
now we can think of them as some choice of trajectory associated with the initial conditions.

-/

namespace InitialConditions

/-!

### B.1. The trajectory associated with the initial conditions

-/

/-- Given initial conditions, the solution to the classical harmonic oscillator. -/
noncomputable def trajectory (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀

/-!

#### B.1.1. Definitional equality for the trajectory

We show a basic definitional equality for the trajectory.

-/
lemma trajectory_eq (IC : InitialConditions) :
    IC.trajectory S = fun t : Time => cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀ := rfl

/-!

### B.2. The trajectory for zero initial conditions

The trajectory for zero initial conditions is the zero function.

-/

/-- For zero initial conditions, the trajectory is zero. -/
@[simp]
lemma trajectory_zero : trajectory S 0 = fun _ => 0 := by
  simp [trajectory_eq]

/-!

### B.3. Smoothness of the trajectories

The trajectories for any initial conditions are smooth functions of time.

-/

@[fun_prop]
lemma trajectory_contDiff (S : HarmonicOscillator) (IC : InitialConditions) {n : WithTop ℕ∞} :
    ContDiff ℝ n (IC.trajectory S) := by
  rw [trajectory_eq]
  apply ContDiff.add
  apply ContDiff.smul _ contDiff_const
  · change ContDiff ℝ _ (((fun x => cos x) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
    refine ContDiff.comp_continuousLinearMap (ContDiff.comp contDiff_cos ?_)
    fun_prop
  apply ContDiff.smul _ contDiff_const
  · have hx := contDiff_sin (n := n)
    change ContDiff ℝ _ (((fun x => sin x / S.ω) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
    refine ContDiff.comp_continuousLinearMap (ContDiff.comp ?_ ?_)
    · fun_prop
    · fun_prop

/-!

### B.4. Velocity of the trajectories

We give a simplification of the velocity of the trajectory.

-/

lemma trajectory_velocity (IC : InitialConditions) : ∂ₜ (IC.trajectory S) =
    fun t : Time => - S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_eq, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
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
  simp only [fderiv_fun_const, Pi.zero_apply, smul_zero, add_zero, neg_smul,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, fderiv_val,
    smul_eq_mul, mul_one]
  field_simp
  ring_nf
  rw [← mul_smul, mul_rotate, NonUnitalRing.mul_assoc]
  field_simp [mul_div_assoc, div_self, mul_one, S.ω_neq_zero]

/-!

### B.5. Acceleration of the trajectories

We give a simplification of the acceleration of the trajectory.

-/

lemma trajectory_acceleration (IC : InitialConditions) : ∂ₜ (∂ₜ (IC.trajectory S)) =
    fun t : Time => - S.ω^2 • cos (S.ω * t.val) • IC.x₀ - S.ω • sin (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_velocity, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop), fderiv_fun_const_smul (by fun_prop),
    fderiv_smul_const (by fun_prop)]
  simp only [neg_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp [smul_smul]
  simp only [fderiv_fun_const, Pi.ofNat_apply, smul_zero, add_zero, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply, fderiv_val,
    smul_eq_mul, mul_one, neg_smul]
  ring_nf
  module

/-!

### B.6. The initial conditions of the trajectories

We show that, unsurprisingly, the trajectories have the initial conditions
used to define them.

-/

/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma trajectory_position_at_zero (IC : InitialConditions) : IC.trajectory S 0 = IC.x₀ := by
  simp [trajectory]

@[simp]
lemma trajectory_velocity_at_zero (IC : InitialConditions) : ∂ₜ (IC.trajectory S) 0 = IC.v₀ := by
  simp [trajectory_velocity]

/-!

## C. Trajectories and Equation of motion

The trajectories satisfy the equation of motion for the harmonic oscillator.

-/

lemma trajectory_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion S (IC.trajectory S) := by
  rw [EquationOfMotion, gradLagrangian_eq_force]
  funext t
  simp only [Pi.zero_apply]
  rw [trajectory_acceleration, force_eq_linear]
  simp [trajectory_eq]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.zero_apply]
  rw [ω_sq]
  have h : S.ω ≠ 0 := by exact ω_neq_zero S
  field_simp
  ring_nf
  rw [ω_sq]
  field_simp
  simp only [neg_add_cancel, mul_zero]
  fun_prop

/-!

### C.1. Uniqueness of the solutions

We show that the trajectories are the unique solutions to the equation of motion
for the given initial conditions. This is currently a TODO.

-/
/-- The trajectories to the equation of motion for a given set of initial conditions
  are unique.

  Semiformal implementation:
  - One may needed the added condition of smoothness on `x` here.
  - `EquationOfMotion` needs defining before this can be proved. -/
lemma trajectories_unique (IC : InitialConditions) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    S.EquationOfMotion x ∧ x 0 = IC.x₀ ∧ ∂ₜ x 0 = IC.v₀ →
    x = IC.trajectory S := by
  intro h
  rcases h with ⟨hEOM, hx0, hv0⟩

  -- Newton form for x
  have hNewt_x :
      ∀ t, S.m • ∂ₜ (∂ₜ x) t = force S (x t) :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := x) hx).1 hEOM

  -- Newton form for the explicit trajectory
  have hTrajContDiff : ContDiff ℝ ∞ (IC.trajectory S) := by
    -- trajectory_contDiff already exists and is [fun_prop]
    fun_prop

  have hNewt_traj :
      ∀ t, S.m • ∂ₜ (∂ₜ (IC.trajectory S)) t = force S ((IC.trajectory S) t) :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := IC.trajectory S) hTrajContDiff).1
      (trajectory_equationOfMotion S IC)

  -- Define the difference y = x - traj
  set y : Time → EuclideanSpace ℝ (Fin 1) := fun t => x t - IC.trajectory S t with hydef

  have hyContDiff : ContDiff ℝ ∞ y := by
    -- ContDiff closed under subtraction
    simpa [hydef] using hx.sub hTrajContDiff

  -- First derivative of y
  have hy_deriv : ∂ₜ y = fun t => ∂ₜ x t - ∂ₜ (IC.trajectory S) t := by
    funext t
    -- same style as in trajectory_velocity: unfold Time.deriv and use fderiv_fun_sub
    rw [hydef, Time.deriv]
    -- ContDiff implies DifferentiableAt - use this explicitly since fun_prop can't infer it
    -- ContDiff ℝ ∞ f implies ContDiffAt ℝ ∞ f t for any t
    have hx_contDiffAt : ContDiffAt ℝ ∞ x t := hx.contDiffAt
    have htraj_contDiffAt : ContDiffAt ℝ ∞ (IC.trajectory S) t := hTrajContDiff.contDiffAt
    have hx_diff : DifferentiableAt ℝ x t :=
      ContDiffAt.differentiableAt hx_contDiffAt (by norm_num : (1 : ℕ∞) ≤ ∞)
    have htraj_diff : DifferentiableAt ℝ (IC.trajectory S) t :=
      ContDiffAt.differentiableAt htraj_contDiffAt (by norm_num : (1 : ℕ∞) ≤ ∞)
    rw [fderiv_fun_sub hx_diff htraj_diff]
    simp only [ContinuousLinearMap.sub_apply, Time.deriv]

  -- Second derivative of y
  have hy_deriv2 :
      ∂ₜ (∂ₜ y) = fun t => ∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t := by
    funext t
    rw [hy_deriv, Time.deriv]
    -- now differentiate (∂ₜ x - ∂ₜ traj)
    -- use differentiability of time-derivatives from ContDiff
    have hx1 : Differentiable ℝ (fun t => ∂ₜ x t) :=
      deriv_differentiable_of_contDiff x hx
    have htr1 : Differentiable ℝ (fun t => ∂ₜ (IC.trajectory S) t) :=
      deriv_differentiable_of_contDiff (IC.trajectory S) hTrajContDiff
    -- Apply fderiv_fun_sub and use Time.deriv to convert back
    -- Differentiable ℝ f means ∀ x, DifferentiableAt ℝ f x
    -- In Mathlib, Differentiable is defined as ∀ x, DifferentiableAt, so we can apply directly
    have hx1_at : DifferentiableAt ℝ (fun t => ∂ₜ x t) t := hx1 t
    have htr1_at : DifferentiableAt ℝ (fun t => ∂ₜ (IC.trajectory S) t) t := htr1 t
    rw [fderiv_fun_sub hx1_at htr1_at]
    -- Now we need to show fderiv of (fun t => fderiv ℝ x t 1) equals fderiv of (∂ₜ x)
    -- This follows from Time.deriv f t = fderiv ℝ f t 1
    simp only [ContinuousLinearMap.sub_apply]
    rw [Time.deriv, Time.deriv]

  -- Newton form for y (linearity of force)
  have hNewt_y : ∀ t, S.m • ∂ₜ (∂ₜ y) t = force S (y t) := by
    intro t
    have hy2t : ∂ₜ (∂ₜ y) t =
        (∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
      simpa using congrFun hy_deriv2 t

    -- Expand and substitute Newton laws for x and traj, then fold back using force_eq_linear
    calc
      S.m • ∂ₜ (∂ₜ y) t
          = S.m • (∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
              simp [hy2t]
      _   = (S.m • ∂ₜ (∂ₜ x) t) - (S.m • ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
              simp [smul_sub]
      _   = force S (x t) - force S ((IC.trajectory S) t) := by
              simp [hNewt_x t, hNewt_traj t]
      _   = force S (y t) := by
              -- force = -k•x, so it is linear: force(x) - force(traj) = force(x-traj)
              -- and y t = x t - traj t by definition
              simp [hydef, force_eq_linear, smul_sub]

  -- Turn Newton form back into EquationOfMotion for y
  have hEOM_y : S.EquationOfMotion y :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := y) hyContDiff).2 hNewt_y

  -- Initial conditions for y are zero
  have hy0 : y 0 = 0 := by
    -- y 0 = x 0 - traj 0 = IC.x₀ - IC.x₀
    simp [hydef, hx0]

  have hyv0 : ∂ₜ y 0 = 0 := by
    -- ∂ₜ y 0 = ∂ₜ x 0 - ∂ₜ traj 0 = IC.v₀ - IC.v₀
    rw [congr_fun hy_deriv 0]
    rw [hv0, trajectory_velocity_at_zero S IC]
    simp

  -- Energy at time 0 is 0
  have hE0 : S.energy y 0 = 0 := by
    -- unfold energy, kinetic, potential and use hy0, hyv0
    simp [HarmonicOscillator.energy, HarmonicOscillator.kineticEnergy,
      HarmonicOscillator.potentialEnergy, hy0, hyv0, one_div, smul_eq_mul]

  -- Energy is constant, hence always 0
  have hE : ∀ t, S.energy y t = 0 := by
    intro t
    have ht := S.energy_conservation_of_equationOfMotion' (xₜ := y) hyContDiff hEOM_y t
    simpa [hE0] using ht

  -- From energy=0 and positivity => y(t)=0
  have hy_all : ∀ t, y t = 0 := by
    intro t
    have hEt : S.energy y t = 0 := hE t

    have hk_nonneg : 0 ≤ S.kineticEnergy y t := by
      unfold HarmonicOscillator.kineticEnergy
      have hcoeff : 0 ≤ (1 / (2 : ℝ)) * S.m := by
        exact mul_nonneg (by norm_num) (le_of_lt S.m_pos)
      -- Use the same approach as for potential energy below
      have hin : 0 ≤ inner ℝ (∂ₜ y t) (∂ₜ y t) := by
        -- For EuclideanSpace ℝ (Fin 1), inner product with itself is nonnegative
        exact real_inner_self_nonneg (x := ∂ₜ y t)
      exact mul_nonneg hcoeff hin

    have hp_nonneg : 0 ≤ S.potentialEnergy (y t) := by
      unfold HarmonicOscillator.potentialEnergy
      -- potentialEnergy = (1/2) * k * ⟪y,y⟫
      simp only [one_div, smul_eq_mul]
      -- Goal is 0 ≤ 2⁻¹ * (S.k * inner ℝ (y t) (y t))
      apply mul_nonneg
      · norm_num -- 0 ≤ 2⁻¹
      · -- 0 ≤ S.k * inner ℝ (y t) (y t)
        have hk_pos : 0 ≤ S.k := le_of_lt S.k_pos
        have hin : 0 ≤ inner ℝ (y t) (y t) := by
          -- For EuclideanSpace ℝ (Fin 1), inner product with itself is nonnegative
          exact real_inner_self_nonneg (x := y t)
        exact mul_nonneg hk_pos hin

    have hp_le : S.potentialEnergy (y t) ≤ S.energy y t := by
      unfold HarmonicOscillator.energy
      exact le_add_of_nonneg_left hk_nonneg

    have hp0 : S.potentialEnergy (y t) = 0 := by
      have : S.potentialEnergy (y t) ≤ 0 := by
        calc
          S.potentialEnergy (y t) ≤ S.energy y t := hp_le
          _ = 0 := hEt
      exact le_antisymm this hp_nonneg

    -- extract ⟪y,y⟫ = 0 from potentialEnergy = 0, then y=0
    have hy_inner0 : inner ℝ (y t) (y t) = 0 := by
      -- potentialEnergy = (1/2) * k * ⟪y,y⟫
      have hmul : ((1 / (2 : ℝ)) * S.k) * inner ℝ (y t) (y t) = 0 := by
        simpa [HarmonicOscillator.potentialEnergy, one_div, smul_eq_mul, mul_assoc] using hp0
      have hcoeff : ((1 / (2 : ℝ)) * S.k) ≠ 0 := by
        exact mul_ne_zero (by norm_num) (S.k_neq_zero)
      rcases mul_eq_zero.mp hmul with hcoeff0 | hinner
      · exact (False.elim (hcoeff hcoeff0))
      · exact hinner

    exact (inner_self_eq_zero.mp hy_inner0)

  -- Conclude x = traj
  funext t
  have : y t = 0 := hy_all t
  -- y t = x t - traj t
  simpa [hydef] using (sub_eq_zero.mp this)

/-!

## D. The energy of the trajectories

For a given set of initial conditions, the energy of the trajectory is constant,
due to the conservation of energy. Here we show it's value.

-/

lemma trajectory_energy (IC : InitialConditions) : S.energy (IC.trajectory S) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy_conservation_of_equationOfMotion' _ _ (by fun_prop) (trajectory_equationOfMotion S IC)]
  simp [energy, kineticEnergy, potentialEnergy]
  ring

/-!

## E. The trajectories at zero velocity

We study the properties of the trajectories when the velocity is zero.

-/

/-!

### E.1. The times at which the velocity is zero

We show that if the velocity of the trajectory is zero, then the time satisfies
the condition that
```
tan (S.ω * t) = IC.v₀ 0 / (S.ω * IC.x₀ 0)
```

-/
lemma tan_time_eq_of_trajectory_velocity_eq_zero (IC : InitialConditions) (t : Time)
    (h : ∂ₜ (IC.trajectory S) t = 0) (hx : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    tan (S.ω * t) = IC.v₀ 0 / (S.ω * IC.x₀ 0) := by
  rw [trajectory_velocity] at h
  simp at h
  have hx : S.ω ≠ 0 := by exact ω_neq_zero S
  by_cases h1 : IC.x₀ ≠ 0
  by_cases h2 : IC.v₀ ≠ 0
  have h1' : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply h1
    ext i
    fin_cases i
    simp [hn]
  have hcos : cos (S.ω * t.val) ≠ 0 := by
    by_contra hn
    rw [hn] at h
    rw [Real.cos_eq_zero_iff_sin_eq] at hn
    simp_all
  rw [tan_eq_sin_div_cos]
  field_simp
  trans (sin (S.ω * t.val) * (S.ω * IC.x₀ 0)) +
    (-(S.ω • sin (S.ω * t.val) • IC.x₀) + cos (S.ω * t.val) • IC.v₀) 0
  · rw [h]
    simp only [Fin.isValue, PiLp.zero_apply, add_zero]
    ring
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

/-!

### E.2. A time when the velocity is zero

We show that as long as the initial position is non-zero, then at
the time `arctan (IC.v₀ 0 / (S.ω * IC.x₀ 0)) / S.ω` the velocity is zero.

-/

lemma trajectory_velocity_eq_zero_at_arctan (IC : InitialConditions) (hx : IC.x₀ ≠ 0) :
    (∂ₜ (IC.trajectory S)) (arctan (IC.v₀ 0 / (S.ω * IC.x₀ 0)) / S.ω) = 0 := by
  rw [trajectory_velocity]
  simp only [Fin.isValue, neg_smul]
  have hx' : S.ω ≠ 0 := by exact ω_neq_zero S
  field_simp
  rw [Real.sin_arctan, Real.cos_arctan]
  ext i
  fin_cases i
  simp only [Fin.isValue, one_div, Fin.zero_eta, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.zero_apply]
  trans (-(S.ω * (IC.v₀ 0 / (S.ω * IC.x₀ 0) * IC.x₀ 0)) + IC.v₀ 0) *
    (√(1 + (IC.v₀ 0 / (S.ω * IC.x₀ 0)) ^ 2))⁻¹
  · ring
  simp only [Fin.isValue, mul_eq_zero, inv_eq_zero]
  left
  field_simp
  have hx : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply hx
    ext i
    fin_cases i
    simp [hn]
  field_simp
  ring

/-!

### E.3. The position when the velocity is zero

We show that the position is equal to `√(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) ` when
the velocity is zero.

-/

lemma trajectory_velocity_eq_zero_iff (IC : InitialConditions) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
    ‖(IC.trajectory S) t‖ = √(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) := by
  have := by exact energy_eq S (trajectory S IC)
  have h_energy_t := congrFun this t
  simp only [kineticEnergy_eq, one_div, potentialEnergy_eq, smul_eq_mul] at h_energy_t
  rw [real_inner_self_eq_norm_sq (trajectory S IC t)] at h_energy_t
  have := by exact trajectory_energy S IC
  have h_init := congrFun this t
  have h_ω := by exact ω_sq S
  constructor
  · intro h_partial
    rw [h_partial, inner_zero_left, mul_zero, zero_add] at h_energy_t
    have h₁ : ‖trajectory S IC t‖ ^ 2 = S.energy (trajectory S IC) t * 2 * (1 / S.k) := by
      simp [h_energy_t]
      field_simp
    symm
    refine (sqrt_eq_iff_mul_self_eq ?_ ?_).mpr ?_
    · apply add_nonneg <;> apply sq_nonneg
    · apply norm_nonneg
    rw [← pow_two]
    rw [h₁, h_init]
    ring_nf
    rw [mul_assoc]
    rw [mul_inv_cancel₀]
    · rw [mul_one, inv_eq_one_div S.k, mul_assoc]
      rw [mul_one_div S.m S.k, ← inverse_ω_sq]
      ring
    · exact k_neq_zero S
  · intro h_norm
    apply norm_eq_zero.mp
    rw [real_inner_self_eq_norm_sq (∂ₜ (trajectory S IC) t)] at h_energy_t
    have energies : S.energy (trajectory S IC) t = S.energy (trajectory S IC) t := by rfl
    nth_rewrite 1 [h_energy_t] at energies
    nth_rewrite 1 [h_init] at energies
    rw [h_norm] at energies
    have h₁ : S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (√(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)
            = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by
      calc
        S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (√(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)
            = 2 * (2⁻¹ * S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2
            + 2⁻¹ * (S.k * √(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)) := by
          simp [mul_add]
          rw [← mul_assoc, ← mul_assoc]
          rw [mul_inv_cancel_of_invertible 2, one_mul]
      _ = 2 * (1 / 2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2)) := by rw [energies]
      _ = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by simp
    have h₂ : S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2)
        = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by
      rw [← h₁, sq_sqrt ?_]
      apply add_nonneg
      apply sq_nonneg
      apply sq_nonneg
    have h₃: ‖∂ₜ (trajectory S IC) t‖ ^ 2 = ‖IC.v₀‖ ^ 2 - (S.k / S.m) * (‖IC.v₀‖ / S.ω) ^ 2 := by
      calc
        ‖∂ₜ (trajectory S IC) t‖ ^ 2 = (1 / S.m) * (S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2
        + S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) - S.k * (‖IC.x₀‖ ^ 2
        + (‖IC.v₀‖ / S.ω) ^ 2)) := by simp
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2
          - S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2)) := by rw [h₂]
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2
          - S.k * ‖IC.x₀‖ ^ 2 - S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by
          rw [mul_add S.k (‖IC.x₀‖ ^ 2) ((‖IC.v₀‖ /S.ω) ^2)]
          rw [←sub_sub_sub_eq (S.m * ‖IC.v₀‖ ^ 2) (S.k * ‖IC.x₀‖ ^ 2)
          (S.k * (‖IC.v₀‖ / S.ω) ^ 2) (S.k * ‖IC.x₀‖ ^ 2)]
          simp only [one_div, sub_sub_sub_cancel_right, add_sub_cancel_right]
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 - S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by simp
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2) - (1 / S.m) * (S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by
          rw [mul_sub (1 / S.m) (S.m * ‖IC.v₀‖ ^ 2) (S.k * (‖IC.v₀‖ / S.ω) ^ 2)]
        _ = ‖IC.v₀‖ ^ 2 - (S.k / S.m) * (‖IC.v₀‖ / S.ω) ^ 2 := by
          simp only [one_div, ne_eq, m_neq_zero, not_false_eq_true, inv_mul_cancel_left₀,
            sub_right_inj]
          rw [← mul_assoc, inv_mul_eq_div S.m S.k]
    rw [← ω_sq, div_pow ‖IC.v₀‖ S.ω 2] at h₃
    rw [mul_div_cancel₀ (‖IC.v₀‖ ^ 2) ?_] at h₃
    rw [sub_self (‖IC.v₀‖ ^ 2)] at h₃
    rw [sq_eq_zero_iff] at h₃
    exact h₃
    rw [pow_ne_zero_iff ?_]
    apply ω_neq_zero
    exact Ne.symm (Nat.zero_ne_add_one 1)
/-!

## F. Some open TODOs

We give some open TODOs for the classical harmonic oscillator.

-/

TODO "6VZI3" "For the classical harmonic oscillator find the time for which it returns to
  it's initial position and velocity."

TODO "6VZJB" "For the classical harmonic oscillator find the times for
  which it passes through zero."

end InitialConditions

end HarmonicOscillator

end ClassicalMechanics
