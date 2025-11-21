/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Electromagnetism.Kinematics.ElectricField
import PhysLean.Electromagnetism.Distributions.Potential
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
import PhysLean.SpaceAndTime.Space.DistConst
import PhysLean.SpaceAndTime.Space.Norm
import PhysLean.Mathematics.Distribution.PowMul
/-!

# The electrostatics of a stationary point particle in 1d

## i. Overview

In this module we give the electromagnetic properties of a point particle
sitting at the origin in 1d space.

The electric field is given by the Heaviside step function, and the scalar potential
is given by a function proportional to the absolute value of the distance from the particle.

Note this currently has two versions of many of the results.
The ones not in the `DistElectromagneticPotential` namespace are old, and will slowly be
replaced.

## ii. Key results

- `oneDimPointParticleCurrentDensity` : The Lorentz current density of a point particle
  stationary at the origin of 1d space.
- `oneDimPointParticle` : The electromagnetic potential of a point particle
  stationary at the origin of 1d space.
- `oneDimPointParticle_gradLagrangian` : The variational gradient of the Lagrangian
  for a point particle stationary at the origin of 1d space is zero for the
  given electromagnetic potential. (i.e. Maxwell's equations are satisfied).

## iii. Table of contents

- A. The electromagnetic potential
- B. The Potentials
  - B.1. The electromagnetic potential
  - B.2. The vector potential is zero
  - B.3. The scalar potential
- C. The electric field
  - C.1. Time derivative of the electric field is zero
- D. Maxwell's equations
  - D.1. Gauss' law
  - D.2. The variational gradient of the Lagrangian is zero

## iv. References

-/

namespace Electromagnetism
open Distribution SchwartzMap
open Space StaticElectricField MeasureTheory

/-!

## A. The electromagnetic potential

-/

/-- The current density of of a point particle stationary at the origin
  of 1d space. -/
noncomputable def oneDimPointParticleCurrentDensity (q : ℝ) : LorentzCurrentDensityD 1 :=
  LorentzCurrentDensityD.toComponents.symm fun μ =>
  match μ with
  | Sum.inl 0 => SpaceTime.distTimeSlice.symm <| constantTime (q • diracDelta ℝ 0)
  | Sum.inr _ => 0

@[simp]
lemma oneDimPointParticleCurrentDensity_apply_inr_eq_zero (q : ℝ) (i : Fin 1) :
    (oneDimPointParticleCurrentDensity q).toComponents (Sum.inr i) = 0 := by
  simp [oneDimPointParticleCurrentDensity]

/-!

## B. The Potentials

-/

/-!

### B.1. The electromagnetic potential

-/

/-- The electromagnetic potential of a point particle stationary at the origin
  of 1d space. -/
noncomputable def oneDimPointParticle (q : ℝ) : ElectromagneticPotentialD 1 :=
  ElectromagneticPotentialD.toComponents.symm fun μ =>
  match μ with
  | Sum.inl 0 => SpaceTime.distTimeSlice.symm <| Space.constantTime
    (- distOfFunction (fun x => (q/(2)) • ‖x‖)
    (by
      apply IsDistBounded.const_smul
      convert IsDistBounded.pow (n := 1) (by simp)
      simp))
  | Sum.inr i => 0

/-- The electromagnetic potential of a point particle stationary at the origin
  of 1d space. -/
noncomputable def DistElectromagneticPotential.oneDimPointParticle (q : ℝ) :
    DistElectromagneticPotential 1 := SpaceTime.distTimeSlice.symm <| Space.constantTime <|
  distOfFunction (fun x => ((- q/(2)) * ‖x‖) • Lorentz.Vector.basis (Sum.inl 0)) (by fun_prop)

/-

### B.2. The vector potential is zero

-/

@[simp]
lemma oneDimPointParticle_vectorPotential (q : ℝ) :
    (oneDimPointParticle q).vectorPotential = 0 := by
  rw [Electromagnetism.ElectromagneticPotentialD.vectorPotential]
  ext i
  simp [oneDimPointParticle]

@[simp]
lemma DistElectromagneticPotential.oneDimPointParticle_vectorPotential(q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle q).vectorPotential 1 = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    oneDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

### B.3. The scalar potential

-/

lemma oneDimPointParticle_scalarPotential (q : ℝ) :
    (oneDimPointParticle q).scalarPotential =
    Space.constantTime (- distOfFunction (fun x => (q/(2)) • ‖x‖)
    (by
      apply IsDistBounded.const_smul
      convert IsDistBounded.pow (n := 1) (by simp)
      simp)) := by
  rw [Electromagnetism.ElectromagneticPotentialD.scalarPotential]
  ext x
  simp [oneDimPointParticle]

lemma DistElectromagneticPotential.oneDimPointParticle_scalarPotential (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle q).scalarPotential 1 =
    Space.constantTime (distOfFunction (fun x => - (q/(2)) • ‖x‖) (by fun_prop)) := by
  ext ε
  simp only [scalarPotential, Lorentz.Vector.temporalCLM, Fin.isValue, SpeedOfLight.val_one,
    one_smul, oneDimPointParticle, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_comp',
    LinearMap.coe_toContinuousLinearMap', Function.comp_apply, constantTime_apply,
    distOfFunction_vector_eval, Lorentz.Vector.apply_smul, Lorentz.Vector.basis_apply, ↓reduceIte,
    mul_one, smul_eq_mul, neg_mul]
  congr
  funext x
  ring

/-!

## C. The electric field

-/

set_option maxHeartbeats 400000 in
lemma oneDimPointParticle_electricField_eq_heavisideStep (q : ℝ) :
    (oneDimPointParticle q).electricField = constantTime (q •
    ((heavisideStep 0).smulRight (basis 0) - (1 / (2 : ℝ)) • distConst 1 (basis 0))) := by
  suffices hE : - Space.distGrad (- distOfFunction (fun x => (q/(2)) • ‖x‖)
      (by
        apply IsDistBounded.const_smul
        convert IsDistBounded.pow (n := 1) (by simp)
        simp)) = ((q) • ((heavisideStep 0).smulRight (basis 0) -
      (1/(2 : ℝ)) • distConst 1 (basis 0))) by
    rw [Electromagnetism.ElectromagneticPotentialD.electricField]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, oneDimPointParticle_vectorPotential, map_zero,
      sub_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, one_div, map_smul, map_sub]
    rw [oneDimPointParticle_scalarPotential, constantTime_distSpaceGrad, ← map_neg, hE]
    simp
  /- Some preamble for results which are used throughout this proof. -/
  let s : Set (EuclideanSpace ℝ (Fin 1)) :=
    {x : EuclideanSpace ℝ (Fin 1) | 0 < x (Fin.last 0)}
  have hs : NullMeasurableSet s volume := by
    simp [s]
    refine nullMeasurableSet_lt ?_ ?_
    · fun_prop
    · change AEMeasurable oneEquivCLE volume
      fun_prop
  /- We are showing equality of two distributions of the from
    `(Space 1) →d[ℝ] EuclideanSpace ℝ (Fin 1)`. Two such distributions `f` and `g` are equal
    if and only if for all Schwartz maps η `⟪f, η⟫ 0 = ⟪g, η⟫ 0` -/
  ext η i
  fin_cases i
  calc _

    /- By the definition of the gradiant on distributions
      `-⟪∇ (- q/(2 * ε) |x|), η⟫ 0 = - ⟪(-q/(2 * ε) |x|), -dη/dx⟫`
      which is equal to `- ⟪(q/(2 * ε) |x|), dη/dx⟫`.
      By definition of `(q/(2 * ε) |x|)` as a distribution this is equal to
      `- ∫ x, dη/dx • (q/(2 * ε) |x|)`.
    -/
    _ = - (∫ x, fderiv ℝ η x (basis 0) • (q/(2)) • ‖x‖) := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul, map_neg, neg_neg, Fin.zero_eta,
        Fin.isValue, distGrad_eq_sum_basis, Finset.univ_unique, Fin.default_eq_zero, neg_smul,
        Finset.sum_neg_distrib, Finset.sum_singleton, PiLp.neg_apply, PiLp.smul_apply, basis_self,
        mul_one, neg_inj]
      rw [distOfFunction_apply]
      rfl
    /- Pulling out the scalar `q/(2 * ε)` gives
      `- ∫ x, dη/dx • (q/(2 * ε) |x|) = - q/(2 * ε) ∫ x, dη/dx • |x|`.
      With the bounds of the integral explicit this is
      `- q/(2 * ε) ∫_(-∞)^(∞) x, dη/dx • |x|`
    -/
    _ = - (q/(2)) * (∫ x, fderiv ℝ η x (basis 0) • ‖x‖) := by
      rw [← integral_const_mul, ← integral_neg]
      congr
      funext x
      simp only [Fin.isValue, smul_eq_mul, neg_mul, neg_inj]
      ring
    /- We split the integral
      `- q/(2 * ε) ∫_(-∞)^(∞) x, dη/dx • |x|`
      into two halfs
      `- q/(2 * ε) ∫_0^(∞) x, dη/dx • |x| - q/(2 * ε) ∫_(-∞)^0 x, dη/dx • |x| `
    -/
    _ = - (q/(2)) * (∫ x in s, fderiv ℝ η x (basis 0) • ‖x‖) +
        - (q/(2)) * (∫ x in sᶜ, fderiv ℝ η x (basis 0) • ‖x‖) := by
      rw [← integral_add_compl₀ hs ?_]
      · ring
      change Integrable (fun x : EuclideanSpace ℝ (Fin 1) =>
        ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0)) ((fderivCLM ℝ) η)) x • ‖x‖)
      apply IsDistBounded.integrable_space
      convert IsDistBounded.pow (n := 1) (by simp)
      simp
    /- In the first of these integrals `|x|=x` whilst in the second `|x| = -x` giving
      us
      `- q/(2 * ε) ∫_0^(∞) x, dη/dx • x - q/(2 * ε) ∫_(-∞)^0 x, dη/dx • (-x)` -/
    _ = - (q/(2)) * (∫ x in s, fderiv ℝ η x (basis 0) • x 0) +
        - (q/(2)) * (∫ x in sᶜ, fderiv ℝ η x (basis 0) • (- x 0)) := by
      congr 2
      · refine setIntegral_congr_ae₀ hs ?_
        filter_upwards with x hx
        congr
        rw [@PiLp.norm_eq_of_L2]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
          Finset.sum_singleton]
        refine Real.sqrt_eq_cases.mpr ?_
        left
        apply And.intro
        · exact Eq.symm (Lean.Grind.Semiring.pow_two (x 0))
        · simp [s] at hx
          apply le_of_lt hx
      · refine setIntegral_congr_ae₀ ?_ ?_
        · simpa using hs
        filter_upwards with x hx
        congr
        rw [@PiLp.norm_eq_of_L2]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
          Finset.sum_singleton]
        refine Real.sqrt_eq_cases.mpr ?_
        left
        simp only [Fin.isValue, mul_neg, neg_mul, neg_neg, Left.nonneg_neg_iff]
        apply And.intro
        · exact Eq.symm (Lean.Grind.Semiring.pow_two (x 0))
        · simp [s] at hx
          exact hx
    /- The next couple of steps are setting things up to use the
      result `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`. -/
    /- So far our integral has really being over `Space 1` we now transorm it
      into an integral over `ℝ`, using `oneEquivCLE`.
      Here `(η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)` is just `η` as
      a Schwartz map from `ℝ` rather then from `Space 1`.
      So symatically we have exactly the same thing as above
      `- q/(2 * ε) ∫_0^(∞) x, dη/dx • x - q/(2 * ε) ∫_(-∞)^0 x, dη/dx • (-x)`
      exacpt `x` is now `ℝ` rather then `Space 1`.
        -/
    _ = - (q/(2)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) x * x) +
        - (q/(2)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) x * (-x)) := by
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      congr 3
      · simp only [Fin.isValue, smul_eq_mul, compCLMOfContinuousLinearEquiv_apply]
        funext x
        congr 1
        rw [← fderiv_deriv]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        simp only [Fin.isValue, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
          Function.comp_apply]
        congr 1
        ext i
        fin_cases i
        simp only [Fin.isValue, Fin.zero_eta, basis_self, oneEquivCLE]
        rfl
      · congr
        simp only [Fin.reduceLast, Fin.isValue, Set.preimage_compl, Set.preimage_setOf_eq, s]
        ext x
        simp [oneEquiv_symm_apply]
      · simp only [Fin.isValue, smul_eq_mul, mul_neg, compCLMOfContinuousLinearEquiv_apply]
        funext x
        congr 1
        rw [← fderiv_deriv]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        simp only [Fin.isValue, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
          Function.comp_apply]
        congr 2
        ext i
        fin_cases i
        simp only [Fin.isValue, Fin.zero_eta, basis_self, oneEquivCLE]
        rfl
        exact 2
    /- We use the fact that e.g. `(d(η • x)/dx - η x) = d η/dx • x` to rewrite
    `- q/(2 * ε) ∫_0^(∞) x, dη/dx • x - q/(2 * ε) ∫_(-∞)^0 x, dη/dx • (-x)`
    as
    `- q/(2 * ε) ∫_0^(∞) x, (d(η • x)/dx - η x) - q/(2 * ε) ∫_(-∞)^0 x, (d(η • (-x))/dx + η x)` -/
    _ = - (q/(2)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (fun x => η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x * (fun x => x) x) x
        - η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (fun x => η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x * (fun x => - x) x) x
        + η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · funext x
        rw [deriv_fun_mul]
        simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, deriv_id'', mul_one,
          add_sub_cancel_right]
        · exact SchwartzMap.differentiableAt _
        · fun_prop
      · funext x
        rw [deriv_fun_mul]
        simp only [compCLMOfContinuousLinearEquiv_apply, mul_neg, Function.comp_apply, deriv_neg'',
          mul_one, neg_add_cancel_right]
        · exact SchwartzMap.differentiableAt _
        · fun_prop
    /- By definition of `powOneMul` we rewrite `η • x` using `powOneMul`. Symatically we now have
      `- q/(2 * ε) ∫_0^(∞) x, (d(η • x)/dx - η x) - q/(2 * ε) ∫_(-∞)^0 x, (d(- (η • x)))/dx + η x)`
      things are just written in different ways. -/
    _ = - (q/(2)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x
        - η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x
        + η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · funext x
        congr
        funext x
        simp [powOneMul_apply]
        rw [mul_comm]
      · funext x
        congr
        funext x
        change _ = - ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)) x
        simp [powOneMul_apply]
        rw [mul_comm]
    /- We seperate the integrals to get
      `- q/(2 * ε) (∫_0^(∞) x, d(η • x)/dx - ∫_0^(∞) x, η x) `
      `- q/(2 * ε) (∫_(-∞)^0 x, d(- (η • x)))/dx + ∫_(-∞)^0 x, η x)`. -/
    _ = - (q/(2)) * ((∫ x in Set.Ioi (0 : ℝ),
        deriv (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) * ((∫ x in Set.Iic (0 : ℝ),
        deriv (-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      rw [integral_sub, integral_add]
      · refine Integrable.restrict ?_
        change Integrable (derivCLM ℝ
          (-(powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
        exact integrable
            ((derivCLM ℝ) (-(powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
      · refine Integrable.restrict ?_
        exact integrable _
      · refine Integrable.restrict ?_
        change Integrable (derivCLM ℝ
          (powOneMul ℝ ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
        exact integrable
            ((derivCLM ℝ) (powOneMul ℝ ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
      · refine Integrable.restrict ?_
        exact integrable _
    /- We are now in a position to use `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`
      which rewrites `∫_0^(∞) x, d(η • x)/dx = 0 - (η 0 • 0)`
      and `∫_(-∞)^0 x, d(- (η • x)))/dx = (- η 0 • 0) - 0`. This gives us
      `- q/(2 * ε) ((0 - (η 0 • 0))- ∫_0^(∞) x, η x)`
      `- q/(2 * ε) (((- η 0 • 0) - 0)+ ∫_(-∞)^0 x, η x)`. -/
    _ = - (q/(2)) * ((0 -
        (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) 0)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) *
        (((-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) 0 - 0)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        · apply Continuous.continuousWithinAt
          fun_prop
        · intro x hx
          refine DifferentiableAt.hasDerivAt ?_
          exact SchwartzMap.differentiableAt _
        · apply Integrable.integrableOn
          change Integrable (derivCLM ℝ ((powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
          exact integrable
            ((derivCLM ℝ) ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
        · exact Filter.Tendsto.mono_left ((powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)).toZeroAtInfty.zero_at_infty'
            atTop_le_cocompact
      · apply MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto
        · apply Continuous.continuousWithinAt
          fun_prop
        · intro x hx
          refine DifferentiableAt.hasDerivAt ?_
          exact SchwartzMap.differentiableAt _
        · apply Integrable.integrableOn
          change Integrable (derivCLM ℝ (- (powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
          exact integrable
            ((derivCLM ℝ) (- (powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
        · apply Filter.Tendsto.mono_left
            ((- (powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)).toZeroAtInfty.zero_at_infty')
          exact atBot_le_cocompact
    /- We simplify the `(η 0 • 0)` and `(- η 0 • 0)` terms to be `0`. Giving us
    `- q/(2 * ε) ((0 - 0)- ∫_0^(∞) x, η x)`
    `- q/(2 * ε) ((0 - 0)+ ∫_(-∞)^0 x, η x)`. -/
    _ = - (q/(2)) * ((0 - 0)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) * ((0 - 0)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · simp [powOneMul_apply]
      · change - ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)) 0 = 0
        simp [powOneMul_apply]
    /- Simplifying further gives
    `q/(2 * ε) ∫_0^(∞) x, η x + - q/(2 * ε) ∫_(-∞)^0 x, η x)`. -/
    _ = (q/(2)) *
        (∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2)) *
          (∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      simp
    /- We now turn back to integrals over `Space 1` instead of integrals over `x`.
    Schematically the integral remains the same.
    `q/(2 * ε) ∫_0^(∞) x, η x + - q/(2 * ε) ∫_(-∞)^0 x, η x)`. -/
    _ = (q/(2)) * (∫ x in s, η x) + - (q/2) * (∫ x in sᶜ, η x) := by
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      congr
      ext x
      simp [oneEquiv_symm_apply, s]
    /- We rewrite the second integral `∫_(-∞)^0 = ∫_(-∞)^∞ - ∫_0^∞` to give
    `q/(2 * ε) ∫_0^(∞) x, η x + - q/(2 * ε) (∫_(-∞)^∞ x, η x - ∫_0^∞ x, η x)`. -/
    _ = (q/(2)) * (∫ x in s, η x) + - (q/(2)) * ((∫ x, η x) - ∫ x in s, η x) := by
      congr 2
      rw [← integral_add_compl₀ hs]
      · ring
      exact integrable η
    /- Simplifying we get:
    `q/(ε) ∫_0^(∞) x, η x + - q/(2 * ε) ∫_(-∞)^∞ x, η x`. -/
    _ = (q) * (∫ x in s, η x) + - (q/(2)) * (∫ x, η x) := by
      ring
  /- Both sides are now essentially equal, by the definition of the heaviside step,
    and the constant distribution. What is left is some small tidying up. -/
  simp [mul_sub]
  congr 2
  rw [← mul_assoc]
  congr 1
  simp [distConst, const_apply]
  rw [integral_smul_const]
  simp

lemma DistElectromagneticPotential.oneDimPointParticle_electricField (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle q).electricField 1 =
    (q / 2) • constantTime (distOfFunction (fun x : Space 1 => ‖x‖ ^ (- 1 : ℤ) • x)
      (IsDistBounded.zpow_smul_self (- 1 : ℤ) (by omega))) := by
  have h1 := Space.distGrad_distOfFunction_norm_zpow (d := 0) 1 (by grind)
  simp at h1
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, oneDimPointParticle_scalarPotential,
    smul_eq_mul, neg_mul, oneDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg,
    zpow_neg, zpow_one]
  rw [constantTime_distSpaceGrad, distOfFunction_neg, distOfFunction_mul_fun _ (by fun_prop)]
  simp only [map_neg, map_smul, neg_neg, h1]

/-!

### C.1. Time derivative of the electric field is zero

-/

@[simp]
lemma oneDimPointParticle_electricField_timeDeriv_eq_zero (q : ℝ) :
    distTimeDeriv (oneDimPointParticle q).electricField = 0 := by
  rw [oneDimPointParticle_electricField_eq_heavisideStep]
  rw [constantTime_distTimeDeriv]

/-!

## D. Maxwell's equations

-/

/-!

### D.1. Gauss' law

-/

lemma oneDimPointParticle_gaussLaw (q : ℝ) :
    distSpaceDiv (oneDimPointParticle q).electricField = constantTime (q • diracDelta ℝ 0) := by
  ext η
  rw [oneDimPointParticle_electricField_eq_heavisideStep]
  rw [constantTime_distSpaceDiv]
  congr
  ext η
  change (distDiv ((q) • (ContinuousLinearMap.smulRight (heavisideStep 0) (basis 0) -
    (1 / 2) • distConst 1 (basis 0)))) η = (q • diracDelta ℝ 0) η
  haveI : SMulZeroClass ℝ ((Space 1)→d[ℝ] ℝ) := by infer_instance
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, one_div, map_smul, map_sub,
    distDiv_distConst, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sub', Pi.smul_apply,
    Pi.sub_apply, ContinuousLinearMap.zero_apply, smul_eq_mul, mul_zero, sub_zero, diracDelta_apply]
  field_simp
  congr 1
  rw [distDiv_apply_eq_sum_fderivD]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rw [fderivD_apply]
  simp only [Fin.isValue, ContinuousLinearMap.smulRight_apply, PiLp.neg_apply, PiLp.smul_apply,
    basis_self, smul_eq_mul, mul_one]
  rw [heavisideStep_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceLast, Fin.isValue]
  rw [← MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
    (μ := volume) (ν := volume) (f := oneEquiv.symm)]
  simp only [Fin.isValue, Set.preimage_setOf_eq]
  let f' := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0)) ((fderivCLM ℝ) η))
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm η
  change -∫ (x : ℝ) in Set.Ioi 0, f' x = _
  rw [neg_eq_iff_eq_neg]
  trans 0 - f 0
  · apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f' := f')
      (f := f)
    · apply Continuous.continuousWithinAt
      fun_prop
    · have hf : f' = (SchwartzMap.derivCLM ℝ) f := by
        ext x
        simp [f']
        change fderiv ℝ η (oneEquivCLE.symm x) (basis 0) = _
        trans fderiv ℝ η (oneEquivCLE.symm x) (oneEquivCLE.symm 1)
        · congr 1
          ext i
          fin_cases i
          simp
          rfl
        rw [← fderiv_deriv]
        dsimp [f]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        rfl
      rw [hf]
      simpa using fun x hx => SchwartzMap.differentiableAt f
    · exact (integrable f').integrableOn
    · exact Filter.Tendsto.mono_left f.toZeroAtInfty.zero_at_infty' atTop_le_cocompact
  · simp [f]
  · exact oneEquiv_symm_measurePreserving
  · exact oneEquiv_symm_measurableEmbedding

lemma DistElectromagneticPotential.oneDimPointParticle_gaussLaw (q : ℝ) :
    distSpaceDiv ((DistElectromagneticPotential.oneDimPointParticle q).electricField 1) =
    constantTime (q • diracDelta ℝ 0) := by
  rw [DistElectromagneticPotential.oneDimPointParticle_electricField]
  simp only [Int.reduceNeg, zpow_neg, zpow_one, map_smul]
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 0)
  simp at h1
  rw [constantTime_distSpaceDiv, h1]
  simp only [map_smul]
  suffices h : volume.real (Metric.ball (0 : Space 1) 1) = 2 by
    rw [h]
    simp [smul_smul]
  simp [MeasureTheory.Measure.real]
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0)]
  · simp
  · simp

/-!

### D.2. The variational gradient of the Lagrangian is zero

-/

lemma oneDimPointParticle_gradLagrangian (q : ℝ) :
    (oneDimPointParticle q).gradLagrangian (oneDimPointParticleCurrentDensity q) = 0 := by
  rw [ElectromagneticPotentialD.gradLagrangian_one_dimension_electricField]
  funext μ
  match μ with
  | Sum.inl 0 =>
    simp [oneDimPointParticleCurrentDensity]
    rw [oneDimPointParticle_gaussLaw]
    simp
  | Sum.inr 0 =>
    simp

end Electromagnetism
