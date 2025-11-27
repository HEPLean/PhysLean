/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Electromagnetism.Dynamics.KineticTerm
import PhysLean.Electromagnetism.Dynamics.IsExtrema
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

- `oneDimPointParticle` : The electromagnetic potential of a point particle
  stationary at the origin of 1d space.
- `oneDimPointParticle_gaussLaw` : The electric field of a point
  particle stationary at the origin of 1d space satisfies Gauss' law.

## iii. Table of contents

- A. The Potentials
  - A.1. The electromagnetic potential
  - A.2. The vector potential is zero
  - A.3. The scalar potential
- B. The electric field
- D. Maxwell's equations

## iv. References

-/

namespace Electromagnetism
open Distribution SchwartzMap
open Space StaticElectricField MeasureTheory
namespace DistElectromagneticPotential

/-!

## A. The current density

-/

/-- The current density of a point particle stationary at the origin
  of 1d space. -/
noncomputable def oneDimPointParticleCurrentDensity (c : SpeedOfLight) (q : ℝ) :
    DistLorentzCurrentDensity 1 := (SpaceTime.distTimeSlice c).symm <|
    constantTime ((c * q) • diracDelta' ℝ 0 (Lorentz.Vector.basis (Sum.inl 0)))

@[simp]
lemma oneDimPointParticleCurrentDensity_currentDensity (c : SpeedOfLight) (q : ℝ) :
    (oneDimPointParticleCurrentDensity c q).currentDensity c = 0 := by
  ext ε i
  simp [oneDimPointParticleCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    Lorentz.Vector.spatialCLM,  constantTime_apply]

@[simp]
lemma oneDimPointParticleCurrentDensity_chargeDensity (c : SpeedOfLight) (q : ℝ) :
    (oneDimPointParticleCurrentDensity c q).chargeDensity c = constantTime (q • diracDelta ℝ 0) := by
  ext ε
  simp only [DistLorentzCurrentDensity.chargeDensity, one_div, Lorentz.Vector.temporalCLM,
    Fin.isValue, oneDimPointParticleCurrentDensity, map_smul, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, diracDelta'_apply, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul, diracDelta_apply]
  field_simp

/-!

## A. The Potentials

-/

/-!

### A.1. The electromagnetic potential

-/

/-- The electromagnetic potential of a point particle stationary at the origin
  of 1d space. -/
noncomputable def oneDimPointParticle (𝓕  : FreeSpace) (q : ℝ) :
    DistElectromagneticPotential 1 := (SpaceTime.distTimeSlice 𝓕.c).symm <| Space.constantTime <|
  distOfFunction (fun x => ((- (q * 𝓕.μ₀ * 𝓕.c)/ 2) * ‖x‖) • Lorentz.Vector.basis (Sum.inl 0)) (by fun_prop)

/-

### A.2. The vector potential is zero

-/

@[simp]
lemma oneDimPointParticle_vectorPotential (𝓕  : FreeSpace) (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle 𝓕 q).vectorPotential 𝓕.c = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    oneDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

### A.3. The scalar potential

-/

lemma oneDimPointParticle_scalarPotential (𝓕  : FreeSpace) (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle 𝓕 q).scalarPotential 𝓕.c =
    Space.constantTime (distOfFunction (fun x => - ((q * 𝓕.μ₀ * 𝓕.c ^ 2)/(2)) • ‖x‖) (by fun_prop)) := by
  ext ε
  simp only [scalarPotential, Lorentz.Vector.temporalCLM, Fin.isValue, map_smul,
    ContinuousLinearMap.comp_smulₛₗ, Real.ringHom_apply, oneDimPointParticle, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, distOfFunction_vector_eval, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul, neg_mul]
  rw [distOfFunction_mul_fun _ (by fun_prop), distOfFunction_neg, distOfFunction_mul_fun  _ (by fun_prop)]
  simp
  ring

/-!

## B. The electric field

-/

lemma oneDimPointParticle_electricField (𝓕 : FreeSpace) (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle 𝓕 q).electricField 𝓕.c =
    ((q * 𝓕.μ₀ * 𝓕.c ^ 2) / 2) • constantTime (distOfFunction (fun x : Space 1 => ‖x‖ ^ (- 1 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 1 : ℤ) (by omega))) := by
  have h1 := Space.distGrad_distOfFunction_norm_zpow (d := 0) 1 (by grind)
  simp at h1
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, oneDimPointParticle_scalarPotential,
    smul_eq_mul, neg_mul, oneDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg,
    zpow_neg, zpow_one]
  rw [constantTime_distSpaceGrad, distOfFunction_neg, distOfFunction_mul_fun _ (by fun_prop)]
  simp only [map_neg, map_smul, neg_neg, h1]

/-!

### B.1. the time derivative of the electric field

-/

@[simp]
lemma oneDimPointParticle_electricField_timeDeriv (𝓕 : FreeSpace) (q : ℝ) :
    Space.distTimeDeriv ((DistElectromagneticPotential.oneDimPointParticle 𝓕 q).electricField 𝓕.c) = 0 := by
  rw [oneDimPointParticle_electricField]
  simp

/-!

## C. The magnetic field

-/

lemma oneDimPointParticle_magneticFieldMatrix (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle 𝓕 q).magneticFieldMatrix 𝓕.c = 0 := by
  simp
/-!

## D. Maxwell's equations

-/

lemma oneDimPointParticle_div_electricField {𝓕} (q : ℝ) :
    distSpaceDiv ((DistElectromagneticPotential.oneDimPointParticle 𝓕 q).electricField 𝓕.c) =
    (𝓕.μ₀ * 𝓕.c ^ 2) • constantTime (q • diracDelta ℝ 0) := by
  rw [DistElectromagneticPotential.oneDimPointParticle_electricField]
  simp only [Int.reduceNeg, zpow_neg, zpow_one, map_smul]
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 0)
  simp at h1
  rw [constantTime_distSpaceDiv, h1]
  simp only [map_smul]
  suffices h : volume.real (Metric.ball (0 : Space 1) 1) = 2 by
    rw [h]
    simp [smul_smul]
    ring_nf
  simp [MeasureTheory.Measure.real]
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0)]
  · simp
  · simp

lemma oneDimPointParticle_isExterma  (𝓕 : FreeSpace) (q : ℝ) :
    (oneDimPointParticle 𝓕 q).IsExtrema 𝓕 (oneDimPointParticleCurrentDensity 𝓕.c q) := by
  rw [isExtrema_iff_components]
  apply And.intro
  · intro ε
    rw [gradLagrangian_sum_inl_0]
    simp
    rw [oneDimPointParticle_div_electricField]
    simp
    field_simp
    ring
  · intro ε i
    rw [gradLagrangian_sum_inr_i]
    simp
end DistElectromagneticPotential
end Electromagnetism
