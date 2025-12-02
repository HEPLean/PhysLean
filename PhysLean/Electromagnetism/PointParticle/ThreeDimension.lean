/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.IsExtrema
import PhysLean.SpaceAndTime.Space.Norm
import PhysLean.SpaceAndTime.Space.Translations
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!

# The electrostatics of a stationary point particle in 3d

## i. Overview

In this module we give the electromagnetic properties of a point particle
sitting at the origin in 3d space.

The electric field is given by the Heaviside step function, and the scalar potential
is given by a function proportional to the absolute value of the distance from the particle.

## ii. Key results

- `threeDimPointParticle` : The electromagnetic potential of a point particle
  stationary at a point in 3d space.
- `threeDimPointParticle_isExterma` : The electric field of a point
  particle stationary at a point of 3d space satisfies Maxwell's equations

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
open Space MeasureTheory
namespace DistElectromagneticPotential

/-!

## A. The current density

-/

/-- The current density of a point particle stationary at a point `r\₀`
  of 3d space. -/
noncomputable def threeDimPointParticleCurrentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    DistLorentzCurrentDensity 3 := (SpaceTime.distTimeSlice c).symm <|
  constantTime ((c * q) • diracDelta' ℝ r₀ (Lorentz.Vector.basis (Sum.inl 0)))

lemma threeDimPointParticleCurrentDensity_eq_distTranslate (c : SpeedOfLight) (q : ℝ)
    (r₀ : Space 3) :
    threeDimPointParticleCurrentDensity c q r₀ = ((SpaceTime.distTimeSlice c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    ((c * q) • diracDelta' ℝ 0 (Lorentz.Vector.basis (Sum.inl 0)))) := by
  rw [threeDimPointParticleCurrentDensity]
  congr
  ext η
  simp [distTranslate_apply]

@[simp]
lemma threeDimPointParticleCurrentDensity_currentDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticleCurrentDensity c q r₀).currentDensity c = 0 := by
  ext ε i
  simp [threeDimPointParticleCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    Lorentz.Vector.spatialCLM, constantTime_apply]

@[simp]
lemma threeDimPointParticleCurrentDensity_chargeDensity (c : SpeedOfLight) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticleCurrentDensity c q r₀).chargeDensity c =
    constantTime (q • diracDelta ℝ r₀) := by
  ext ε
  simp only [DistLorentzCurrentDensity.chargeDensity, one_div, Lorentz.Vector.temporalCLM,
    Fin.isValue, threeDimPointParticleCurrentDensity, map_smul, LinearMap.coe_mk, AddHom.coe_mk,
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
open Real

/-- The electromagnetic potential of a point particle stationary at `r₀`
  of 3d space. -/
noncomputable def threeDimPointParticle (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    DistElectromagneticPotential 3 := (SpaceTime.distTimeSlice 𝓕.c).symm <| Space.constantTime <|
  distOfFunction (fun x => (((q * 𝓕.μ₀ * 𝓕.c)/ (4 * π)) * ‖x - r₀‖⁻¹) •
    Lorentz.Vector.basis (Sum.inl 0))
    (((IsDistBounded.inv_shift _).const_mul_fun _).smul_const _)

lemma threeDimPointParticle_eq_distTranslate (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    threeDimPointParticle 𝓕 q r₀ = ((SpaceTime.distTimeSlice 𝓕.c).symm <|
    constantTime <|
    distTranslate (basis.repr r₀) <|
    distOfFunction (fun x => (((q * 𝓕.μ₀ * 𝓕.c)/ (4 * π))* ‖x‖⁻¹) •
      Lorentz.Vector.basis (Sum.inl 0))
      ((IsDistBounded.inv.const_mul_fun _).smul_const _)) := by
  rw [threeDimPointParticle]
  congr
  ext η
  simp [distTranslate_ofFunction]

/-

### A.2. The vector potential is zero

-/

@[simp]
lemma threeDimPointParticle_vectorPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).vectorPotential 𝓕.c = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    threeDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

### A.3. The scalar potential

-/

lemma threeDimPointParticle_scalarPotential (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).scalarPotential 𝓕.c =
    Space.constantTime (distOfFunction (fun x => (q/ (4 * π * 𝓕.ε₀))• ‖x - r₀‖⁻¹)
      (((IsDistBounded.inv_shift _).const_mul_fun _))) := by
  ext ε
  simp only [scalarPotential, Lorentz.Vector.temporalCLM, Fin.isValue, map_smul,
    ContinuousLinearMap.comp_smulₛₗ, ringHom_apply, threeDimPointParticle, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', Pi.smul_apply,
    Function.comp_apply, constantTime_apply, distOfFunction_vector_eval, Lorentz.Vector.apply_smul,
    Lorentz.Vector.basis_apply, ↓reduceIte, mul_one, smul_eq_mul]
  rw [distOfFunction_mul_fun _ (IsDistBounded.inv_shift _),
    distOfFunction_mul_fun _ (IsDistBounded.inv_shift _)]
  simp
  ring_nf
  simp only [𝓕.c_sq, one_div, mul_inv_rev, mul_eq_mul_right_iff, inv_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  field_simp

/-!

## B. The electric field

-/

lemma threeDimPointParticle_electricField (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c =
    (q/ (4 * π * 𝓕.ε₀)) • constantTime (distOfFunction (fun x : Space 3 =>
      ‖x - r₀‖ ^ (- 3 : ℤ) • basis.repr (x - r₀))
      ((IsDistBounded.zpow_smul_repr_self (- 3 : ℤ) (by omega)).comp_sub_right r₀)) := by
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, threeDimPointParticle_scalarPotential,
    smul_eq_mul, threeDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg, zpow_neg]
  rw [constantTime_distSpaceGrad, distOfFunction_mul_fun _
    (IsDistBounded.inv_shift r₀)]
  simp only [map_smul]
  trans -(q / (4 * π * 𝓕.ε₀)) • (constantTime <| distGrad <| distTranslate (basis.repr r₀) <|
    (distOfFunction (fun x => ‖x‖⁻¹) (IsDistBounded.inv)))
  · simp [distTranslate_ofFunction]
  rw [Space.distTranslate_distGrad]
  have := Space.distGrad_distOfFunction_norm_zpow (d := 2) (-1) (by grind)
  simp_all [distOfFunction_neg, distTranslate_ofFunction]

/-!

### B.1. the time derivative of the electric field

-/

@[simp]
lemma threeDimPointParticle_electricField_timeDeriv (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    Space.distTimeDeriv ((threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c) = 0 := by
  rw [threeDimPointParticle_electricField]
  simp

/-!

## C. The magnetic field

-/

@[simp]
lemma threeDimPointParticle_magneticFieldMatrix (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).magneticFieldMatrix 𝓕.c = 0 := by
  ext η
  simp [magneticFieldMatrix_eq_vectorPotential]

/-!

## D. Maxwell's equations

-/

lemma threeDimPointParticle_div_electricField {𝓕} (q : ℝ) (r₀ : Space 3) :
    distSpaceDiv ((threeDimPointParticle 𝓕 q r₀).electricField 𝓕.c) =
    (1/𝓕.ε₀) • constantTime (q • diracDelta ℝ r₀) := by
  rw [threeDimPointParticle_electricField]
  simp only [Int.reduceNeg, zpow_neg, map_smul, smul_smul]
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 2)
  simp at h1
  trans (q / (4 * π * 𝓕.ε₀)) •
    distSpaceDiv (constantTime <|
    distTranslate (basis.repr r₀) <|
    (distOfFunction (fun x => ‖x‖ ^ (-3 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 3 : ℤ) (by omega))))
  · ext η
    simp [distTranslate_ofFunction]
  simp
  rw [constantTime_distSpaceDiv, distDiv_distTranslate, h1]
  simp only [map_smul]
  suffices h : volume.real (Metric.ball (0 : Space 3) 1) = (4/3 * Real.pi) by
    rw [h]
    simp [smul_smul]
    ext η
    simp [constantTime_apply, diracDelta_apply, distTranslate_apply]
    left
    ring_nf
    field_simp
  simp [MeasureTheory.Measure.real]
  exact pi_nonneg

lemma threeDimPointParticle_isExterma (𝓕 : FreeSpace) (q : ℝ) (r₀ : Space 3) :
    (threeDimPointParticle 𝓕 q r₀).IsExtrema 𝓕 (threeDimPointParticleCurrentDensity 𝓕.c q r₀) := by
  rw [isExtrema_iff_components]
  apply And.intro
  · intro ε
    rw [gradLagrangian_sum_inl_0]
    simp
    rw [threeDimPointParticle_div_electricField]
    simp
    field_simp
    simp [𝓕.c_sq]
    right
    field_simp
    simp
  · intro ε i
    rw [gradLagrangian_sum_inr_i]
    simp

end DistElectromagneticPotential
end Electromagnetism
