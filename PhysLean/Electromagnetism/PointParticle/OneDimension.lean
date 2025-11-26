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

- `oneDimPointParticle` : The electromagnetic potential of a point particle
  stationary at the origin of 1d space.
- `oneDimPointParticle_gaussLaw` : The electric field of a point
  particle stationary at the origin of 1d space satisfies Gauss' law.

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

## A. The Potentials

-/

/-!

### A.1. The electromagnetic potential

-/


/-- The electromagnetic potential of a point particle stationary at the origin
  of 1d space. -/
noncomputable def DistElectromagneticPotential.oneDimPointParticle (q : ℝ) :
    DistElectromagneticPotential 1 := SpaceTime.distTimeSlice.symm <| Space.constantTime <|
  distOfFunction (fun x => ((- q/(2)) * ‖x‖) • Lorentz.Vector.basis (Sum.inl 0)) (by fun_prop)

/-

### A.2. The vector potential is zero

-/

@[simp]
lemma DistElectromagneticPotential.oneDimPointParticle_vectorPotential(q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle q).vectorPotential 1 = 0 := by
  ext ε i
  simp [vectorPotential, Lorentz.Vector.spatialCLM,
    oneDimPointParticle, constantTime_apply, distOfFunction_vector_eval]

/-!

### A.3. The scalar potential

-/

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

## B. The electric field

-/

lemma DistElectromagneticPotential.oneDimPointParticle_electricField (q : ℝ) :
    (DistElectromagneticPotential.oneDimPointParticle q).electricField 1 =
    (q / 2) • constantTime (distOfFunction (fun x : Space 1 => ‖x‖ ^ (- 1 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 1 : ℤ) (by omega))) := by
  have h1 := Space.distGrad_distOfFunction_norm_zpow (d := 0) 1 (by grind)
  simp at h1
  simp only [electricField, LinearMap.coe_mk, AddHom.coe_mk, oneDimPointParticle_scalarPotential,
    smul_eq_mul, neg_mul, oneDimPointParticle_vectorPotential, map_zero, sub_zero, Int.reduceNeg,
    zpow_neg, zpow_one]
  rw [constantTime_distSpaceGrad, distOfFunction_neg, distOfFunction_mul_fun _ (by fun_prop)]
  simp only [map_neg, map_smul, neg_neg, h1]

/-!

## D. Maxwell's equations

-/

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


end Electromagnetism
