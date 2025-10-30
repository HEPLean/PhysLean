/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.IsExtrema
import PhysLean.ClassicalMechanics.VectorFields
/-!

# The constant electric and magnetic fields

## i. Overview

In this module we define the electromagnetic potential which gives rise to a
given constant electric and magnetic field matrix.

We show that the kinetic term for this potential has a variational gradient equal to
zero, i.e. it satisfies the source-free Maxwell equations.

## ii. Key results

- `ElectromagneticPotential.constantEB E₀ B₀` : An electromagnetic potential which gives rise to a
  given constant electric field `E₀` and magnetic field `B₀` in 3d.
- `ElectromagneticPotential.constantEB_gradKineticTerm` : The variational gradient of the kinetic
  term for the potential `constantEB E₀ B₀` is equal to zero.

## iii. Table of contents

- A. The definition of the potential
- B. Smoothness of the potential
- C. The scalar potential
- D. The vector potential
- E. The electric field
- F. The magnetic field
- G. The kinetic term
- H. The variational gradient of the kinetic term

## iv. References

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor ContDiff

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The definition of the potential

The potential which gives rise to a constant electric field `E₀` and magnetic field `B₀` in 3d is
given by
`(- ⟪E₀, x⟫, (1/2) B₀ × x)`
where `x` is the spatial position vector.

-/
open Matrix
set_option linter.unusedVariables false
/-- An electric potential in 3d which gives a given constant E-field and B-field. -/
@[nolint unusedArguments]
noncomputable def constantEB {d : ℕ} (c : SpeedOfLight)
    (E₀ : EuclideanSpace ℝ (Fin d)) (B₀ : Fin d × Fin d → ℝ)
    (B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)) : ElectromagneticPotential d :=
  fun x μ =>
  match μ with
  | Sum.inl _ => - (1/c) * ⟪E₀, x.space⟫_ℝ
  | Sum.inr i => (1/2) * ∑ j, B₀ (i, j) * x.space j

/-!

## B. Smoothness of the potential

The potential `constantEB E₀ B₀` is smooth.

-/

lemma constantEB_smooth {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    ContDiff ℝ ∞ (constantEB c E₀ B₀ B₀_antisymm) := by
  rw [contDiff_euclidean]
  intro μ
  match μ with
  | Sum.inl _ =>
      simp [constantEB]
      apply ContDiff.neg
      apply ContDiff.mul
      · fun_prop
      apply ContDiff.inner
      · fun_prop
      · change ContDiff ℝ ∞ SpaceTime.space
        fun_prop
  | Sum.inr i =>
      simp [constantEB]
      apply ContDiff.mul
      · fun_prop
      · apply ContDiff.sum
        intro j _
        apply ContDiff.mul
        · fun_prop
        fun_prop

/-!

## C. The scalar potential

The scalar potential for `constantEB E₀ B₀` is given by `-⟪E₀, x⟫`.

-/

lemma constantEB_scalarPotential {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).scalarPotential c = fun _ x => -⟪E₀, x⟫_ℝ := by
  ext t x
  simp [scalarPotential, timeSlice, constantEB, space_toCoord_symm, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]


/-!

## D. The vector potential

The vector potential for `constantEB E₀ B₀` is given by `(1/2) B₀ × x`.

-/

lemma constantEB_vectorPotential {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).vectorPotential c = fun _ x i =>
      (1 / 2) * ∑ j, B₀ (i, j) * x j := by
  ext t x i
  simp [vectorPotential, timeSlice, constantEB, space_toCoord_symm, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]

/-!

### D.1. Time derivative of the vector potential

-/
open Time

@[simp]
lemma constantEB_vectorPotential_time_deriv {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} (t : Time) (x : Space d) :
    ∂ₜ ((constantEB c E₀ B₀ B₀_antisymm).vectorPotential c ·  x) t = 0 := by
  rw [constantEB_vectorPotential]
  simp

/-!

### D.2. Space derivative of the vector potential

-/

lemma constantEB_vectorPotential_space_deriv {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} (t : Time) (x : Space d) (i j : Fin d):
    Space.deriv i ((constantEB c E₀ B₀ B₀_antisymm).vectorPotential c t · j) x =
       (1 / 2) *  B₀ (j, i) := by
  rw [constantEB_vectorPotential]
  rw [Space.deriv_eq]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  simp
  rw [Finset.sum_eq_single i]
  · rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq]
  · intro k _ hk
    rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq]
    rw [Space.deriv_component_diff]
    simp
    exact id (Ne.symm hk)
  · simp


/-!

## E. The electric field

The electric field for `constantEB E₀ B₀` is given by `E₀`.

-/

@[simp]
lemma constantEB_electricField  {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).electricField c = fun _ _ => E₀ := by
  funext t x
  rw [electricField_eq]
  simp [constantEB_scalarPotential]
  erw [Space.grad_neg]
  rw [Space.grad_inner_right]
  simp

/-!

## F. The magnetic field

The magnetic field for `constantEB E₀ B₀` is given by `B₀`.

-/

@[simp]
lemma constantEB_magneticFieldMatrix {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).magneticFieldMatrix c = fun _ _ => B₀ := by
  funext t x
  funext i
  match i with
  | (i, j) =>
  rw [magneticFieldMatrix_eq_vectorPotential]
  rw [constantEB_vectorPotential_space_deriv, constantEB_vectorPotential_space_deriv]
  conv_lhs =>
    enter [2]
    rw [B₀_antisymm]
  ring
  apply constantEB_smooth.differentiable (by simp)

/-!

## G. Is extrema

-/

lemma constantEB_isExtrema {𝓕 : FreeSpace}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    IsExtrema 𝓕 (constantEB 𝓕.c E₀ B₀ B₀_antisymm) 0 := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix]
  · intro t x
    simp
  · exact constantEB_smooth
  · exact contDiff_zero_fun

end ElectromagneticPotential

end Electromagnetism
