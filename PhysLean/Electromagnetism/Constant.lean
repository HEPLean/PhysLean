/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.KineticTerm
import PhysLean.ClassicalMechanics.VectorFields
/-!

# The constant electric and magnetic fields

## i. Overview

In this module we define the electromagnetic potential which gives rise to a
given constant electric and magnetic field in 3d.

We show that the kinetic term for this potential has a varaiational gradient equal to
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

/-- An electric potential in 3d which gives a given constant E-field and B-field. -/
noncomputable def constantEB (E₀ B₀ : EuclideanSpace ℝ (Fin 3)) : ElectromagneticPotential 3 :=
  fun x μ =>
  match μ with
  | Sum.inl _ => -⟪E₀, x.space⟫_ℝ
  | Sum.inr i => (1/2) * (B₀ ⨯ₑ₃ x.space) i

/-!

## B. Smoothness of the potential

The potential `constantEB E₀ B₀` is smooth.

-/

lemma constantEB_smooth {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    ContDiff ℝ ∞ (constantEB E₀ B₀) := by
  rw [contDiff_euclidean]
  intro μ
  match μ with
  | Sum.inl _ =>
      simp [constantEB]
      apply ContDiff.neg
      apply ContDiff.inner
      · fun_prop
      · change ContDiff ℝ ∞ SpaceTime.space
        fun_prop
  | Sum.inr i =>
      fin_cases i
      all_goals
        simp [constantEB, cross_apply]
        apply ContDiff.mul
        · fun_prop
        apply ContDiff.sub
        · fun_prop
        · fun_prop

/-!

## C. The scalar potential

The scalar potential for `constantEB E₀ B₀` is given by `-⟪E₀, x⟫`.

-/

lemma constantEB_scalarPotential {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    (constantEB E₀ B₀).scalarPotential = fun _ x => -⟪E₀, x⟫_ℝ := by
  ext t x
  simp only [scalarPotential, timeSlice, constantEB, space_toCoord_symm, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]
  rfl

/-!

## D. The vector potential

The vector potential for `constantEB E₀ B₀` is given by `(1/2) B₀ × x`.

-/

lemma constantEB_vectorPotential {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    (constantEB E₀ B₀).vectorPotential = fun _ x => (1/2 : ℝ) • B₀ ⨯ₑ₃ x := by
  ext t x i
  simp [vectorPotential, timeSlice, constantEB, space_toCoord_symm, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]
  rfl

/-!

## E. The electric field

The electric field for `constantEB E₀ B₀` is given by `E₀`.

-/

@[simp]
lemma constantEB_electricField {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    (constantEB E₀ B₀).electricField = fun _ _ => E₀ := by
  funext t x
  rw [electricField_eq]
  simp
  rw [constantEB_vectorPotential]
  simp
  rw [Time.deriv_eq, fderiv_fun_const]
  simp
  rw [constantEB_scalarPotential]
  simp
  erw [Space.grad_neg]
  rw [Space.grad_inner_right]
  simp

/-!

## F. The magnetic field

The magnetic field for `constantEB E₀ B₀` is given by `B₀`.

-/

@[simp]
lemma constantEB_magneticField {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    (constantEB E₀ B₀).magneticField = fun _ _ => B₀ := by
  funext t x
  rw [magneticField_eq]
  simp
  rw [constantEB_vectorPotential]
  simp
  ext i
  fin_cases i
  all_goals
  · simp [Space.curl, Space.coord, cross_apply]
    rw [Space.deriv_eq, Space.deriv_eq]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    simp
    repeat rw [← Space.deriv_eq]
    repeat rw [Space.deriv_component]
    simp
    ring

/-!

## G. The kinetic term

The kinetic term for `constantEB E₀ B₀` is given by `1/2 (‖E₀‖² - ‖B₀‖²)`.
Note this is not the same as the kinetic energy.

-/

lemma constantEB_kineticTerm {E₀ B₀ : EuclideanSpace ℝ (Fin 3)}
    (x : SpaceTime 3) :
    (constantEB E₀ B₀).kineticTerm x = 1/2 * (‖E₀‖ ^ 2 - ‖B₀‖ ^ 2) := by
  obtain ⟨t, rfl⟩ := SpaceTime.toTimeAndSpace.symm.surjective x
  rw [kineticTerm_eq_electric_magnetic]
  simp
  exact constantEB_smooth.differentiable (ENat.LEInfty.out)

/-!

## H. The variational gradient of the kinetic term

The variational gradient of the kinetic term for `constantEB E₀ B₀` is equal to zero.

-/

lemma constantEB_gradKineticTerm {E₀ B₀ : EuclideanSpace ℝ (Fin 3)} :
    (constantEB E₀ B₀).gradKineticTerm = 0 := by
  funext x
  rw [gradKineticTerm_eq_electric_magnetic]
  rw [constantEB_electricField, constantEB_magneticField]
  simp
  apply Finset.sum_eq_zero
  intro x _
  rw [Time.deriv, fderiv_fun_const]
  simp
  exact constantEB_smooth

end ElectromagneticPotential

end Electromagnetism
