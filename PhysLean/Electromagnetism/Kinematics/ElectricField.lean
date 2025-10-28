/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.VectorPotential
import PhysLean.Electromagnetism.Kinematics.ScalarPotential
import PhysLean.Electromagnetism.Kinematics.FieldStrength
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# The Electric Field

## i. Overview

The electric field is defined in terms of the electromagnetic potential `A` as
`E = - ∇ φ - ∂ₜ \vec A`.

In this module we define the electric field, and prove lemmas about it.

## ii. Key results

- `electricField` : The electric field from the electromagnetic potential.
- `electricField_eq_fieldStrengthMatrix` : The electric field expressed in terms of the
  field strength tensor.

## iii. Table of contents

- A. Definition of the Electric Field
- B. Relation to the field strength tensor
- C. Smoothness of the electric field
- D. Differentiability of the electric field
- E. Time derivative of the vector potential in terms of the electric field

## iv. References

-/
namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

open Space Time

/-!

## A. Definition of the Electric Field

-/

/-- The electric field from the electromagnetic potential. -/
noncomputable def electricField {d} (A : ElectromagneticPotential d) : ElectricField d :=
  fun t x => - ∇ (A.scalarPotential t) x - ∂ₜ (fun t => A.vectorPotential t x) t

lemma electricField_eq (A : ElectromagneticPotential d) :
    A.electricField = fun t x =>
      - ∇ (A.scalarPotential t) x - ∂ₜ (fun t => A.vectorPotential t x) t := rfl

/-!

## B. Relation to the field strength tensor

-/

lemma electricField_eq_fieldStrengthMatrix (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) (hA : Differentiable ℝ A) :
    A.electricField t x i = -
    A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inl 0, Sum.inr i) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add, neg_add_rev]
  rw [electricField]
  simp only [PiLp.sub_apply, PiLp.neg_apply, Fin.isValue]
  congr
  · rw [Space.grad_apply]
    trans ∂_ (Sum.inr i) (fun x => A x (Sum.inl 0)) (toTimeAndSpace.symm (t, x)); swap
    · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq]
      rw [fderiv_pi]
      rfl
      · exact fun μ => (differentiable_component A hA μ).differentiableAt
    · rw [SpaceTime.deriv_sum_inr]
      simp
      rfl
      · exact fun μ => (differentiable_component A hA _).differentiableAt
  · rw [SpaceTime.deriv_sum_inl]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [Time.deriv_eq, Time.deriv_eq]
    rw [vectorPotential]
    simp [timeSlice]
    rw [fderiv_pi, fderiv_pi]
    rfl
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA μ)
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA (Sum.inr μ))
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop
    · exact hA

/-!

## C. Smoothness of the electric field

-/

lemma electricField_contDiff {n} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (↿A.electricField) := by
  rw [@contDiff_euclidean]
  intro i
  conv =>
    enter [3, x];
    change A.electricField x.1 x.2 i
    rw [electricField_eq_fieldStrengthMatrix (A) x.1 x.2 i (hA.differentiable (by simp))]
    change - A.fieldStrengthMatrix (toTimeAndSpace.symm (x.1, x.2)) (Sum.inl 0, Sum.inr i)
  apply ContDiff.neg
  change ContDiff ℝ n ((fun x => A.fieldStrengthMatrix x (Sum.inl 0, Sum.inr i))
    ∘ (toTimeAndSpace (d := d)).symm)
  refine ContDiff.comp ?_ ?_
  · exact fieldStrengthMatrix_contDiff (hA)
  · exact ContinuousLinearEquiv.contDiff toTimeAndSpace.symm

lemma electricField_apply_contDiff {n} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (↿(fun t x => A.electricField t x i)) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿A.electricField)
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · exact electricField_contDiff hA

lemma electricField_apply_contDiff_space {n} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) (t : Time) :
    ContDiff ℝ n (fun x => A.electricField t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿A.electricField ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · refine ContDiff.comp ?_ ?_
    · exact electricField_contDiff hA
    · fun_prop

lemma electricField_apply_contDiff_time {n} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) :
    ContDiff ℝ n (fun t => A.electricField t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿A.electricField ∘ fun t => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · refine ContDiff.comp ?_ ?_
    · exact electricField_contDiff hA
    · fun_prop

/-!

## D. Differentiability of the electric field

-/

lemma electricField_differentiable {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) : Differentiable ℝ (↿A.electricField) := by
  rw [differentiable_pi]
  intro i
  conv =>
    enter [2, x];
    change A.electricField x.1 x.2 i
    rw [electricField_eq_fieldStrengthMatrix (A) x.1 x.2 i (hA.differentiable (by simp))]
    change - A.fieldStrengthMatrix (toTimeAndSpace.symm (x.1, x.2)) (Sum.inl 0, Sum.inr i)
  apply Differentiable.neg
  change Differentiable ℝ ((fun x => A.fieldStrengthMatrix x (Sum.inl 0, Sum.inr i))
    ∘ (toTimeAndSpace (d := d)).symm)
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable (hA)
  · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm

lemma electricField_differentiable_time {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) (x : Space d) : Differentiable ℝ (A.electricField · x) := by
  change Differentiable ℝ (↿A.electricField ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact electricField_differentiable hA
  · fun_prop

lemma electricField_differentiable_space {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) (t : Time) : Differentiable ℝ (A.electricField t) := by
  change Differentiable ℝ (↿A.electricField ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact electricField_differentiable hA
  · fun_prop

lemma electricField_apply_differentiable_space {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => A.electricField t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (A.electricField t))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)
  · exact electricField_differentiable_space hA t

/-!

## E. Time derivative of the vector potential in terms of the electric field

-/

lemma time_deriv_vectorPotential_eq_electricField {d} (A : ElectromagneticPotential d)
    (t : Time) (x : Space d) :
    ∂ₜ (fun t => A.vectorPotential t x) t =
    - A.electricField t x - ∇ (A.scalarPotential t) x := by
  rw [electricField]
  abel

lemma time_deriv_comp_vectorPotential_eq_electricField {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (fun t => A.vectorPotential t x i) t =
    - A.electricField t x i - ∂[i] (A.scalarPotential t) x := by
  rw [Time.deriv_euclid, time_deriv_vectorPotential_eq_electricField]
  simp
  rfl
  apply vectorPotential_differentiable_time A hA x

end ElectromagneticPotential

end Electromagnetism
