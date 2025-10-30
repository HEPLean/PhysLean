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
noncomputable def electricField {d} (c : SpeedOfLight := 1)
    (A : ElectromagneticPotential d) : ElectricField d :=
  fun t x => - ∇ (A.scalarPotential c t) x - ∂ₜ (fun t => A.vectorPotential c t x) t

lemma electricField_eq {c : SpeedOfLight} (A : ElectromagneticPotential d) :
    A.electricField c = fun t x =>
      - ∇ (A.scalarPotential c t) x - ∂ₜ (fun t => A.vectorPotential c t x) t := rfl

/-!

## B. Relation to the field strength tensor

The electric field can be expressed in terms of the field strength tensor as
`E_i = - c * F_0^i`.
-/

lemma electricField_eq_fieldStrengthMatrix {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) (hA : Differentiable ℝ A) :
    A.electricField c t x i = -
    c * A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) (Sum.inl 0, Sum.inr i) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add]
  rw [electricField]
  simp only [PiLp.sub_apply, PiLp.neg_apply, Fin.isValue, mul_add, neg_add_rev]
  congr
  · rw [Space.grad_apply]
    trans c * ∂_ (Sum.inr i) (fun x => A x (Sum.inl 0)) ((toTimeAndSpace c).symm (t, x)); swap
    · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq]
      rw [fderiv_pi]
      rfl
      · exact fun μ => (differentiable_component A hA μ).differentiableAt
    · rw [SpaceTime.deriv_sum_inr c]
      simp [scalarPotential]
      change Space.deriv i (fun y => c * A ((toTimeAndSpace c).symm (t, y)) (Sum.inl 0)) x = _
      rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul]
      simp [← Space.deriv_eq_fderiv_basis]
      · apply Differentiable.differentiableAt
        have h1 := (differentiable_component A hA (Sum.inl 0))
        apply Differentiable.comp h1
        refine Differentiable.fun_comp ?_ ?_
        · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
        · fun_prop
      · exact fun μ => (differentiable_component A hA _).differentiableAt
  · rw [SpaceTime.deriv_sum_inl c]
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
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA (Sum.inr μ))
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm
      · fun_prop
    · exact hA

lemma fieldStrengthMatrix_inl_inr_eq_electricField {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i : Fin d) (hA : Differentiable ℝ A) :
    A.fieldStrengthMatrix x (Sum.inl 0, Sum.inr i) =
    - (1 /c) * A.electricField c (x.time c) x.space i  := by
  rw [electricField_eq_fieldStrengthMatrix A (x.time c) x.space i hA]
  simp

lemma fieldStrengthMatrix_inr_inl_eq_electricField {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i : Fin d) (hA : Differentiable ℝ A) :
    A.fieldStrengthMatrix x (Sum.inr i, Sum.inl 0) =
    (1 /c) * A.electricField c (x.time c) x.space i  := by
  rw [electricField_eq_fieldStrengthMatrix A (x.time c) x.space i hA]
  simp
  rw [fieldStrengthMatrix_antisymm A x (Sum.inr i) (Sum.inl 0)]
/-!

## C. Smoothness of the electric field

-/

lemma electricField_contDiff {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n ↿(A.electricField c) := by
  rw [@contDiff_euclidean]
  intro i
  conv =>
    enter [3, x];
    change A.electricField c x.1 x.2 i
    rw [electricField_eq_fieldStrengthMatrix (A) x.1 x.2 i (hA.differentiable (by simp))]
    change - c * A.fieldStrengthMatrix ((toTimeAndSpace c).symm (x.1, x.2)) (Sum.inl 0, Sum.inr i)
  apply ContDiff.mul
  · fun_prop
  change ContDiff ℝ n ((fun x => A.fieldStrengthMatrix x (Sum.inl 0, Sum.inr i))
    ∘ (toTimeAndSpace c (d := d)).symm)
  refine ContDiff.comp ?_ ?_
  · exact fieldStrengthMatrix_contDiff hA
  · exact ContinuousLinearEquiv.contDiff (toTimeAndSpace c).symm

lemma electricField_apply_contDiff {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (↿(fun t x => A.electricField c t x i)) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.electricField c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · exact electricField_contDiff hA

lemma electricField_apply_contDiff_space {n} {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ (n + 1) A) (t : Time) :
    ContDiff ℝ n (fun x => A.electricField c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿(A.electricField c) ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · refine ContDiff.comp ?_ ?_
    · exact electricField_contDiff hA
    · fun_prop

lemma electricField_apply_contDiff_time {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) :
    ContDiff ℝ n (fun t => A.electricField c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿(A.electricField c) ∘ fun t => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) _
  · refine ContDiff.comp ?_ ?_
    · exact electricField_contDiff hA
    · fun_prop

/-!

## D. Differentiability of the electric field

-/

lemma electricField_differentiable {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) : Differentiable ℝ (↿(A.electricField c)) := by
  rw [differentiable_pi]
  intro i
  conv =>
    enter [2, x];
    change A.electricField c x.1 x.2 i
    rw [electricField_eq_fieldStrengthMatrix (A) x.1 x.2 i (hA.differentiable (by simp))]
    change - c * A.fieldStrengthMatrix ((toTimeAndSpace c).symm (x.1, x.2)) (Sum.inl 0, Sum.inr i)
  apply Differentiable.mul
  · fun_prop
  change Differentiable ℝ ((fun x => A.fieldStrengthMatrix x (Sum.inl 0, Sum.inr i))
    ∘ (toTimeAndSpace c (d := d)).symm)
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable (hA)
  · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm

lemma electricField_differentiable_time {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (x : Space d) : Differentiable ℝ (A.electricField c · x) := by
  change Differentiable ℝ (↿(A.electricField c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact electricField_differentiable hA
  · fun_prop

lemma electricField_differentiable_space {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (t : Time) : Differentiable ℝ (A.electricField c t) := by
  change Differentiable ℝ (↿(A.electricField c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact electricField_differentiable hA
  · fun_prop

lemma electricField_apply_differentiable_space {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => A.electricField c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (A.electricField c t))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)
  · exact electricField_differentiable_space hA t

/-!

## E. Time derivative of the vector potential in terms of the electric field

-/

lemma time_deriv_vectorPotential_eq_electricField {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (t : Time) (x : Space d) :
    ∂ₜ (fun t => A.vectorPotential c t x) t =
    - A.electricField c t x - ∇ (A.scalarPotential c t) x := by
  rw [electricField]
  abel

lemma time_deriv_comp_vectorPotential_eq_electricField {d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : Differentiable ℝ A)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (fun t => A.vectorPotential c t x i) t =
    - A.electricField c t x i - ∂[i] (A.scalarPotential c t) x := by
  rw [Time.deriv_euclid, time_deriv_vectorPotential_eq_electricField]
  simp
  rfl
  apply vectorPotential_differentiable_time A hA x

/-!

## F. Derivatives of the electric field in terms of field strength tensor

-/

open Space

lemma time_deriv_electricField_eq_fieldStrengthMatrix {d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight} (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (fun t => A.electricField c t x) t i =
    - c ^ 2 *  ∂_ (Sum.inl 0) (fun x => (A.fieldStrengthMatrix x) (Sum.inl 0, Sum.inr i))
    ((toTimeAndSpace c).symm (t, x)) := by
  rw [SpaceTime.deriv_sum_inl c]
  simp
  rw [← Time.deriv_euclid]
  conv_lhs =>
    enter [1, t]
    rw [electricField_eq_fieldStrengthMatrix (c := c) A t x i (hA.differentiable (by simp))]
  rw [Time.deriv_eq]
  rw [fderiv_const_mul]
  simp [← Time.deriv_eq]
  field_simp
  · apply Differentiable.differentiableAt
    apply fieldStrengthMatrix_differentiable_time hA
  · apply electricField_differentiable_time hA x
  · apply fieldStrengthMatrix_differentiable hA


lemma div_electricField_eq_fieldStrengthMatrix{d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight} (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) :
    (∇ ⬝ A.electricField c t) x =  c * ∑ (μ : (Fin 1 ⊕ Fin d)),
      (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inl 0)) ((toTimeAndSpace c).symm (t, x)))  := by
  rw [Finset.mul_sum]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, fieldStrengthMatrix_diag_eq_zero, SpaceTime.deriv_zero, Pi.ofNat_apply,
    mul_zero, zero_add]
  conv_rhs =>
    enter [2, i]
    rw [SpaceTime.deriv_sum_inr c _ (fieldStrengthMatrix_differentiable hA)]
    simp only [Fin.isValue]
  rw [Space.div]
  congr
  funext i
  simp [Space.coord]
  conv_lhs =>
    enter [2, y]
    rw [electricField_eq_fieldStrengthMatrix (c := c) A t y i (hA.differentiable (by simp))]
    rw [fieldStrengthMatrix_antisymm]
  rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul]
  simp [← Space.deriv_eq_fderiv_basis]
  apply Differentiable.differentiableAt
  apply Differentiable.neg
  apply fieldStrengthMatrix_differentiable_space hA
end ElectromagneticPotential

end Electromagnetism
