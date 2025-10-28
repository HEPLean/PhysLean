/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.ElectricField
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
import PhysLean.ClassicalMechanics.VectorFields

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

### E.4. The magnetic field

-/

/-- The magnetic field from the electromagnetic potential. -/
noncomputable def magneticField (A : ElectromagneticPotential) : MagneticField :=
  fun t x => (∇ × (A.vectorPotential t)) x

lemma magneticField_eq (A : ElectromagneticPotential) :
    A.magneticField = fun t x => (∇ × (A.vectorPotential t)) x := rfl

/-!

#### E.4.1. Relation between the magnetic field and the field strength matrix

-/

lemma magneticField_fst_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField t x 0 =
    - A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inr 1, Sum.inr 2) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add, neg_add_rev, neg_neg]
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, fderiv_pi]
    rfl
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA μ)
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop

lemma magneticField_snd_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField t x 1 = A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x))
      (Sum.inr 0, Sum.inr 2) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, fderiv_pi]
    rfl
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA μ)
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop

lemma magneticField_thd_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField t x 2 =
    - A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inr 0, Sum.inr 1) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add, neg_add_rev, neg_neg]
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, fderiv_pi]
    rfl
    · intro μ
      apply Differentiable.differentiableAt
      have h1 := (differentiable_component A hA μ)
      apply Differentiable.comp h1
      refine Differentiable.fun_comp ?_ ?_
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop

/-!

#### E.4.2. Divergence of the magnetic field

-/

lemma magneticField_div_eq_zero (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) : Space.div (A.magneticField t) = 0 := by
  rw [magneticField_eq]
  simp
  rw [Space.div_of_curl_eq_zero]
  exact vectorPotential_contDiff_space A hA t

/-!

### E.5. Magnetic field matrix

-/

noncomputable def magneticFieldMatrix (A : ElectromagneticPotential d) :
    Time → Space d → (Fin d × Fin d) → ℝ := timeSlice <| fun x ij =>
    A.fieldStrengthMatrix x (Sum.inr ij.1, Sum.inr ij.2)

lemma magneticFieldMatrix_eq (A : ElectromagneticPotential d) :
    A.magneticFieldMatrix = fun t x ij =>
      A.fieldStrengthMatrix (toTimeAndSpace.symm (t, x)) (Sum.inr ij.1, Sum.inr ij.2) := rfl

lemma magneticFieldMatrix_antisymm (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix t x (i, j) = - A.magneticFieldMatrix t x (j, i) := by
  rw [magneticFieldMatrix_eq]
  exact fieldStrengthMatrix_antisymm A (toTimeAndSpace.symm (t, x)) (Sum.inr i) (Sum.inr j)

@[simp]
lemma magneticFieldMatrix_diag_eq_zero (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) :
    A.magneticFieldMatrix t x (i, i) = 0 := by
  rw [magneticFieldMatrix_eq]
  exact fieldStrengthMatrix_diag_eq_zero A (toTimeAndSpace.symm (t, x)) (Sum.inr i)

lemma magneticField_eq_magneticFieldMatrix (A : ElectromagneticPotential)
    (hA : Differentiable ℝ A) :
    A.magneticField = fun t x i =>
      match i with
      | 0 => - A.magneticFieldMatrix t x (1, 2)
      | 1 => A.magneticFieldMatrix t x (0, 2)
      | 2 => - A.magneticFieldMatrix t x (0, 1) := by
  rw [magneticFieldMatrix_eq]
  funext t x i
  fin_cases i
  · simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
  · simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
  · simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]

lemma magneticField_curl_eq_magneticFieldMatrix (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) :
    (∇ × A.magneticField t) x i = ∑ j, Space.deriv j (A.magneticFieldMatrix t · (j, i)) x:= by
  rw [magneticField_eq_magneticFieldMatrix A (hA.differentiable (by simp))]
  simp [Space.curl, Space.coord]
  fin_cases i
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    Fin.zero_eta, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero, fderiv_fun_const,
    Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_add]
    conv_lhs =>
      enter [2, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    conv_lhs =>
      enter [1, 1, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    simp
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    sub_neg_eq_add, Fin.mk_one, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero,
    fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, add_zero]
    conv_lhs =>
      enter [1, 1, 1, 2, x]
      rw [magneticFieldMatrix_antisymm]
    simp
    ring
  · simp only [Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
    sub_neg_eq_add, Fin.reduceFinMk, Fin.sum_univ_three, magneticFieldMatrix_diag_eq_zero,
    fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, add_zero]

lemma magneticFieldMatrix_eq_vectorPotential (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix t x (i, j) = Space.deriv j (A.vectorPotential t · i) x -
    Space.deriv i (A.vectorPotential t · j) x := by
  rw [magneticFieldMatrix_eq]
  simp
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp
  rw [SpaceTime.deriv_sum_inr _ hA, SpaceTime.deriv_sum_inr _ hA]
  simp [vectorPotential]
  rw [add_comm]
  congr
  all_goals
  · rw [← Space.deriv_lorentz_vector]
    rfl
    apply Differentiable.comp
    · exact hA
    · apply Differentiable.fun_comp
      · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm
      · fun_prop

/-!

### E.5.1. Differentiablity of the magnetic field matrix
-/

lemma magneticFieldMatrix_contDiff {n} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (ij) : ContDiff ℝ n ↿(fun t x => A.magneticFieldMatrix t x ij) := by
  simp [magneticFieldMatrix_eq]
  change ContDiff ℝ n ((A.fieldStrengthMatrix · (Sum.inr ij.1, Sum.inr ij.2)) ∘
    toTimeAndSpace.symm)
  refine ContDiff.comp ?_ ?_
  · exact fieldStrengthMatrix_contDiff (hA)
  · exact ContinuousLinearEquiv.contDiff toTimeAndSpace.symm

lemma magneticFieldMatrix_space_contDiff {n} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (t : Time) (ij) :
    ContDiff ℝ n (fun x => A.magneticFieldMatrix t x ij) := by
  change ContDiff ℝ n (↿(fun t x => A.magneticFieldMatrix t x ij) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact magneticFieldMatrix_contDiff A hA ij
  · fun_prop

lemma magneticFieldMatrix_time_contDiff {n} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) (ij) :
    ContDiff ℝ n (fun t => A.magneticFieldMatrix t x ij) := by
  change ContDiff ℝ n (↿(fun t x => A.magneticFieldMatrix t x ij) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact magneticFieldMatrix_contDiff A hA ij
  · fun_prop

lemma magneticFieldMatrix_differentiable (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (ij) : Differentiable ℝ ↿(fun t x => A.magneticFieldMatrix t x ij) := by
  simp [magneticFieldMatrix_eq]
  change Differentiable ℝ ((A.fieldStrengthMatrix · (Sum.inr ij.1, Sum.inr ij.2)) ∘
    toTimeAndSpace.symm)
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable (hA)
  · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm

lemma magneticFieldMatrix_differentiable_space (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (ij) :
    Differentiable ℝ (fun x => A.magneticFieldMatrix t x ij) := by
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix t x ij) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact magneticFieldMatrix_differentiable A hA ij
  · fun_prop

lemma magneticFieldMatrix_differentiable_time (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (x : Space d) (ij) :
    Differentiable ℝ (fun t => A.magneticFieldMatrix t x ij) := by
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix t x ij) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact magneticFieldMatrix_differentiable A hA ij
  · fun_prop

/-!

### E.5.2. Space derivative of the magnetic field matrix

-/

lemma magneticFieldMatrix_space_deriv_eq (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j k : Fin d) :
    ∂[k] (A.magneticFieldMatrix t · (i, j)) x =
    ∂[i] (A.magneticFieldMatrix t · (k, j)) x
    - ∂[j] (A.magneticFieldMatrix t · (k, i)) x := by
  conv_lhs =>
    enter [2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x i j]
  conv_rhs =>
    enter [1, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  conv_rhs =>
    enter [2, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  conv_lhs =>
    rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub]
  simp [← Space.deriv_eq_fderiv_basis]
  conv_rhs =>
    rw [Space.deriv_eq_fderiv_basis]
    enter [2]
    rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub, fderiv_fun_sub]
  simp [← Space.deriv_eq_fderiv_basis]
  conv_lhs =>
    rw [Space.deriv_commute _ (vectorPotential_apply_contDiff_space _ hA _ _)]
    enter [2]
    rw [Space.deriv_commute _ ((vectorPotential_apply_contDiff_space _ hA _ _))]
  conv_rhs =>
    enter [1, 1]
    rw [Space.deriv_commute _ ((vectorPotential_apply_contDiff_space _ hA _ _))]
  ring
  all_goals
  · apply Differentiable.differentiableAt
    apply Space.deriv_differentiable
    apply vectorPotential_apply_contDiff_space _ hA

/-!

### E.5. Field strength matrix in terms of the electric and magnetic fields

-/

lemma fieldStrengthMatrix_eq_electric_magnetic (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x)) (μ, ν) =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField t x i
    | Sum.inr i, Sum.inl 0 => A.electricField t x i
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField t x 2
    | 0, 2 => A.magneticField t x 1
    | 1, 0 => A.magneticField t x 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField t x 0
    | 2, 0 => - A.magneticField t x 1
    | 2, 1 => A.magneticField t x 0
    | 2, 2 => 0 := by
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => simp
  | Sum.inl 0, Sum.inr i => simp [electricField_eq_fieldStrengthMatrix A t x i hA]
  | Sum.inr i, Sum.inl 0 =>
    simp [electricField_eq_fieldStrengthMatrix A t x i hA]
    exact fieldStrengthMatrix_antisymm A (toTimeAndSpace.symm (t, x)) (Sum.inr i) (Sum.inl 0)
  | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => simp
    | 0, 1 =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
    | 0, 2 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
    | 1, 0 =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 1, 1 => simp
    | 1, 2 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
    | 2, 0 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 2, 1 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    | 2, 2 => simp

lemma fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime (A : ElectromagneticPotential)
    (x : SpaceTime) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    let tx := SpaceTime.toTimeAndSpace x
    A.fieldStrengthMatrix x (μ, ν) =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField tx.1 tx.2 i
    | Sum.inr i, Sum.inl 0 => A.electricField tx.1 tx.2 i
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField tx.1 tx.2 2
    | 0, 2 => A.magneticField tx.1 tx.2 1
    | 1, 0 => A.magneticField tx.1 tx.2 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField tx.1 tx.2 0
    | 2, 0 => - A.magneticField tx.1 tx.2 1
    | 2, 1 => A.magneticField tx.1 tx.2 0
    | 2, 2 => 0 := by
  dsimp
  rw [← fieldStrengthMatrix_eq_electric_magnetic A]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact hA

lemma time_deriv_magneticFieldMatrix {d : ℕ} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix · x (i, j)) t =
    ∂[i] (A.electricField t · j) x - ∂[j] (A.electricField t · i) x := by
  calc _
    _ = ∂ₜ (fun t => ∂[j] (fun x => A.vectorPotential t x i) x) t
        - ∂ₜ (fun t => ∂[i] (fun x => A.vectorPotential t x j) x) t := by
      conv_lhs =>
        enter [1, t]
        rw [magneticFieldMatrix_eq_vectorPotential _ (hA.differentiable (by simp))]
      rw [Time.deriv, fderiv_fun_sub]
      rfl
      all_goals
      · apply Differentiable.differentiableAt
        apply ClassicalMechanics.space_deriv_differentiable_time
        apply vectorPotential_comp_contDiff _ hA
    _ = ∂[j] (fun x => ∂ₜ (fun t => A.vectorPotential t x i) t) x
        - ∂[i] (fun x => ∂ₜ (fun t => A.vectorPotential t x j) t) x := by
      rw [ClassicalMechanics.time_deriv_comm_space_deriv _]
      rw [ClassicalMechanics.time_deriv_comm_space_deriv _]
      all_goals
      · apply vectorPotential_comp_contDiff _ hA
    _ = ∂[i] (A.electricField t · j) x - ∂[j] (A.electricField t · i) x := by
      conv_lhs =>
        enter [1, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      conv_lhs =>
        enter [2, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space A hA t), fderiv_fun_neg]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space A hA t), fderiv_fun_neg]
      conv_lhs =>
        enter [1]
        simp
        enter [2]
        rw [← Space.deriv_eq_fderiv_basis, Space.deriv_commute _
          (scalarPotential_contDiff_space A hA t)]
      simp [← Space.deriv_eq_fderiv_basis]
      ring

end ElectromagneticPotential

end Electromagnetism
