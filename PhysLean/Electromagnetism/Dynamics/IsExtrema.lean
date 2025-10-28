/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.Lagrangian


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
open Lorentz.Vector
open Time Space
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## C. Extrema of the Lagrangian density
-/

def IsExtrema {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : Prop :=
  gradLagrangian A J = 0

lemma isExtrema_iff_gradLagrangian (A : ElectromagneticPotential d) (J : LorentzCurrentDensity d):
    IsExtrema A J ↔  A.gradLagrangian J  = 0 := by rfl

lemma isExtrema_iff_fieldStrengthMatrix (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema A J ↔
    ∀ x, ∀ ν, ∑ μ, ∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x = J x ν := by
  rw [isExtrema_iff_gradLagrangian, gradLagrangian_eq_sum_fieldStrengthMatrix A hA J hJ, funext_iff]
  conv_lhs =>
    enter [x, 1, 2, ν]
    rw [smul_smul]
  simp only [Pi.zero_apply]
  trans ∀ x, ∀ ν, (η ν ν * (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)) = 0
  · apply Iff.intro
    · intro h x
      specialize h x
      have h' := linearIndependent_iff'.mp (Lorentz.Vector.basis.linearIndependent)
        Finset.univ
        (fun ν => (η ν ν * (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)))
         (by simpa using h)
      intro ν
      simpa using h' ν
    · intro h x
      simp [h x]
  apply Iff.intro
  · intro h x ν
    have h' := h x ν
    simp at h'
    have h'' : η ν ν ≠ 0 := by
      exact η_diag_ne_zero
    simp_all
    linear_combination h'
  · intro h x ν
    rw [h x]
    simp

lemma gaussLaw_electricField_of_isExtrema {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema A J)
    (t : Time) (x : Space d) : (∇ ⬝ (A.electricField t)) x = J.chargeDensity t x := by
  rw [isExtrema_iff_fieldStrengthMatrix A hA J hJ] at h
  specialize h (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inl 0)
  simp [LorentzCurrentDensity.chargeDensity]
  rw [← h]
  simp [Fintype.sum_sum_type, Space.div]
  congr
  funext i
  rw [SpaceTime.deriv_sum_inr]
  congr
  funext x
  simp [Space.coord_apply]
  rw [electricField_eq_fieldStrengthMatrix A t x i (hA.differentiable (by simp))]
  rw [fieldStrengthMatrix_antisymm]
  simp
  · refine fieldStrengthMatrix_differentiable ?_
    exact hA.of_le (ENat.LEInfty.out)

lemma ampereLaw_magneticFieldMatrix_of_isExtrema {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema A J)
    (t : Time) (x : Space d) (i : Fin d):
    ∂ₜ (fun t => A.electricField t x) t i =
      ∑ j, Space.deriv j (A.magneticFieldMatrix t · (j, i)) x - J.currentDensity t x i := by
  rw [isExtrema_iff_fieldStrengthMatrix A hA J hJ] at h
  specialize h (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inr i)
  simp [LorentzCurrentDensity.currentDensity]
  rw [← h]

  simp [Fintype.sum_sum_type]
  have h1 : ∂ₜ (fun t => A.electricField t x) t i =
       - ∂_ (Sum.inl 0) (fun x => (A.fieldStrengthMatrix x) (Sum.inl 0, Sum.inr i))
       (toTimeAndSpace.symm (t, x)) := by
    rw [SpaceTime.deriv_sum_inl _
      (fieldStrengthMatrix_differentiable (hA.of_le (ENat.LEInfty.out)))]
    trans ∂ₜ (fun t => A.electricField t x i) t
    · rw [Time.deriv_eq, Time.deriv_eq]
      trans (fderiv ℝ (EuclideanSpace.proj i ∘ fun t => A.electricField t x) t) 1;swap
      · rfl
      rw [fderiv_comp]
      simp
      · fun_prop
      · apply Differentiable.differentiableAt
        apply A.electricField_differentiable_time
        exact hA.of_le (ENat.LEInfty.out)
    · conv_lhs =>
        enter [1, t]
        rw [electricField_eq_fieldStrengthMatrix A t x i (hA.differentiable (by simp))]
      simp [Time.deriv_eq]
  have h2 : ∑ j, Space.deriv j (fun x => A.magneticFieldMatrix t x (j, i)) x  =
      ∑ a₂, ∂_ (Sum.inr a₂) (fun x => (A.fieldStrengthMatrix x) (Sum.inr a₂, Sum.inr i))
      (toTimeAndSpace.symm (t, x)) := by
    congr
    funext j
    rw [SpaceTime.deriv_sum_inr _
      (fieldStrengthMatrix_differentiable (hA.of_le (ENat.LEInfty.out)))]
    simp [magneticFieldMatrix ]
    rfl
  rw [h1, h2]
  simp

lemma isExtrema_iff_gauss_ampere_magneticFieldMatrix {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    IsExtrema A J ↔ ∀ x, ∀ t, (∇ ⬝ (A.electricField t)) x = J.chargeDensity t x
    ∧  ∀ i, ∂ₜ (fun t => A.electricField t x) t i =
    ∑ j, ∂[j] (A.magneticFieldMatrix t · (j, i)) x - J.currentDensity t x i := by
  apply Iff.intro
  · intro h x t
    apply And.intro
    · exact gaussLaw_electricField_of_isExtrema hA J hJ h t x
    · exact ampereLaw_magneticFieldMatrix_of_isExtrema hA J hJ h t x
  intro h
  rw [isExtrema_iff_fieldStrengthMatrix A hA J hJ]
  intro x ν
  match ν with
  | Sum.inl 0 =>
    have h1 := (h x.space x.time).1
    simp [Fintype.sum_sum_type]
    simp [LorentzCurrentDensity.chargeDensity] at h1
    rw [← h1]
    simp [Space.div]
    congr
    funext ν
    rw [SpaceTime.deriv_sum_inr]
    congr
    funext y
    simp [Space.coord_apply]
    rw [electricField_eq_fieldStrengthMatrix, fieldStrengthMatrix_antisymm]
    simp
    rfl
    · exact hA.differentiable (by simp)
    · apply fieldStrengthMatrix_differentiable
      exact hA.of_le (ENat.LEInfty.out)
  | Sum.inr i =>
    have hn := (h x.space x.time).2 i
    simp [Fintype.sum_sum_type]
    have h1 : - ∂ₜ (fun t => A.electricField t x.space) x.time i =
       ∂_ (Sum.inl 0) (fun x => (A.fieldStrengthMatrix x) (Sum.inl 0, Sum.inr i)) x := by
      rw [SpaceTime.deriv_sum_inl _
        (fieldStrengthMatrix_differentiable (hA.of_le (ENat.LEInfty.out)))]
      trans -∂ₜ (fun t => A.electricField t x.space i) x.time
      · rw [Time.deriv_eq, Time.deriv_eq]
        trans -(fderiv ℝ (EuclideanSpace.proj i ∘ fun t => A.electricField t x.space) x.time) 1;swap
        · rfl
        rw [fderiv_comp]
        simp
        · fun_prop
        · apply Differentiable.differentiableAt
          apply A.electricField_differentiable_time
          exact hA.of_le (ENat.LEInfty.out)
      · conv_lhs =>
          enter [1, 1, t]
          rw [electricField_eq_fieldStrengthMatrix A t x.space i (hA.differentiable (by simp))]
        simp [Time.deriv_eq]
        rfl
    have h2 : ∑ j, Space.deriv j (fun y => A.magneticFieldMatrix x.time y (j, i)) x.space  =
      ∑ a₂, ∂_ (Sum.inr a₂) (fun x => (A.fieldStrengthMatrix x) (Sum.inr a₂, Sum.inr i)) x := by
      congr
      funext j
      rw [SpaceTime.deriv_sum_inr _
        (fieldStrengthMatrix_differentiable (hA.of_le (ENat.LEInfty.out)))]
      simp [magneticFieldMatrix ]
      rfl
    rw [← h1, ← h2, hn]
    simp [LorentzCurrentDensity.currentDensity]

open Time

lemma time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJd : Differentiable ℝ J)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema A J)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix  · x (i, j))) t =
      ∑ k, ∂[k] (∂[k] (A.magneticFieldMatrix t · (i, j))) x +
      ∂[j] (J.currentDensity t · i) x - ∂[i] (J.currentDensity t · j) x := by
  calc _
    _ = ∂ₜ (fun t => Space.deriv i (fun x => A.electricField t x j) x -
      Space.deriv j (fun x => A.electricField t x i) x) t := by
      conv_lhs =>
        enter [1, t]
        rw [time_deriv_magneticFieldMatrix _ (hA.of_le (ENat.LEInfty.out))]
    _ = ∂ₜ (fun t => Space.deriv i (fun x => A.electricField t x j) x) t -
        ∂ₜ (fun t => Space.deriv j (fun x => A.electricField t x i) x) t := by
      rw [Time.deriv_eq, fderiv_fun_sub]
      simp [Time.deriv_eq]
      all_goals
      · apply ClassicalMechanics.space_deriv_differentiable_time
        apply electricField_apply_contDiff
        apply hA.of_le (right_eq_inf.mp rfl)
    _ = ∂[i] (fun x => ∂ₜ  (fun t => A.electricField t x j) t) x -
        ∂[j] (fun x => ∂ₜ (fun t => A.electricField t x i) t) x := by
      rw [ClassicalMechanics.time_deriv_comm_space_deriv,
        ClassicalMechanics.time_deriv_comm_space_deriv]
      all_goals
      · apply electricField_apply_contDiff
        apply hA.of_le (right_eq_inf.mp rfl)
    _ = ∂[i] (fun x => ∂ₜ  (fun t => A.electricField t x) t j) x -
        ∂[j] (fun x => ∂ₜ (fun t => A.electricField t x) t i) x := by
      congr
      all_goals
      · funext x
        rw [Time.deriv_euclid]
        apply electricField_differentiable_time
        apply hA.of_le (right_eq_inf.mp rfl)
    _ = ∂[i] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, j)) x -
          J.currentDensity t x j) x -
        ∂[j] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, i)) x -
          J.currentDensity t x i) x := by
      rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
      congr
      all_goals
      · funext x
        rw [(h _ _).2]
    _ = ∂[i] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, j)) x) x -
        ∂[i] (fun x => J.currentDensity t x j) x -
        ∂[j] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, i)) x) x +
        ∂[j] (fun x => J.currentDensity t x i) x := by
      rw [Space.deriv_eq_fderiv_basis]
      rw [fderiv_fun_sub]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_eq_fderiv_basis,
          fderiv_fun_sub (by
          apply Differentiable.fun_sum
          intro i _
          apply Space.deriv_differentiable
          apply magneticFieldMatrix_space_contDiff
          apply hA.of_le
          exact right_eq_inf.mp rfl)
          (by
          apply Differentiable.differentiableAt
          apply LorentzCurrentDensity.currentDensity_apply_differentiable_space
          exact hJd)]
      simp [Space.deriv_eq_fderiv_basis]
      ring
      · apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff
        apply hA.of_le
        exact right_eq_inf.mp rfl
      · apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_space
        exact hJd
    _ = ∂[i] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, j)) x) x -
        ∂[j] (fun x => ∑ k, ∂[k] (A.magneticFieldMatrix t · (k, i)) x) x +
        ∂[j] (fun x => J.currentDensity t x i) x
        - ∂[i] (fun x => J.currentDensity t x j) x  := by ring
    _ = ∑ k, (∂[i] (fun x => ∂[k] (A.magneticFieldMatrix t · (k, j)) x) x -
        ∂[j] (fun x => ∂[k] (A.magneticFieldMatrix t · (k, i)) x) x) +
        ∂[j] (fun x => J.currentDensity t x i) x
        - ∂[i] (fun x => J.currentDensity t x j) x  := by
      rw [Finset.sum_sub_distrib]
      congr
      all_goals
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sum]
        simp
        congr
        funext k
        rw [Space.deriv_eq_fderiv_basis]
        intro i _
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff
        apply hA.of_le
        exact right_eq_inf.mp rfl
     _ = ∑ k, ∂[k] (∂[k] (A.magneticFieldMatrix t · (i, j))) x +
        ∂[j] (fun x => J.currentDensity t x i) x
        - ∂[i] (fun x => J.currentDensity t x j) x := by
      congr
      funext k
      rw [Space.deriv_commute _ (by
        apply magneticFieldMatrix_space_contDiff
        apply hA.of_le
        exact right_eq_inf.mp rfl), Space.deriv_eq_fderiv_basis]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_commute _ (by
          apply magneticFieldMatrix_space_contDiff
          apply hA.of_le
          exact right_eq_inf.mp rfl), Space.deriv_eq_fderiv_basis]
      trans fderiv ℝ (Space.deriv i (fun x => A.magneticFieldMatrix t x (k, j))
        - Space.deriv j fun x => A.magneticFieldMatrix t x (k, i)) x (Space.basis k)
      · rw [fderiv_sub]
        simp
        all_goals
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff
        apply hA.of_le
        exact right_eq_inf.mp rfl
      rw [← Space.deriv_eq_fderiv_basis]
      congr
      funext x
      conv_rhs =>
        rw [magneticFieldMatrix_space_deriv_eq _ (hA.of_le (ENat.LEInfty.out))]
      simp

lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJd : Differentiable ℝ J)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema A J)
    (t : Time) (x : Space d) (i : Fin d):
    ∂ₜ (∂ₜ (A.electricField  · x i)) t = ∑ j, (∂[j] (∂[j] (A.electricField t · i)) x) -
        ∂[i] (J.chargeDensity t ·) x - ∂ₜ (J.currentDensity · x i) t := by
  calc _
    _ = ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticFieldMatrix t · (j, i)) x -
      J.currentDensity t x i) t := by
      rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
      congr
      funext t
      rw [Time.deriv_euclid]
      rw [(h _ _).2]
      apply electricField_differentiable_time
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticFieldMatrix t · (j, i)) x) t -
      ∂ₜ (J.currentDensity · x i) t := by
      rw [Time.deriv_eq]
      rw [fderiv_fun_sub]
      simp [Time.deriv_eq]
      · apply Differentiable.fun_sum
        intro j _
        apply ClassicalMechanics.space_deriv_differentiable_time
        apply magneticFieldMatrix_contDiff
        apply hA.of_le (right_eq_inf.mp rfl)
      · apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_time
        exact hJd
    _ = (∑ j, ∂ₜ (fun t => ∂[j] (A.magneticFieldMatrix t · (j, i)) x)) t -
        ∂ₜ (J.currentDensity · x i) t := by
      congr
      rw [Time.deriv_eq]
      rw [fderiv_fun_sum]
      simp
      rfl
      intro i _
      apply Differentiable.differentiableAt
      apply ClassicalMechanics.space_deriv_differentiable_time
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = (∑ j, ∂[j] (fun x => ∂ₜ (A.magneticFieldMatrix · x (j, i)) t)) x -
        ∂ₜ (J.currentDensity · x i) t := by
      congr
      simp
      congr
      funext k
      rw [ClassicalMechanics.time_deriv_comm_space_deriv]
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = (∑ j, ∂[j] (fun x => ∂[j] (A.electricField t · i) x - ∂[i] (A.electricField t · j) x)) x -
          ∂ₜ (J.currentDensity · x i) t := by
        congr
        simp
        congr
        funext k
        congr
        funext x
        rw [time_deriv_magneticFieldMatrix _ (hA.of_le (ENat.LEInfty.out))]
    _ = (∑ j, (∂[j] (fun x => ∂[j] (A.electricField t · i) x) x -
          ∂[j] (fun x => ∂[i] (A.electricField t · j) x) x))  -
          ∂ₜ (J.currentDensity · x i) t := by
        congr
        simp only [Finset.sum_apply]
        congr
        funext j
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sub]
        simp [← Space.deriv_eq_fderiv_basis]
        all_goals
        · apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          apply electricField_apply_contDiff_space
          apply hA.of_le
          exact right_eq_inf.mp rfl
    _ = ∑ j, (∂[j] (fun x => ∂[j] (A.electricField t · i) x) x) -
          ∑ j, (∂[j] (fun x => ∂[i] (A.electricField t · j) x) x)  -
          ∂ₜ (J.currentDensity · x i) t := by simp
    _ = ∑ j, (∂[j] (fun x => ∂[j] (A.electricField t · i) x) x) -
          ∑ j, (∂[i] (fun x => ∂[j] (A.electricField t · j) x) x)  -
          ∂ₜ (J.currentDensity · x i) t := by
        congr
        funext j
        rw [Space.deriv_commute _ (by
          apply electricField_apply_contDiff_space
          apply hA.of_le
          exact right_eq_inf.mp rfl), Space.deriv_eq_fderiv_basis]
      _ = ∑ j, (∂[j] (fun x => ∂[j] (A.electricField t · i) x) x) -
          (∂[i] (fun x => ∑ j, ∂[j] (A.electricField t · j) x) x)  -
          ∂ₜ (J.currentDensity · x i) t := by
        congr
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sum]
        simp [← Space.deriv_eq_fderiv_basis]
        intro i _
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply electricField_apply_contDiff_space
        apply hA.of_le
        exact right_eq_inf.mp rfl
      _ = ∑ j, (∂[j] (fun x => ∂[j] (A.electricField t · i) x) x) -
          (∂[i] (fun x => (∇ ⬝ (A.electricField t)) x) x)  -
          ∂ₜ (J.currentDensity · x i) t := by
        congr
        funext x
        simp [Space.div, Space.coord_apply]
      _ = ∑ j, (∂[j] (∂[j] (A.electricField t · i)) x) -
          ∂[i] (J.chargeDensity t ·) x - ∂ₜ (J.currentDensity · x i) t := by
        congr
        funext x
        rw [gaussLaw_electricField_of_isExtrema hA J hJ h t x]


end ElectromagneticPotential

end Electromagnetism
