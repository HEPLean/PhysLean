/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.Lagrangian
/-!

# Extrema of the Lagrangian density

## i. Overview

In this module we define what it means for an electromagnetic potential
to be an extremum of the Lagrangian density in presence of a Lorentz current density.

This is equivalent to the electromagnetic potential satisfying
Maxwell's equations with sources, i.e. Gauss's law and Ampère's law.

## ii. Key results

- `IsExtrema` : The condition on an electromagnetic potential to be an extrema of the lagrangian.
- `isExtrema_iff_gauss_ampere_magneticFieldMatrix` : The electromagnetic potential is an extrema
  of the lagrangian if and only if Gauss's law and Ampère's law hold
  (in terms of the magnetic field matrix).
- `time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema` : A wave-like equation for the
  magnetic field matrix from the extrema condition.
- `time_deriv_time_deriv_electricField_of_isExtrema` : A wave-like equation for the
  electric field from the extrema condition.

## iii. Table of contents

- A. The condition for an extrema of the Lagrangian density
  - A.1. Extrema condition in terms of the field strength matrix
- B. Gauss's law and Ampère's law and the extrema condition
- C. Time derivatives from the extrema condition
- D. Second time derivatives from the extrema condition
  - D.1. Second time derivatives of the magnetic field from the extrema condition
  - D.2. Second time derivatives of the electric field from the extrema condition

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
open Lorentz.Vector
open Time Space
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The condition for an extrema of the Lagrangian density

-/

/-- The condition on an electromagnetic potential to be an extrema of the lagrangian. -/
def IsExtrema {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : Prop :=
  gradLagrangian 𝓕 A J = 0

lemma isExtrema_iff_gradLagrangian {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ A.gradLagrangian 𝓕 J = 0 := by rfl

/-!

### A.1. Extrema condition in terms of the field strength matrix

-/

lemma isExtrema_iff_fieldStrengthMatrix {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔
    ∀ x, ∀ ν, ∑ μ, ∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x = 𝓕.μ₀ * J x ν := by
  rw [isExtrema_iff_gradLagrangian, gradLagrangian_eq_sum_fieldStrengthMatrix A hA J hJ, funext_iff]
  conv_lhs =>
    enter [x, 1, 2, ν]
    rw [smul_smul]
  conv_lhs =>
    enter [x]
    simp only [one_div, Pi.zero_apply]
    rw [Lorentz.Vector.sum_basis_eq_zero_iff]
  apply Iff.intro
  · intro h x ν
    specialize h x ν
    simp at h
    have h' : η ν ν ≠ 0 := η_diag_ne_zero
    simp_all
    linear_combination (norm := field_simp) 𝓕.μ₀ * h
    ring
  · intro h x ν
    specialize h x ν
    simp only [mul_eq_zero]
    right
    linear_combination (norm := field_simp) 𝓕.μ₀⁻¹ * h
    ring

/-!

## B. Gauss's law and Ampère's law and the extrema condition

-/

lemma isExtrema_iff_gauss_ampere_magneticFieldMatrix {d} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔ ∀ t, ∀ x, (∇ ⬝ (A.electricField 𝓕.c t)) x = J.chargeDensity 𝓕.c t x / 𝓕.ε₀
    ∧ ∀ i, 𝓕.μ₀ * 𝓕.ε₀ * ∂ₜ (fun t => A.electricField 𝓕.c t x) t i =
    ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x - 𝓕.μ₀ * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gradLagrangian]
  rw [funext_iff]
  conv_lhs =>
    enter [x]
    rw [gradLagrangian_eq_electricField_magneticField (𝓕 := 𝓕) A hA J hJ]
    simp only [Pi.zero_apply]
    rw [Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff]
  simp only [forall_and]
  apply and_congr
  · apply Iff.intro
    · intro h t x
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x))
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.c) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
    · intro h x
      specialize h (x.time 𝓕.c) x.space
      linear_combination (norm := simp) (𝓕.μ₀⁻¹ * 𝓕.c⁻¹) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
  · apply Iff.intro
    · intro h t x i
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x)) i
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀) * h
      field_simp
      simp
    · intro h x i
      specialize h (x.time 𝓕.c) x.space i
      linear_combination (norm := simp) (𝓕.μ₀⁻¹) * h
      field_simp
      simp

/-!

## C. Time derivatives from the extrema condition

-/

lemma time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J)
    (h : IsExtrema 𝓕 A J) (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (A.electricField 𝓕.c · x) t i =
      1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x -
      (1/ 𝓕.ε₀) * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
  specialize h t x
  have h1 := (h.2 i)
  linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.ε₀)⁻¹ * h1
  field_simp
  ring

/-!

## D. Second time derivatives from the extrema condition

-/

/-!

### D.1. Second time derivatives of the magnetic field from the extrema condition

-/

lemma time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJd : Differentiable ℝ J)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j))) t =
    𝓕.c ^ 2 * ∑ k, ∂[k] (∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j))) x +
    𝓕.ε₀⁻¹ * (∂[j] (J.currentDensity 𝓕.c t · i) x - ∂[i] (J.currentDensity 𝓕.c t · j) x) := by
  rw [time_deriv_time_deriv_magneticFieldMatrix A (hA.of_le (ENat.LEInfty.out))]
  conv_lhs =>
    enter [2, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  conv_lhs =>
    enter [1, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub (by
        apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
          ((LorentzCurrentDensity.currentDensity_apply_differentiable_space
          hJd _ _).const_mul _).differentiableAt,
    fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))),
    fderiv_const_mul (by
        apply (LorentzCurrentDensity.currentDensity_apply_differentiable_space
        hJd _ _).differentiableAt),
    fderiv_fun_sum fun i _ => by
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))]
  conv_lhs =>
    enter [2]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by
        apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
          ((LorentzCurrentDensity.currentDensity_apply_differentiable_space
          hJd _ _).const_mul _).differentiableAt,
    fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro i _
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))),
    fderiv_const_mul (by
        apply (LorentzCurrentDensity.currentDensity_apply_differentiable_space
        hJd _ _).differentiableAt),
    fderiv_fun_sum fun i _ => by
        apply Differentiable.differentiableAt
        apply Space.deriv_differentiable
        apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl))]
  simp [← Space.deriv_eq_fderiv_basis, FreeSpace.c_sq]
  field_simp
  conv_rhs =>
    enter [1, 2, k, 2, x]
    rw [magneticFieldMatrix_space_deriv_eq A (hA.of_le (right_eq_inf.mp rfl))]
  conv_rhs =>
    enter [1, 2, k]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (by
      apply Space.deriv_differentiable
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))
      (by
      apply Space.deriv_differentiable
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
    simp [← Space.deriv_eq_fderiv_basis]
    rw [Space.deriv_commute _ (by
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
    enter [2]
    rw [Space.deriv_commute _ (by
      apply magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)))]
  simp only [Finset.sum_sub_distrib]
  ring

/-!

### D.2. Second time derivatives of the electric field from the extrema condition

-/

lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (∂ₜ (A.electricField 𝓕.c · x i)) t =
      𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
      𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
      𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
  calc _
    _= ∂ₜ (fun t =>
      1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, Space.deriv j (fun x => magneticFieldMatrix 𝓕.c A t x (j, i)) x -
      1 / 𝓕.ε₀ * LorentzCurrentDensity.currentDensity 𝓕.c J t x i) t := by
        conv_lhs =>
          enter [1]
          change fun t => ∂ₜ (A.electricField 𝓕.c · x i) t
          enter [t]
          rw [Time.deriv_euclid (electricField_differentiable_time
            (hA.of_le (right_eq_inf.mp rfl)) _),
            time_deriv_electricField_of_isExtrema hA J hJ h]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x) t -
      1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
      rw [Time.deriv_eq]
      rw [fderiv_fun_sub]
      simp only [one_div, mul_inv_rev, ContinuousLinearMap.coe_sub', Pi.sub_apply]
      rw [fderiv_const_mul (by
        apply Differentiable.fun_sum
        intro j _
        apply ClassicalMechanics.space_deriv_differentiable_time
        apply magneticFieldMatrix_contDiff
        apply hA.of_le (right_eq_inf.mp rfl))]
      rw [fderiv_const_mul (by
        apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_time
        exact hJ.differentiable (by simp))]
      simp [Time.deriv_eq]
      · apply Differentiable.const_mul
        apply Differentiable.fun_sum
        intro j _
        apply ClassicalMechanics.space_deriv_differentiable_time
        apply magneticFieldMatrix_contDiff
        apply hA.of_le (right_eq_inf.mp rfl)
      · apply DifferentiableAt.const_mul
        apply Differentiable.differentiableAt
        apply LorentzCurrentDensity.currentDensity_apply_differentiable_time
        exact hJ.differentiable (by simp)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ((∑ j, ∂ₜ (fun t => ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x)) t) -
      1 / 𝓕.ε₀ * (∂ₜ (J.currentDensity 𝓕.c · x i) t) := by
      congr
      rw [Time.deriv_eq]
      rw [fderiv_fun_sum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
      rfl
      intro i _
      apply Differentiable.differentiableAt
      apply ClassicalMechanics.space_deriv_differentiable_time
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂[j] (fun x => ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (j, i)) t)) x -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
      congr
      simp only [Finset.sum_apply]
      congr
      funext k
      rw [ClassicalMechanics.time_deriv_comm_space_deriv]
      apply magneticFieldMatrix_contDiff
      apply hA.of_le (right_eq_inf.mp rfl)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) *(∑ j, ∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x -
        ∂[i] (A.electricField 𝓕.c t · j) x)) x -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        simp only [Finset.sum_apply]
        congr
        funext k
        congr
        funext x
        rw [time_deriv_magneticFieldMatrix _ (hA.of_le (ENat.LEInfty.out))]
    _ = (1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x -
          ∂[j] (fun x => ∂[i] (A.electricField 𝓕.c t · j) x) x)) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
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
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[i] (A.electricField 𝓕.c t · j) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by simp [mul_sub]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[i] (fun x => ∂[j] (A.electricField 𝓕.c t · j) x) x) -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        funext j
        rw [Space.deriv_commute _ (by
          apply electricField_apply_contDiff_space
          apply hA.of_le
          exact right_eq_inf.mp rfl), Space.deriv_eq_fderiv_basis]
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * (∂[i] (fun x => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
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
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀) * (∂[i] (fun x => (∇ ⬝ (A.electricField 𝓕.c t)) x) x) -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr
        funext x
        simp [Space.div, Space.coord_apply]
      _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
          1 / (𝓕.μ₀ * 𝓕.ε₀ ^ 2) * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
          1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        congr 2
        rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix] at h

        conv_lhs =>
          enter [2, 2, x]
          rw [(h t x).1]
        trans 1 / (𝓕.μ₀ * 𝓕.ε₀) * Space.deriv i
            (fun x => (1/ 𝓕.ε₀) * LorentzCurrentDensity.chargeDensity 𝓕.c J t x) x
        · congr
          funext x
          ring
        · rw [Space.deriv_eq_fderiv_basis]
          rw [fderiv_const_mul]
          simp [← Space.deriv_eq_fderiv_basis]
          field_simp
          apply Differentiable.differentiableAt
          apply LorentzCurrentDensity.chargeDensity_differentiable_space
          exact hJ.differentiable (by simp)
        · exact hA
        · exact hJ
      _ = 𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
            𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
            𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
          simp [FreeSpace.c_sq]
          field_simp

end ElectromagneticPotential

end Electromagnetism
