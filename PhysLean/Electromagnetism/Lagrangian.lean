/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.CurrentDensity
import PhysLean.Electromagnetism.FaradayLaw
/-!

# The Lagrangian in electromagnetism

## i. Overview

In this module we define the Lagrangian density for the electromagnetic field in
presence of a current density. We prover properties of this lagrangian density,
and find it's variational gradient.

## ii. Key results

- `lagrangian` : The lagrangian density for the electromagnetic field in presence of a
  Lorentz current density.
- `gradLagrangian` : The variational gradient of the lagrangian density.
- `gradLagrangian_eq_electricField_magneticField` : The variational gradient of the lagrangian
  density expressed in Gauss's and Ampère laws.

## iii. Table of contents

- A. The Lagrangian density
  - A.1. Shifts in the lagrangian under shifts in the potential
- B. The variational gradient of the lagrangian density
  - B.1. The lagrangian density has a variational gradient
  - B.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density
  - B.3. The variational gradient in terms of the gradient of the kinetic term
  - B.4. The lagrangian density has the variational gradient equal to `gradLagrangian`
  - B.5. The variational gradient in terms of the field strength tensor
  - B.6. The lagrangian gradient recovering Gauss's and Ampère laws

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html

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
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A. The Lagrangian density

The lagrangian density for the electromagnetic field in presence of a current density `J` is
`L = 1/4 F_{μν} F^{μν} - A_μ J^μ`

-/

/-- The lagrangian density associated with a electromagnetic potential and a Lorentz
  current density. -/
noncomputable def lagrangian (A : ElectromagneticPotential d) (J : LorentzCurrentDensity d)
    (x : SpaceTime d) : ℝ :=
    A.kineticTerm x - ⟪A x, J x⟫ₘ

/-!

### A.1. Shifts in the lagrangian under shifts in the potential

-/

lemma lagrangian_add_const {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (c : Lorentz.Vector d) (x : SpaceTime d) :
    lagrangian (fun x => A x + c) J x = lagrangian A J x - ⟪c, J x⟫ₘ := by
  rw [lagrangian, lagrangian, kineticTerm_add_const]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

/-!

## B. The variational gradient of the lagrangian density
-/

/-!

### B.1. The lagrangian density has a variational gradient

-/

lemma lagrangian_hasVarGradientAt_eq_add_gradKineticTerm (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    HasVarGradientAt (fun A => lagrangian A J)
    (A.gradKineticTerm - ((∑ μ, fun x => (η μ μ * J x μ) • Lorentz.Vector.basis μ))) A := by
  conv =>
    enter [1, q', x]
    rw [lagrangian]
  apply HasVarGradientAt.add
  · exact A.kineticTerm_hasVarGradientAt hA
  apply HasVarGradientAt.neg
  conv =>
    enter [1, q', x]
    rw [minkowskiProduct_toCoord_minkowskiMatrix]
  apply HasVarGradientAt.sum _ hA
  intro μ
  have h1 := hasVarAdjDerivAt_component μ A hA
  have h2' : ContDiff ℝ ∞ fun x => η μ μ * J x μ :=
    ContDiff.mul (by fun_prop) (contDiff_euclidean.mp hJ μ)
  have h2 := HasVarAdjDerivAt.fun_mul h2' _ _ A h1
  have h3' : (fun (φ : SpaceTime d → Lorentz.Vector d) x => η μ μ * J x μ * φ x μ) =
    (fun (φ : SpaceTime d → Lorentz.Vector d) x => η μ μ * φ x μ * J x μ) := by
    funext φ x
    ring
  rw [h3'] at h2
  apply HasVarGradientAt.intro _ h2
  simp

/-!

### B.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density

-/

/-- The variational gradient of the lagrangian of electromagnetic field. -/
noncomputable def gradLagrangian {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, lagrangian q' J x)

/-!

### B.3. The variational gradient in terms of the gradient of the kinetic term

-/

lemma gradLagrangian_eq_kineticTerm_sub (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian J = A.gradKineticTerm -
      ((∑ μ, fun x => (η μ μ * J x μ) • Lorentz.Vector.basis μ)) := by
  apply HasVarGradientAt.varGradient
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ

/-!

### B.4. The lagrangian density has the variational gradient equal to `gradLagrangian`

-/
lemma lagrangian_hasVarGradientAt_gradLagrangian (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    HasVarGradientAt (fun A => lagrangian A J) (A.gradLagrangian J) A := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ

/-!

### B.5. The variational gradient in terms of the field strength tensor

-/

lemma gradLagrangian_eq_sum_fieldStrengthMatrix (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian J = fun x => ∑ ν,
      (η ν ν • (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)
      • Lorentz.Vector.basis ν) := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  funext x
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [gradKineticTerm_eq_fieldStrength]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [smul_smul, ← sub_smul, ← mul_sub, ← smul_smul]
  exact hA

/-!

### B.6. The lagrangian gradient recovering Gauss's and Ampère laws

-/

open Time
lemma gradLagrangian_eq_electricField_magneticField (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity 3)
    (hJ : ContDiff ℝ ∞ J) (x : SpaceTime) :
    A.gradLagrangian J x = ((∇ ⬝ A.electricField x.time) x.space - J.chargeDensity x.time x.space) •
        Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time - (∇ × (A.magneticField x.time)) x.space
          + J.currentDensity x.time x.space) i • Lorentz.Vector.basis (Sum.inr i)) := by
  calc A.gradLagrangian J x
    _ = A.gradKineticTerm x - ((∑ μ, (η μ μ * J x μ) • Lorentz.Vector.basis μ)) := by
      rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
      simp
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0) +
        ∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i) -
        ((∑ μ, (η μ μ * J x μ) • Lorentz.Vector.basis μ)) := by
      rw [gradKineticTerm_eq_electric_magnetic _ _ hA]
      rfl
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0) +
        ∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i) -
        ((J x (Sum.inl 0) • Lorentz.Vector.basis (Sum.inl 0))
        - (∑ i, J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
      rw [Fintype.sum_sum_type]
      simp
      rfl
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0)
        - (J x (Sum.inl 0) • Lorentz.Vector.basis (Sum.inl 0)) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i)
        + (∑ i, J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
        module
    _ = ((∇ ⬝ (A.electricField x.time)) x.space - J x (Sum.inl 0)) •
        Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i)
        + (∑ i, J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
        module
    _ = ((∇ ⬝ (A.electricField x.time)) x.space - J.chargeDensity x.time x.space) •
        Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i
          + J x (Sum.inr i)) • Lorentz.Vector.basis (Sum.inr i)) := by
        conv_rhs =>
          enter [2, 2, i]
          rw [add_smul]
        rw [Finset.sum_add_distrib]
        congr
        simp
    _ = ((∇ ⬝ A.electricField x.time) x.space - J.chargeDensity x.time x.space) •
        Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time - (∇ × (A.magneticField x.time)) x.space
          + J.currentDensity x.time x.space) i • Lorentz.Vector.basis (Sum.inr i)) := by
      congr
      funext i
      simp [LorentzCurrentDensity.currentDensity]


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
    (t : Time) (x : Space d) (i  j: Fin d):
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
      rw [Time.deriv_eq]
      rw [fderiv_fun_sub]
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
    (t : Time) (x : Space d) (i  j: Fin d):
    ∂ₜ (∂ₜ (A.electricField  · x i)) t = 0 := by
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


end ElectromagneticPotential

end Electromagnetism
