/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.CurrentDensity
import PhysLean.Electromagnetism.Dynamics.KineticTerm
/-!

# The Lagrangian in electromagnetism

## i. Overview

In this module we define the Lagrangian density for the electromagnetic field in
presence of a current density. We prove properties of this lagrangian density,
and find it's variational gradient.

The lagrangian density is given by
`L = -1/(4 μ₀) F_{μν} F^{μν} - A_μ J^μ`

In this implementation we set `μ₀ = 1`. It is a TODO to introduce this constant.

## ii. Key results

- `freeCurrentPotential` : The potential energy from the interaction of the electromagnetic
  potential with a free Lorentz current density.
- `gradFreeCurrentPotential` : The variational gradient of the free current potential.
- `lagrangian` : The lagrangian density for the electromagnetic field in presence of a
  Lorentz current density.
- `gradLagrangian` : The variational gradient of the lagrangian density.
- `gradLagrangian_eq_electricField_magneticField` : The variational gradient of the lagrangian
  density expressed in Gauss's and Ampère laws.

## iii. Table of contents

- A. Free current potential
  - A.1. Shifts in the free current potential under shifts in the potential
  - A.2. The free current potential has a variational gradient
  - A.3. The free current potential in terms of the scalar and vector potentials
  - A.4. The variational gradient of the free current potential
- B. The Lagrangian density
  - B.1. Shifts in the lagrangian under shifts in the potential
  - B.2. Lagrangian in terms of electric and magnetic fields
- C. The variational gradient of the lagrangian density
  - C.1. The lagrangian density has a variational gradient
  - C.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density
  - C.3. The variational gradient in terms of the gradient of the kinetic term
  - C.4. The lagrangian density has the variational gradient equal to `gradLagrangian`
  - C.5. The variational gradient in terms of the field strength tensor
  - C.6. The lagrangian gradient recovering Gauss's and Ampère laws

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html
- https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf

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

## A. Free current potential

-/

/-- The potential energy from the interaction of the electromagnetic potential
  with the free current `J`. -/
noncomputable def freeCurrentPotential (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d)
    (x : SpaceTime d) : ℝ := ⟪A x, J x⟫ₘ

/-!

### A.1. Shifts in the free current potential under shifts in the potential

-/

lemma freeCurrentPotential_add_const (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (c : Lorentz.Vector d) (x : SpaceTime d) :
    freeCurrentPotential (fun x => A x + c) J x = freeCurrentPotential A J x + ⟪c, J x⟫ₘ := by
  rw [freeCurrentPotential, freeCurrentPotential]
  simp

/-!

### A.2. The free current potential has a variational gradient

-/

lemma freeCurrentPotential_hasVarGradientAt (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    HasVarGradientAt (fun A => freeCurrentPotential A J)
    (((∑ μ, fun x => (η μ μ * J x μ) • Lorentz.Vector.basis μ))) A := by
  conv =>
    enter [1, q', x]
    rw [freeCurrentPotential, minkowskiProduct_toCoord_minkowskiMatrix]
  apply HasVarGradientAt.sum _ hA
  intro μ
  have h1 := hasVarAdjDerivAt_component μ A hA
  have h2' : ContDiff ℝ ∞ fun x => η μ μ * J x μ :=
    ContDiff.mul (by fun_prop) ((Lorentz.Vector.contDiff_apply _).mpr hJ μ)
  have h2 := HasVarAdjDerivAt.fun_mul h2' _ _ A h1
  have h3' : (fun (φ : SpaceTime d → Lorentz.Vector d) x => η μ μ * J x μ * φ x μ) =
    (fun (φ : SpaceTime d → Lorentz.Vector d) x => η μ μ * φ x μ * J x μ) := by
    funext φ x
    ring
  rw [h3'] at h2
  apply HasVarGradientAt.intro _ h2
  simp

/-!

### A.3. The free current potential in terms of the scalar and vector potentials

-/

lemma freeCurrentPotential_eq_sum_scalarPotential_vectorPotential
    (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) :
    A.freeCurrentPotential J x =
    A.scalarPotential 𝓕.c (x.time 𝓕.c) x.space * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space
    - ∑ i, A.vectorPotential 𝓕.c (x.time 𝓕.c) x.space i *
        J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i := by
  rw [freeCurrentPotential, minkowskiProduct_toCoord_minkowskiMatrix]
  simp [Fintype.sum_sum_type, scalarPotential, vectorPotential, LorentzCurrentDensity.chargeDensity,
    LorentzCurrentDensity.currentDensity, timeSlice]
  field_simp
  ring

/-!

### A.4. The variational gradient of the free current potential

-/

/-- The variational gradient of the free current potential. -/
noncomputable def gradFreeCurrentPotential {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, freeCurrentPotential q' J x)

lemma gradFreeCurrentPotential_eq_sum_basis {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    A.gradFreeCurrentPotential J = (∑ μ, fun x => (η μ μ * J x μ) • Lorentz.Vector.basis μ) := by
  apply HasVarGradientAt.varGradient
  apply freeCurrentPotential_hasVarGradientAt A hA J hJ

lemma gradFreeCurrentPotential_eq_chargeDensity_currentDensity {d}
    (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (x : SpaceTime d) :
    A.gradFreeCurrentPotential J x =
      (𝓕.c * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space) • Lorentz.Vector.basis (Sum.inl 0) +
      (∑ i, - J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i • Lorentz.Vector.basis (Sum.inr i)) := by
  rw [gradFreeCurrentPotential_eq_sum_basis A hA J hJ]
  rw [Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, _root_.neg_smul, Pi.add_apply, Finset.sum_apply,
    Finset.sum_neg_distrib]
  congr
  · simp [LorentzCurrentDensity.chargeDensity]
  · simp [LorentzCurrentDensity.currentDensity]

/-!

## B. The Lagrangian density

The lagrangian density for the electromagnetic field in presence of a current density `J` is
`L = -1/(4 μ₀) F_{μν} F^{μν} - A_μ J^μ`

-/

/-- The lagrangian density associated with a electromagnetic potential and a Lorentz
  current density. -/
noncomputable def lagrangian (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) : ℝ :=
  A.kineticTerm 𝓕 x - A.freeCurrentPotential J x

/-!

### B.1. Shifts in the lagrangian under shifts in the potential

-/

lemma lagrangian_add_const {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (c : Lorentz.Vector d) (x : SpaceTime d) :
    lagrangian 𝓕 (fun x => A x + c) J x = lagrangian 𝓕 A J x - ⟪c, J x⟫ₘ := by
  rw [lagrangian, lagrangian, kineticTerm_add_const, freeCurrentPotential_add_const]
  ring

/-!

### B.2. Lagrangian in terms of electric and magnetic fields

-/

/-- The Lagrangian is equal to `1/2 * (ε₀ E^2 - 1/μ₀ B^2) - φρ + A · j`-/
lemma lagrangian_eq_electric_magnetic {d} {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ 2 A)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) :
    A.lagrangian 𝓕 J x = 1 / 2 * (𝓕.ε₀ * ‖A.electricField 𝓕.c (x.time 𝓕.c) x.space‖ ^ 2 -
    (1 / (2 * 𝓕.μ₀)) * ∑ i, ∑ j, ‖A.magneticFieldMatrix 𝓕.c (x.time 𝓕.c) x.space (i, j)‖ ^ 2)
    - A.scalarPotential 𝓕.c (x.time 𝓕.c) x.space * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space
    + ∑ i, A.vectorPotential 𝓕.c (x.time 𝓕.c) x.space i *
        J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i := by
  rw [lagrangian]
  rw[kineticTerm_eq_electricMatrix_magneticFieldMatrix _ _ (hA.differentiable (by simp))]
  rw [freeCurrentPotential_eq_sum_scalarPotential_vectorPotential 𝓕 A J x]
  ring

/-!

## C. The variational gradient of the lagrangian density
-/

/-!

### C.1. The lagrangian density has a variational gradient

-/

lemma lagrangian_hasVarGradientAt_eq_add_gradKineticTerm {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    HasVarGradientAt (fun A => lagrangian 𝓕 A J)
    (A.gradKineticTerm 𝓕 - A.gradFreeCurrentPotential J) A := by
  conv =>
    enter [1, q', x]
    rw [lagrangian]
  apply HasVarGradientAt.add
  · exact A.kineticTerm_hasVarGradientAt hA
  apply HasVarGradientAt.neg
  convert freeCurrentPotential_hasVarGradientAt A hA J hJ
  rw [← gradFreeCurrentPotential_eq_sum_basis A hA J hJ]

/-!

### C.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density

-/

/-- The variational gradient of the lagrangian of electromagnetic field. -/
noncomputable def gradLagrangian {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, lagrangian 𝓕 q' J x)

/-!

### C.3. The variational gradient in terms of the gradient of the kinetic term

-/

lemma gradLagrangian_eq_kineticTerm_sub {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian 𝓕 J = A.gradKineticTerm 𝓕 - A.gradFreeCurrentPotential J := by
  apply HasVarGradientAt.varGradient
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ

/-!

### C.4. The lagrangian density has the variational gradient equal to `gradLagrangian`

-/
lemma lagrangian_hasVarGradientAt_gradLagrangian {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    HasVarGradientAt (fun A => lagrangian 𝓕 A J) (A.gradLagrangian 𝓕 J) A := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ

/-!

### C.5. The variational gradient in terms of the field strength tensor

-/

lemma gradLagrangian_eq_sum_fieldStrengthMatrix {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian 𝓕 J = fun x => ∑ ν,
      (η ν ν • (1 / 𝓕.μ₀ * ∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)
      • Lorentz.Vector.basis ν) := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  funext x
  simp only [Pi.sub_apply]
  rw [gradKineticTerm_eq_fieldStrength, gradFreeCurrentPotential_eq_sum_basis A hA J hJ]
  simp only [one_div, Finset.sum_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [smul_smul, smul_smul, ← sub_smul]
  ring_nf
  exact hA

/-!

### C.6. The lagrangian gradient recovering Gauss's and Ampère laws

-/

open Time LorentzCurrentDensity
lemma gradLagrangian_eq_electricField_magneticField {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (x : SpaceTime d) :
    A.gradLagrangian 𝓕 J x = (1 / (𝓕.μ₀ * 𝓕.c.val) *
        Space.div (electricField 𝓕.c A ((time 𝓕.c) x)) (space x) +
        - 𝓕.c * J.chargeDensity 𝓕.c (x.time 𝓕.c) x.space) •
      Lorentz.Vector.basis (Sum.inl 0) +
    ∑ i, (𝓕.μ₀⁻¹ * (𝓕.ε₀ * 𝓕.μ₀ * ∂ₜ (electricField 𝓕.c A · x.space) ((time 𝓕.c) x) i -
      ∑ j, ∂[j] (magneticFieldMatrix 𝓕.c A (x.time 𝓕.c) · (j, i)) x.space) +
      J.currentDensity 𝓕.c (x.time 𝓕.c) x.space i) •
        Lorentz.Vector.basis (Sum.inr i) := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  simp only [Pi.sub_apply, one_div, mul_inv_rev, neg_mul, Fin.isValue]
  rw [gradKineticTerm_eq_electric_magnetic _ _ hA]
  rw [gradFreeCurrentPotential_eq_chargeDensity_currentDensity 𝓕 A hA J hJ x]
  conv_lhs =>
    enter [2]
    rw [add_comm]
  rw [add_sub_assoc]
  conv_lhs =>
    enter [2]
    rw [sub_add_eq_sub_sub]
    rw [← Finset.sum_sub_distrib]
    rw [← neg_add_eq_sub]
  rw [← add_assoc]
  conv_lhs =>
    enter [1, 2]
    rw [← _root_.neg_smul]
  rw [← add_smul]
  conv_lhs =>
    enter [2, 2, i]
    rw [← sub_smul]
    simp [FreeSpace.c_sq]
  ring_nf

end ElectromagneticPotential

end Electromagnetism
