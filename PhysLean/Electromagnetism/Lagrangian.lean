/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.CurrentDensity
/-!

# The Lagrangian in electromagnetism

## i. Overview

In this module we defin the Lagrangian density for the electromagnetic field in
presence of a current density. We prover properties of this lagrangian density,
and find it's variational gradient.

## ii. Key results

- `lagrangian` : The lagrangian density for the electromagnetic field in presence of a
  Lorentz current density.
- `gradLagrangian` : The variational gradient of the lagrangian density.
- `gradLagrangian_eq_electricField_magneticField` : The variational gradient of the lagrangian
  density expressed in Guass's and Ampère laws.

## iii. Table of contents

- A. The Lagrangian density
  - A.1. Shifts in the lagrangian under shifts in the potential
- B. The variational gradient of the lagrangian density
  - B.1. The lagrangian density has a variational gradient
  - B.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density
  - B.3. The variational gradient in terms of the gradient of the kinetic term
  - B.4. The lagrangian density has the variational gradient equal to `gradLagrangian`
  - B.5. The variational gradient in terms of the field strength tensor
  - B.6. The lagrangian gradient recovering Guass's and Ampère laws

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

/-- The langrangian density associated with a electromagnetic potential and a Lorentz
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

/-- The varitional gradient of the lagrangian of electromagnetic field. -/
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
open Time

/-!

### B.6. The lagrangian gradient recovering Guass's and Ampère laws
-/

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

end ElectromagneticPotential

end Electromagnetism
