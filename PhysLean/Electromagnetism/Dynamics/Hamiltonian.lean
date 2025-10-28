/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.Lagrangian
/-!

# The Hamiltonian in electromagnetism

## i. Overview

In this module we define the canonical momentum and the Hamiltonian for the
electromagnetic field in presence of a current density. We prove properties of these
quantities, and express the Hamiltonian in terms of the electric and magnetic fields
in the case of three spatial dimensions.

## ii. Key results

- `canonicalMomentum` : The canonical momentum for the electromagnetic field in presence of a
  Lorentz current density.
- `hamiltonian` : The Hamiltonian for the electromagnetic field in presence of a
  Lorentz current density.
- `hamiltonian_eq_electricField_magneticField` : The Hamiltonian expressed
  in terms of the electric and magnetic fields.

## iii. Table of contents

- A. The canonical momentum
  - A.1. The canonical momentum in terms of the kinetic term
  - A.2. The canonical momentum in terms of the field strength tensor
- B. The Hamiltonian
  - B.1. The hamiltonian in terms of the electric and magnetic fields

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

## A. The canonical momentum

We define the canonical momentum for the lagrangian
`L(A, ∂ A)` as gradient of `v ↦ L(A + t v, ∂ (A + t v)) - t * L(A + v, ∂(A + v))` at `v = 0`
This is equivalent to `∂ L/∂ (∂_0 A)`.

-/

/-- The canonical momentum associated with the lagrangian of an electromagnetic potential
  and a Lorentz current density. -/
noncomputable def canonicalMomentum (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    SpaceTime d → Lorentz.Vector d := fun x =>
  gradient (fun (v : Lorentz.Vector d) =>
    lagrangian (fun x => A x + x (Sum.inl 0) • v) J x) 0
  - x (Sum.inl 0) • gradient (fun (v : Lorentz.Vector d) =>
    lagrangian (fun x => A x + v) J x) 0

/-!

### A.1. The canonical momentum in terms of the kinetic term

-/
lemma canonicalMomentum_eq_gradient_kineticTerm {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum J = fun x =>
    gradient (fun (v : Lorentz.Vector d) =>
    kineticTerm (fun x => A x + x (Sum.inl 0) • v) x) 0:= by
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  rw [gradient, canonicalMomentum]
  simp only [Fin.isValue, toDual_symm_apply]
  rw [inner_sub_left, inner_smul_left]
  simp [gradient]
  conv_lhs =>
    enter [2]
    simp [lagrangian_add_const]
  have hx : DifferentiableAt ℝ (fun v => kineticTerm (fun x => A x + x (Sum.inl 0) • v) x) 0 := by
    apply Differentiable.differentiableAt _
    conv =>
      enter [2, v]
      rw [kineticTerm_add_time_mul_const _ (hA.differentiable (by simp))]
    fun_prop

  conv_lhs =>
    enter [1]
    simp only [lagrangian, Fin.isValue, map_add, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_fun_sub hx (by fun_prop)]
    simp only [Fin.isValue, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul, fderiv_const_add, ContinuousLinearMap.coe_sub', Pi.sub_apply]
    rw [fderiv_const_mul (by fun_prop)]
  simp only [Fin.isValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp

/-!

### A.2. The canonical momentum in terms of the field strength tensor

-/

lemma canonicalMomentum_eq {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum J = fun x => fun μ => η μ μ • A.fieldStrengthMatrix x (μ, Sum.inl 0) := by
  rw [canonicalMomentum_eq_gradient_kineticTerm A hA J]
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  simp [gradient]
  conv_lhs =>
    enter [1, 2, v]
    rw [kineticTerm_add_time_mul_const _ (hA.differentiable (by simp))]
  simp only [Fin.isValue, Finset.sum_sub_distrib, one_div, fderiv_const_add]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  conv_lhs =>
    enter [1, 1, 2, 1, 2, i]
    rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_pow _ (by fun_prop)]
    simp
  conv_lhs =>
    enter [1, 1, 2, 2, 2, i]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    simp
  rw [fderiv_pow _ (by fun_prop)]
  simp [Lorentz.Vector.coordCLM]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr
  funext μ
  simp only [Fin.isValue, RCLike.inner_apply, conj_trivial]
  rw [fieldStrengthMatrix, toFieldStrength_basis_repr_apply_eq_single]
  simp only [Fin.isValue, inl_0_inl_0, one_mul]
  ring_nf
  simp

/-!

## B. The Hamiltonian

-/

/-- The Hamiltonian associated with an electromagnetic potential
  and a Lorentz current density. -/
noncomputable def hamiltonian (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) : ℝ :=
    ∑ μ, A.canonicalMomentum J x μ * ∂_ (Sum.inl 0) A x μ - lagrangian A J x

/-!

### B.1. The hamiltonian in terms of the electric and magnetic fields

This only holds in three spatial dimensions.

-/

lemma hamiltonian_eq_electricField_magneticField (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity 3) (x : SpaceTime) :
    A.hamiltonian J x = 1/2 * (‖A.electricField x.time x.space‖ ^ 2
      + ‖A.magneticField x.time x.space‖ ^ 2)
      + ∑ i, (A.electricField x.time x.space i * ∂_ (Sum.inr i) A x (Sum.inl 0)) +
      ⟪A x, J x⟫ₘ := by
  conv_lhs =>
    rw [hamiltonian, lagrangian, canonicalMomentum_eq A hA J]

    rw [kineticTerm_eq_electric_magnetic' (hA.differentiable (by simp))]
    simp [Fintype.sum_sum_type, Fin.sum_univ_three]
  repeat rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
  simp only [Fin.isValue, one_div, space_toCoord_symm]
  have h1 (i : Fin 3) : ∂_ (Sum.inl 0) A x (Sum.inr i) = -
    (A.fieldStrengthMatrix x (Sum.inr i, Sum.inl 0) + ∂_ (Sum.inr i) A x (Sum.inl 0)) := by
    rw [fieldStrengthMatrix, toFieldStrength_basis_repr_apply_eq_single]
    simp
  rw [h1, h1, h1]
  repeat rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
  simp only [Fin.isValue, neg_add_rev]
  calc _
    _ = ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i)^2
      + ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      ring
    _ = ‖A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2‖ ^ 2
      + ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by
      congr
      rw [PiLp.norm_sq_eq_of_L2]
      simp
    _ = ‖A.electricField x.time x.space‖ ^ 2
      + ∑ i, (A.electricField x.time x.space i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by rfl
    _ = 1/2 * (‖A.electricField x.time x.space‖ ^ 2 + ‖A.magneticField x.time x.space‖ ^ 2)
      + ∑ i, (A.electricField x.time x.space i * ∂_ (Sum.inr i) A x (Sum.inl 0)) +
      ⟪A x, J x⟫ₘ := by simp; ring
  simp only [one_div, space_toCoord_symm, Fin.isValue]
  repeat exact hA.differentiable (by simp)

end ElectromagneticPotential

end Electromagnetism
