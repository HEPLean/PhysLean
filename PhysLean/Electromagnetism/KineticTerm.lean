/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Potential
/-!

# The kinetic term

## i. Overview

The kinetic term of the electromagnetic field is `- 1/4 F_μν F^μν`.
We define this, show it is invariant under Lorentz transformations,
and show properties of its variational gradient.

In particular the variational gradient `gradKineticTerm` of the kinetic term
is directly related to Gauss's law and the Ampere law.

## ii. Key results

- `ElectromagneticPotential.kineticTerm` is the kinetic term of an electromagnetic potential.
- `ElectromagneticPotential.kineticTerm_equivariant` shows that the kinetic term is
  Lorentz invariant.
- `ElectromagneticPotential.gradKineticTerm` is the variational gradient of the kinetic term.
- `ElectromagneticPotential.gradKineticTerm_eq_electric_magnetic` gives a first expression for the
  variational gradient in terms of the electric and magnetic fields.

## iii. Table of contents

- A. The kinetic term
  - A.1. Lorentz invariance of the kinetic term
  - A.2. Kinetic term simplified expressions
  - A.3. The kinetic term in terms of the electric and magnetic fields
- B. Variational gradient of the kinetic term
  - B.1. Variational gradient in terms of fderiv
  - B.2. Writing the variational gradient as a sums over double derivatives of the potential
  - B.3. Variational gradient as a sums over fieldStrengthMatrix
  - B.4. Variational gradient in terms of the Guass's and Ampère laws

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
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The kinetic term

The kinetic term is `- 1/4 F_μν F^μν`. We define this and show that it is
Lorentz invariant.

-/

/-- The kinetic energy from an electromagnetic potential. -/
noncomputable def kineticTerm (A : ElectromagneticPotential) : SpaceTime → ℝ := fun x =>
  - 1/4 * {η' 3 | μ μ' ⊗ η' 3 | ν ν' ⊗
    A.toFieldStrength x | μ ν ⊗ A.toFieldStrength x | μ' ν'}ᵀ.toField

/-!

### A.1. Lorentz invariance of the kinetic term

We show that the kinetic energy is Lorentz invariant.

-/

lemma kineticTerm_equivariant (A : ElectromagneticPotential) (Λ : LorentzGroup 3)
    (hf : Differentiable ℝ A) (x : SpaceTime) :
    kineticTerm (fun x => Λ • A (Λ⁻¹ • x)) x = kineticTerm A (Λ⁻¹ • x) := by
  rw [kineticTerm, kineticTerm]
  conv_lhs =>
    enter [2]
    rw [toFieldStrength_equivariant A Λ hf, Tensorial.toTensor_smul]
    rw [← actionT_coMetric Λ, Tensorial.toTensor_smul]
    simp only [prodT_equivariant, contrT_equivariant, toField_equivariant]

/-!

### A.2. Kinetic term simplified expressions

-/

lemma kineticTerm_eq_sum (A : ElectromagneticPotential) (x : SpaceTime) :
    A.kineticTerm x =
    - 1/4 * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) (μ, ν)
      * (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr
        (A.toFieldStrength x) (μ', ν') := by
  rw [kineticTerm]
  rw [toField_eq_repr]
  rw [contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, μ]
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, ν]
    rw [prodT_basis_repr_apply]
    enter [1]
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, μ']
    rw [contrT_basis_repr_apply_eq_fin]
    enter [2, ν']
    rw [prodT_basis_repr_apply]
    enter [1]
    rw [prodT_basis_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η (finSumFinEquiv.symm μ') (finSumFinEquiv.symm μ)
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 1, 2]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
    change η (finSumFinEquiv.symm ν') (finSumFinEquiv.symm ν)
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 1, 2, μ', 2, ν', 2]
    rw [toFieldStrength_tensor_basis_eq_basis]
    change ((Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x))
      (finSumFinEquiv.symm μ', finSumFinEquiv.symm ν')
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2]
    rw [toFieldStrength_tensor_basis_eq_basis]
    change ((Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x))
      (finSumFinEquiv.symm μ, finSumFinEquiv.symm ν)
  rw [← finSumFinEquiv.sum_comp]
  conv_lhs =>
    enter [2, 2, μ]
    rw [← finSumFinEquiv.sum_comp]
    enter [2, ν]
    rw [← finSumFinEquiv.sum_comp]
    rw [Finset.sum_mul]
    enter [2, μ']
    rw [← finSumFinEquiv.sum_comp]
    rw [Finset.sum_mul]
    enter [2, ν']
    simp
  conv_lhs => enter [2, 2, μ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, 2, μ']; rw [Finset.sum_comm]
  rfl

lemma kineticTerm_eq_sum_potential (A : ElectromagneticPotential) (x : SpaceTime) :
    A.kineticTerm x = - 1 / 2 * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
  calc _
    _ = - 1/4 * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η μ μ' * η ν ν' *
      (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
      * (η μ' μ' * ∂_ μ' A x ν' - η ν' ν' * ∂_ ν' A x μ') := by
      rw [kineticTerm_eq_sum]
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      apply Finset.sum_congr rfl (fun ν' _ => ?_)
      rw [toFieldStrength_basis_repr_apply_eq_single, toFieldStrength_basis_repr_apply_eq_single]
    _ = - 1/4 * ∑ μ, ∑ ν, ∑ μ', η μ μ' * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ' μ' * ∂_ μ' A x ν - η ν ν * ∂_ ν A x μ') := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      rw [Finset.sum_eq_single ν]
      · intro b _ hb
        nth_rewrite 2 [minkowskiMatrix.off_diag_zero]
        simp only [mul_zero, zero_mul]
        exact id (Ne.symm hb)
      · simp
    _ = - 1/4 * ∑ μ, ∑ ν, η μ μ * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Finset.sum_eq_single μ]
      · intro b _ hb
        rw [minkowskiMatrix.off_diag_zero]
        simp only [zero_mul]
        exact id (Ne.symm hb)
      · simp
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ) ^ 2 * η ν ν * ∂_ μ A x ν - (η ν ν) ^ 2 * η μ μ * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/4 * ∑ μ, ∑ ν,
        (η ν ν * ∂_ μ A x ν - η μ μ * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by simp
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - (η ν ν) ^ 2 * ∂_ μ A x ν * ∂_ ν A x μ) + (-
        (η μ μ) ^ 2 * ∂_ ν A x μ * ∂_ μ A x ν + η μ μ * η ν ν * (∂_ ν A x μ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        (- ∂_ ν A x μ * ∂_ μ A x ν + η μ μ * η ν ν * (∂_ ν A x μ)^2)) := by simp
    _ = - 1 / 4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
        (- ∂_ μ A x ν * ∂_ ν A x μ + η ν ν * η μ μ * (∂_ μ A x ν)^2)) := by
      congr 1
      conv_lhs =>
        enter [2, μ];
        rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      conv_lhs => enter [2]; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      conv_lhs =>
        enter [2, μ];
        rw [← Finset.sum_add_distrib]
    _ = - 1 / 4 * ∑ μ, ∑ ν,
        (2 * (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1 / 2 * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) := by
      conv_lhs =>
        enter [2, 2, μ]
        rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      ring

/-!

### A.3. The kinetic term in terms of the electric and magnetic fields

-/
open InnerProductSpace

lemma kineticTerm_eq_electric_magnetic (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.kineticTerm (SpaceTime.toTimeAndSpace.symm (t, x)) =
    1/2 * (‖A.electricField t x‖ ^ 2 - ‖A.magneticField t x‖ ^ 2) := by
  rw [kineticTerm_eq_sum]
  simp only [one_div]
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2, μ', 2, ν']
    rw [fieldStrengthMatrix_eq_electric_magnetic A t x hA,
      fieldStrengthMatrix_eq_electric_magnetic A t x hA]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  ring

/-!

## B. Variational gradient of the kinetic term

We define the variational gradient of the kinetic term, which is the left-hand side
of Gauss's law and Ampère's law in vacuum.

-/

/-- A local instance of an inner product structure on `SpaceTime`. -/
noncomputable local instance : InnerProductSpace ℝ SpaceTime := SpaceTime.innerProductSpace 3

/-- The variational gradient of the kinetic term of an electromagnetic potential. -/
noncomputable def gradKineticTerm (A : ElectromagneticPotential) : SpaceTime → Lorentz.Vector :=
  (δ (q':=A), ∫ x, kineticTerm q' x)

/-!

### B.1. Variational gradient in terms of fderiv

We give a first simplification of the variational gradient in terms of the
a complicated expression involving `fderiv`. This is not very useful in itself,
but acts as a starting point for further simplifications.

-/
lemma gradKineticTerm_eq_sum_fderiv (A : ElectromagneticPotential)
    (hA : ContDiff ℝ ∞ A) :
    let F' : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) → (SpaceTime → ℝ) →
    SpaceTime → Lorentz.Vector := fun μν => (fun ψ x =>
    -(fderiv ℝ (fun x' => (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x' * ∂_ μν.1 A x' μν.2) x)
              (Lorentz.Vector.basis μν.1) •
          Lorentz.Vector.basis μν.2 +
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 *
          (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) •
        Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) •
          Lorentz.Vector.basis μν.1))
    A.gradKineticTerm = fun x => ∑ μν, F' μν (fun x' => -1 / 2 * (fun _ => 1) x') x := by
  apply HasVarGradientAt.varGradient
  change HasVarGradientAt (fun A' x => ElectromagneticPotential.kineticTerm A' x) _ A
  conv =>
    enter [1, A', x]
    rw [kineticTerm_eq_sum_potential]
  let F : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) → (SpaceTime → Lorentz.Vector) →
    SpaceTime → ℝ := fun (μ, ν) A' x =>
        (η μ μ * η ν ν * ∂_ μ A' x ν ^ 2 - ∂_ μ A' x ν * ∂_ ν A' x μ)
  let F' : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) → (SpaceTime → ℝ) →
    SpaceTime → Lorentz.Vector := fun μν => (fun ψ x =>
    -(fderiv ℝ (fun x' => (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x' * ∂_ μν.1 A x' μν.2) x)
              (Lorentz.Vector.basis μν.1) •
          Lorentz.Vector.basis μν.2 +
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 *
          (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) •
        Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) •
            Lorentz.Vector.basis μν.1))
  have F_hasVarAdjDerivAt (μν : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
      HasVarAdjDerivAt (F μν) (F' μν) A := by
    have h1 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
    have h1' := HasVarAdjDerivAt.const_mul _ _ A h1 (c := η μν.1 μν.1 * η μν.2 μν.2)
    have h2 :=
      HasVarAdjDerivAt.mul _ _ _ _ A (deriv_hasVarAdjDerivAt μν.1 μν.2 A hA)
        (deriv_hasVarAdjDerivAt μν.2 μν.1 A hA)
    have h3 := HasVarAdjDerivAt.neg _ _ A h2
    have h4 := HasVarAdjDerivAt.add _ _ _ _ _ h1' h3
    convert h4
    simp [F]
    ring
  have F_sum_hasVarAdjDerivAt :
      HasVarAdjDerivAt (fun A' x => ∑ μ, ∑ ν, F (μ, ν) A' x) (fun ψ x => ∑ μν, F' μν ψ x) A := by
    convert HasVarAdjDerivAt.sum _ _ A (hA) (fun i => F_hasVarAdjDerivAt i)
    exact Eq.symm (Fintype.sum_prod_type fun x => F x _ _)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A F_sum_hasVarAdjDerivAt (c := -1/2)
  change HasVarGradientAt (fun A' x => -1 / 2 * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  apply HasVarGradientAt.intro _ hF_mul
  rfl

/-!

### B.2. Writing the variational gradient as a sums over double derivatives of the potential

We rewrite the variational gradient as a simple double sum over
second derivatives of the potential.

-/

lemma gradKineticTerm_eq_sum_sum (A : ElectromagneticPotential) (x : SpaceTime)
    (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm x = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  rw [gradKineticTerm_eq_sum_fderiv A ha]
  calc _
      _ = ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν : (Fin 1 ⊕ Fin 3)),
      (- (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν +
        -(fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν +
      -(-(fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ)
          • Lorentz.Vector.basis ν +
      -(fderiv ℝ (fun x' => -1 / 2 * ∂_ μ A x' ν) x) (Lorentz.Vector.basis ν)
        • Lorentz.Vector.basis μ)) := by
        dsimp
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        simp only [mul_one, neg_smul, neg_add_rev, neg_neg, mul_neg]
        ring_nf
      _ = ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν : (Fin 1 ⊕ Fin 3)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) +
      ((fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ))) •
        Lorentz.Vector.basis ν +
        (fderiv ℝ (fun x' => -1 / 2 * ∂_ μ A x' ν) x) (Lorentz.Vector.basis ν) •
          Lorentz.Vector.basis μ) := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        rw [neg_add, ← add_assoc, ← neg_smul, ← add_smul]
        congr 1
        · ring_nf
        · simp [← neg_smul]
      _ = ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν : (Fin 1 ⊕ Fin 3)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2) * ∂_ μ A x' ν) x)
        (Lorentz.Vector.basis μ) +
      2 * ((fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ)))) •
        Lorentz.Vector.basis ν := by
        conv_lhs => enter [2, μ]; rw [Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
        conv_lhs => enter [2]; rw [Finset.sum_comm]
        rw [← Finset.sum_add_distrib]
        conv_lhs => enter [2, μ]; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        ring_nf
      _ = ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν : (Fin 1 ⊕ Fin 3)),
      ((- 2 * ((η μ μ * η ν ν * -1 / 2) * ∂_ μ (fun x' => ∂_ μ A x' ν) x) +
      2 * ((-1 / 2 * ∂_ μ (fun x' => ∂_ ν A x' μ) x)))) • Lorentz.Vector.basis ν := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        congr
        · rw [fderiv_const_mul]
          simp [SpaceTime.deriv_eq]
          conv => enter [2, x]; rw [SpaceTime.deriv_eq]
          apply diff_partial μ ν
        · rw [fderiv_const_mul]
          simp [SpaceTime.deriv_eq]
          conv => enter [2, x]; rw [SpaceTime.deriv_eq]
          apply diff_partial ν μ
      _ = ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        ring_nf
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by rw [Finset.sum_comm]

/-!

### B.3. Variational gradient as a sums over fieldStrengthMatrix

We rewrite the variational gradient as a simple double sum over the
fieldStrengthMatrix.

-/

lemma gradKineticTerm_eq_fieldStrength (A : ElectromagneticPotential)
    (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm x = ∑ (ν : (Fin 1 ⊕ Fin 3)), η ν ν •
    (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
    • Lorentz.Vector.basis ν := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  calc _
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by
          rw [gradKineticTerm_eq_sum_sum A x ha]
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (η μ μ * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        η ν ν * ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          ring_nf
          simp
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν) x -
            ∂_ μ (fun x' => η ν ν * ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial μ ν
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial ν μ
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν -
            η ν ν * ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_fun_sub]
          simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply]
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial μ ν
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial ν μ
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          funext x
          rw [toFieldStrength_basis_repr_apply_eq_single]
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), (η ν ν *
          ∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [← Finset.sum_smul, Finset.mul_sum]
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), η ν ν •
          (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [smul_smul]

/-!

### B.4. Variational gradient in terms of the Guass's and Ampère laws

We rewrite the variational gradient in terms of the electric and magnetic fields,
explicitly relating it to Gauss's law and Ampère's law.

-/
open Time

lemma gradKineticTerm_eq_electric_magnetic(A : ElectromagneticPotential)
    (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm x =
    Space.div (A.electricField (toTimeAndSpace x).1) (toTimeAndSpace x).2 •
      Lorentz.Vector.basis (Sum.inl 0) +
    ∑ i, (∂ₜ (fun t => A.electricField t (toTimeAndSpace x).2) (toTimeAndSpace x).1 i-
          Space.curl (A.magneticField (toTimeAndSpace x).1) (toTimeAndSpace x).2 i) •
          Lorentz.Vector.basis (Sum.inr i) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  have hdiff (μ ν) : Differentiable ℝ fun x => (A.fieldStrengthMatrix x) (μ, ν) := by
    conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
      SpaceTime.deriv_eq, SpaceTime.deriv_eq]
    apply Differentiable.sub
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).1 (μ, ν).2
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).2 (μ, ν).1
  calc _
      _ = ∑ (ν : (Fin 1 ⊕ Fin 3)), η ν ν •
          (∑ (μ : (Fin 1 ⊕ Fin 3)),
          (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x)) • Lorentz.Vector.basis ν := by
          rw [gradKineticTerm_eq_fieldStrength A x ha]
  have term_inl_0 : (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inl 0)) x)) =
        (∇ ⬝ A.electricField (toTimeAndSpace x).1) (toTimeAndSpace x).2 := by
      simp [Fintype.sum_sum_type]
      conv_lhs =>
        enter [2, i]
        rw [SpaceTime.deriv_sum_inr _ (hdiff _ _)]
        simp only [Fin.isValue]
        enter [2, y]
        rw [fieldStrengthMatrix_eq_electric_magnetic _ _ _ (ha.differentiable (by simp))]
      simp only
      rw [Space.div]
      simp [Space.coord]
  have term_inr (i : Fin 3) : (∑ (μ : (Fin 1 ⊕ Fin 3)),
      (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inr i)) x)) =
        (-∂ₜ (fun t => A.electricField t (toTimeAndSpace x).2) (toTimeAndSpace x).1 i +
        (∇ × (A.magneticField (toTimeAndSpace x).1)) (toTimeAndSpace x).2 i) := by
      simp [Fintype.sum_sum_type]
      congr
      conv_lhs =>
        rw [SpaceTime.deriv_sum_inl _ (hdiff _ _)]
        simp only [Fin.isValue]
        enter [1, t]
        rw [fieldStrengthMatrix_eq_electric_magnetic _ _ _ (ha.differentiable (by simp))]
        simp
      simp [Time.deriv]
      rw [fderiv_pi]
      rfl
      intro i
      have h1 := electricField_differentiable (ha.of_le (ENat.LEInfty.out))
      fun_prop
      conv_lhs =>
        enter [2, i]
        rw [SpaceTime.deriv_sum_inr _ (hdiff _ _)]
        simp only
        enter [2, y]
        rw [fieldStrengthMatrix_eq_electric_magnetic _ _ _ (ha.differentiable (by simp))]
      fin_cases i
      all_goals
        simp [Fin.sum_univ_three]
        rw [Space.curl]
        simp [Space.coord]
        simp [Space.deriv_eq]
        ring
  rw [Fintype.sum_sum_type, Fin.sum_univ_one, term_inl_0]
  conv_lhs => enter [2, 2, i]; rw [term_inr]
  simp only [Fin.isValue, inl_0_inl_0, one_smul, inr_i_inr_i, neg_smul,
    add_right_inj]
  congr
  funext x
  rw [← neg_smul]
  ring_nf

end ElectromagneticPotential

end Electromagnetism
