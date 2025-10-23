/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a function from
spacetime to contravariant Lorentz vectors. from this we can define
the field strength tensor, the kinetic energy, and the electric and magnetic fields.

## ii. Key results

- `ElectromagneticPotential`: is the type of electromagnetic potentials.
- `ElectromagneticPotential.deriv`: the derivative tensor `∂_μ A^ν`.
- `ElectromagneticPotential.toFieldStrength`: the field strength tensor `F_μ^ν`.
- `ElectromagneticPotential.scalarPotential`: the scalar potential `φ`.
- `ElectromagneticPotential.vectorPotential`: the vector potential `A_i`.
- `ElectromagneticPotential.electricField`: the electric field `E`.
- `ElectromagneticPotential.magneticField`: the magnetic field `B`.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. The action on the space-time derivatives
  - A.2. Differentiability
  - A.3. Varitational adjoint derivative of component
  - A.4. Variational adjoint derivative of derivatives of the potential
- B. The derivative tensor of the electricomagnetic potential
  - B.1. Equivariance of the derivative tensor
  - B.2. The elements of the derivative tensor in terms of the basis
- C. The field strength tensor
  - C.1. Basic equalitites
  - C.2. Elements of the field strength tensor in terms of basis
  - C.3. The field strength matrix
    - C.3.1. Differentiability of the field strength matrix
  - C.4. The antisymmetry of the field strength tensor
  - C.5. Equivariance of the field strength tensor
  - C.6. Linearity of the field strength tensor
- E. The electric and magnetic fields
  - E.1. The scalar potential
  - E.2. The vector potential
  - E.3. The electric field
    - E.3.1. Relation between the electric field and the field strength matrix
    - E.3.2. Differentiability of the electric field
  - E.4. The magnetic field
    - E.4.1. Relation between the magnetic field and the field strength matrix
  - E.5. Field strength matrix in terms of the electric and magnetic fields

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/
/-- The electricomagnetic potential is a tensor `A^μ`. -/
noncomputable abbrev ElectromagneticPotential (d : ℕ := 3) :=
  SpaceTime d → Lorentz.Vector d

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

### A.1. The action on the space-time derivatives

Given a ElectromagneticPotential `A^μ`, we can consider its derivative `∂_μ A^ν`.
Under a Lorentz transformation `Λ`, this transforms as
`∂_ μ (fun x => Λ • A (Λ⁻¹ • x))`, we write an expression for this in terms of the tenosr.
`∂_ ρ A (Λ⁻¹ • x) κ`.

-/

lemma spaceTime_deriv_action_eq_sum {d} {μ ν : Fin 1 ⊕ Fin d} {x : SpaceTime d}
    (Λ : LorentzGroup d) (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) :
    ∂_ μ (fun x => Λ • A (Λ⁻¹ • x)) x ν =
    ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ := by
  calc _
    _ = ((Λ • (∂_ μ (fun x => A (Λ⁻¹ • x)) x)) ν) := by
      have hdif : ∀ i, DifferentiableAt ℝ (fun x => A (Λ⁻¹ • x) i) x := by
          rw [← differentiableAt_pi]
          conv =>
            enter [2, x]; rw [← Lorentz.Vector.actionCLM_apply]
          apply Differentiable.differentiableAt
          apply Differentiable.comp hA
          exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)
      trans ∂_ μ (fun x => (Λ • A (Λ⁻¹ • x)) ν) x
      · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq]
        rw [fderiv_pi]
        rfl
        rw [← differentiableAt_pi]
        conv =>
          enter [2, x]; rw [← Lorentz.Vector.actionCLM_apply, ← Lorentz.Vector.actionCLM_apply]
        apply Differentiable.differentiableAt
        apply Differentiable.comp
        · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ)
        · apply Differentiable.comp
          · exact hA
          · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)
      conv_lhs =>
        enter [2, x]
        rw [Lorentz.Vector.smul_eq_sum]
      rw [SpaceTime.deriv_eq]
      rw [fderiv_fun_sum (𝕜 := ℝ)]
      conv_lhs =>
        enter [1, 2, i]
        rw [fderiv_const_mul (hdif i)]
      simp only [Nat.reduceSucc, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext κ
      congr
      rw [SpaceTime.deriv_eq, fderiv_pi]
      rfl
      · exact fun i => hdif i
      · intro i _
        apply DifferentiableAt.const_mul
        exact hdif i
    _ = (((Λ • (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x)))) ν) := by
      rw [SpaceTime.deriv_comp_lorentz_action]
      · exact hA
    _ = (∑ κ, Λ.1 ν κ * (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) := by
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext j
      congr
      rw [Lorentz.Vector.apply_sum]
      rfl
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun ρ _ => ?_)
  simp only [Nat.reduceSucc, smul_eq_mul]
  ring

/-!

### A.2. Differentiability

We show that the components of field strength tensor are differentiable if the potential is.
-/

lemma differentiable_component {d : ℕ}
    (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) (μ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => A x μ) := by
  revert μ
  rw [← differentiable_pi]
  exact hA

/-!

### A.3. Varitational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

/-- A local instance of the inner product structure on `SpaceTime`. -/
noncomputable local instance {d : ℕ}: InnerProductSpace ℝ (SpaceTime d) :=
  SpaceTime.innerProductSpace d

open ContDiff
lemma hasVarAdjDerivAt_component {d : ℕ} (μ : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime d → Lorentz.Vector d) x => A' x μ)
          (fun (A' : SpaceTime d → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime d → Lorentz.Vector d → ℝ := fun x v => v μ
  let f' : SpaceTime d → Lorentz.Vector d → ℝ → Lorentz.Vector d := fun x _ c =>
    c • Lorentz.Vector.basis μ
  change HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
  apply HasVarAdjDerivAt.fmap
  · fun_prop
  · fun_prop
  intro x A
  refine { differentiableAt := ?_, hasAdjoint_fderiv := ?_ }
  · fun_prop
  refine { adjoint_inner_left := ?_ }
  intro u v
  simp [f,f']
  rw [PiLp.inner_apply]
  simp only [Lorentz.Vector.apply_smul, Lorentz.Vector.basis_apply, mul_ite, mul_one, mul_zero,
    RCLike.inner_apply, conj_trivial, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    mul_eq_mul_right_iff]
  left
  rfl

/-!

### A.4. Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt {d} (μ ν : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime d → Lorentz.Vector d) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime d →
    Lorentz.Vector d) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  simp only
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)

/-!

## B. The derivative tensor of the electricomagnetic potential

We define the derivative as a tensor in `Lorentz.CoVector ⊗[ℝ] Lorentz.Vector` for the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/

/-- The derivative of the electric potential, `∂_μ A^ν`. -/
noncomputable def deriv {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  ∑ μ, ∑ ν, (∂_ μ A x ν) • Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν

/-!

### B.1. Equivariance of the derivative tensor

We show that the derivative tensor is equivariant under the action of the Lorentz group.
That is, `∂_μ (fun x => Λ • A (Λ⁻¹ • x)) = Λ • (∂_μ A (Λ⁻¹ • x))`, or in words:
applying the Lorentz transformation to the potential and then taking the derivative is the same
as taking the derivative and then applying the Lorentz transformation to the resulting tensor.

-/
lemma deriv_equivariant {d} {x : SpaceTime d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) : deriv (fun x => Λ • A (Λ⁻¹ • x)) x = Λ • (deriv A (Λ⁻¹ • x)) := by
    calc _
      _ = ∑ μ, ∑ ν, ∑ κ, ∑ ρ, (Λ.1 ν κ * (Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) •
          (Lorentz.CoVector.basis μ) ⊗ₜ[ℝ]
          Lorentz.Vector.basis ν := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        rw [spaceTime_deriv_action_eq_sum Λ A hf]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        congr 1
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul]
        ring
      _ = ∑ μ, ∑ ν, ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) •
          (Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        refine Finset.sum_congr rfl (fun κ _ => ?_)
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [smul_tmul, tmul_smul, tmul_smul, smul_smul, smul_smul]
        congr 1
        simp only [Nat.reduceSucc, smul_eq_mul]
        ring
      _ = ∑ κ, ∑ ρ, ∑ μ, ∑ ν, (∂_ ρ A (Λ⁻¹ • x) κ) •
          (Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => enter [2, κ, 2, μ]; rw [Finset.sum_comm]
        conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • (∑ μ, Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (∑ ν, Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        conv_rhs =>
          enter [2, κ,2, ρ]; rw [sum_tmul, Finset.smul_sum]
          enter [2, μ]; rw [tmul_sum, Finset.smul_sum];
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • (Λ • (Lorentz.CoVector.basis ρ)) ⊗ₜ[ℝ]
          (Λ • Lorentz.Vector.basis κ) := by
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        congr 2
        · rw [Lorentz.CoVector.smul_basis]
        · rw [Lorentz.Vector.smul_basis]
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • Λ • ((Lorentz.CoVector.basis ρ) ⊗ₜ[ℝ]
        Lorentz.Vector.basis κ) := by
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [Tensorial.smul_prod]
    rw [deriv]
    conv_rhs => rw [← Tensorial.smulLinearMap_apply]
    rw [Finset.sum_comm]
    simp
    rfl

/-!

### B.2. The elements of the derivative tensor in terms of the basis

We show that in the standard basis, the elements of the derivative tensor
are just equal to `∂_ μ A x ν`.

-/

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) μν =
    ∂_ μν.1 A x μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A x)) b =
    ∂_ (finSumFinEquiv.symm (b 0)) A x (finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

/-!

## C. The field strength tensor

We define the field strength tensor `F_μ^ν` in terms of the derivative of the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/
/-- The field strength from an electromagnetic potential, as a tensor `F_μ^ν`. -/
noncomputable def toFieldStrength {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  Tensorial.toTensor.symm
  (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν) + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ)

/-!

### C.1. Basic equalitites

-/

lemma toFieldStrength_eq_add {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (PermCond.auto)
      {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength]
  simp only [map_add, map_neg]
  rw [sub_eq_add_neg]
  apply congrArg₂
  · rfl
  · rw [permT_permT]
    rfl

lemma toTensor_toFieldStrength {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    Tensorial.toTensor (toFieldStrength A x) =
    (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - (permT ![1, 0] (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength_eq_add]
  simp

/-!

### C.2. Elements of the field strength tensor in terms of basis

-/

lemma toTensor_toFieldStrength_basis_repr {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    ∑ κ, (η (finSumFinEquiv.symm (b 0)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 1)) -
      η (finSumFinEquiv.symm (b 1)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 0))) := by
  rw [toTensor_toFieldStrength]
  simp only [Tensorial.self_toTensor_apply, map_sub,
    Finsupp.coe_sub, Pi.sub_apply]
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [1, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [1, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (finSumFinEquiv.symm n) A x (finSumFinEquiv.symm (b 1))
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (finSumFinEquiv.symm (b 1)) (finSumFinEquiv.symm n)
  conv_lhs =>
    enter [2, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (finSumFinEquiv.symm n) A x (finSumFinEquiv.symm (b 0))
  rw [← Finset.sum_sub_distrib]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fin.isValue, Equiv.symm_apply_apply]

lemma toFieldStrength_tensor_basis_eq_basis {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (toFieldStrength A x)
      (finSumFinEquiv.symm (b 0), finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.Vector.basis (d := d)).reindex Lorentz.Vector.indexEquiv.symm).tensorProduct
          (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
          ((Lorentz.Vector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
          (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
        ext b
        match b with
        | ⟨i, j⟩ =>
        simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply]
  congr 1

lemma toFieldStrength_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ∑ κ, ((η μν.1 κ * ∂_ κ A x μν.2) - η μν.2 κ * ∂_ κ A x μν.1) := by
  match μν with
  | (μ, ν) =>
  trans (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν); swap
  · rw [toTensor_toFieldStrength_basis_repr]
    simp
  rw [toFieldStrength_tensor_basis_eq_basis]
  congr 1
  change _ = (finSumFinEquiv.symm (finSumFinEquiv μ), finSumFinEquiv.symm (finSumFinEquiv ν))
  simp

lemma toFieldStrength_basis_repr_apply_eq_single {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ((η μν.1 μν.1 * ∂_ μν.1 A x μν.2) - η μν.2 μν.2 * ∂_ μν.2 A x μν.1) := by
  rw [toFieldStrength_basis_repr_apply]
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single μν.1, Finset.sum_eq_single μν.2]
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp

/-!

### C.3. The field strength matrix

We define the field strength matrix to be the matrix representation of the field strength tensor
in the standard basis.

This is currently not used as much as it could be.
-/
open ContDiff

/-- The matrix corresponding to the field strength in the standard basis. -/
noncomputable abbrev fieldStrengthMatrix {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :=
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x)

lemma fieldStrengthMatrix_eq_tensor_basis_repr {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : (Fin 1 ⊕ Fin d)) :
    A.fieldStrengthMatrix x (μ, ν) =
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν) := by
  rw [toFieldStrength_tensor_basis_eq_basis]
  simp only [Equiv.symm_apply_apply]
  rfl

/-!

#### C.3.1. Differentiability of the field strength matrix

-/

lemma fieldStrengthMatrix_differentiable {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (A.fieldStrengthMatrix · μν) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact ((contDiff_succ_iff_fderiv (n := 1)).mp hA).2.2.differentiable
        (Preorder.le_refl 1)
    · fun_prop
  conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply Differentiable.sub
  apply Differentiable.const_mul
  · exact diff_partial _ _
  apply Differentiable.const_mul
  · exact diff_partial _ _

lemma fieldStrengthMatrix_contDiff {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (A.fieldStrengthMatrix · μν) := by
  conv => enter [3, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply ContDiff.sub
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert ν
    rw [← contDiff_euclidean]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert μ
    rw [← contDiff_euclidean]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop

lemma fieldStrengthMatrix_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μν) :
    ContDiff ℝ ∞ (A.fieldStrengthMatrix · μν) := by
  apply fieldStrengthMatrix_contDiff
  simpa using hA

/-!

### C.4. The antisymmetry of the field strength tensor

We show that the field strength tensor is antisymmetric.

-/

lemma toFieldStrength_antisymmetric {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    {A.toFieldStrength x | μ ν = - (A.toFieldStrength x | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_toFieldStrength_basis_repr]
  rw [permT_basis_repr_symm_apply, map_neg]
  simp only [Nat.reduceAdd, Fin.isValue, Nat.reduceSucc, Finsupp.coe_neg, Pi.neg_apply]
  rw [toTensor_toFieldStrength_basis_repr]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [Fin.isValue, Fin.cast_eq_self, neg_sub]
  rfl

lemma fieldStrengthMatrix_antisymm {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, ν) = - A.fieldStrengthMatrix x (ν, μ) := by
  rw [toFieldStrength_basis_repr_apply, toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp

@[simp]
lemma fieldStrengthMatrix_diag_eq_zero {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, μ) = 0 := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp

/-!

### C.5. Equivariance of the field strength tensor

We show that the field strength tensor is equivariant under the action of the Lorentz group.
That is transforming the potential and then taking the field strength is the same
as taking the field strength and then transforming the resulting tensor.

-/

lemma toFieldStrength_equivariant {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength (fun x => Λ • A (Λ⁻¹ • x)) x =
      Λ • toFieldStrength A (Λ⁻¹ • x) := by
  rw [toFieldStrength, deriv_equivariant A Λ hf, ← actionT_contrMetric Λ, toFieldStrength]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, map_neg,
    permT_equivariant, map_add, ← Tensorial.smul_toTensor_symm, Tensorial.smul_add,
    Tensorial.smul_neg]

lemma fieldStrengthMatrix_equivariant {d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d) (hf : Differentiable ℝ A) (x : SpaceTime d)
    (μ : (Fin 1 ⊕ Fin d)) (ν : Fin 1 ⊕ Fin d) :
    fieldStrengthMatrix (fun x => Λ • A (Λ⁻¹ • x)) x (μ, ν) =
    ∑ κ, ∑ ρ, (Λ.1 μ κ * Λ.1 ν ρ) * A.fieldStrengthMatrix (Λ⁻¹ • x) (κ, ρ) := by
  rw [fieldStrengthMatrix, toFieldStrength_equivariant A Λ hf x]
  conv_rhs =>
    enter [2, κ, 2, ρ]
    rw [fieldStrengthMatrix]
  generalize A.toFieldStrength (Λ⁻¹ • x) = F
  let P (F : Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d) : Prop :=
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (Λ • F)) (μ, ν) =
    ∑ κ, ∑ ρ, Λ.1 μ κ * Λ.1 ν ρ *
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr F) (κ, ρ)
  change P F
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    dsimp [P]
    rw [Tensorial.smul_prod]
    simp only [Basis.tensorProduct_repr_tmul_apply, Lorentz.Vector.basis_repr_apply,
      Lorentz.CoVector.basis_repr_apply, smul_eq_mul]
    rw [Lorentz.Vector.smul_eq_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [Lorentz.Vector.smul_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring
  · intro F1 F2 h1 h2
    simp [P, h1, h2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring

/-!

### C.6. Linearity of the field strength tensor

We show that the field strength tensor is linear in the potential.

-/

lemma toFieldStrength_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    toFieldStrength (A1 + A2) x = toFieldStrength A1 x + toFieldStrength A2 x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  rw [fderiv_add]
  simp only [ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add]
  ring
  · exact hA1.differentiableAt
  · exact hA2.differentiableAt

lemma fieldStrengthMatrix_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    (A1 + A2).fieldStrengthMatrix x =
    A1.fieldStrengthMatrix x + A2.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_add A1 A2 x hA1 hA2]
  conv_rhs => rw [fieldStrengthMatrix, fieldStrengthMatrix]
  simp

lemma toFieldStrength_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    toFieldStrength (c • A) x = c • toFieldStrength A x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  rw [fderiv_const_smul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Lorentz.Vector.apply_smul]
  ring
  exact hA.differentiableAt

lemma fieldStrengthMatrix_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    (c • A).fieldStrengthMatrix x = c • A.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_smul c A x hA]
  conv_rhs => rw [fieldStrengthMatrix]
  simp

/-!

## E. The electric and magnetic fields

We now define the scalar and vector potentials, and the electric and magnetic fields
in terms of the electromagnetic potential.
This breaks the manifest Lorentz covariance.

-/

/-

### E.1. The scalar potential

This assumes that the spee of light is set to `1`.
-/

/-- The scalar potential from the electromagnetic potential. -/
noncomputable def scalarPotential (A : ElectromagneticPotential) : Time → Space → ℝ := timeSlice <|
  fun x => A x (Sum.inl 0)

/-!

### E.2. The vector potential

-/

/-- The vector potential from the electromagnetic potential. -/
noncomputable def vectorPotential (A : ElectromagneticPotential) :
    Time → Space → EuclideanSpace ℝ (Fin 3) := timeSlice <|
  fun x i => A x (Sum.inr i)

/-!

### E.3. The electric field

-/

open Space Time

/-- The electric field from the electromagnetic potential. -/
noncomputable def electricField (A : ElectromagneticPotential) : ElectricField :=
  fun t x => - ∇ (A.scalarPotential t) x - ∂ₜ (fun t => A.vectorPotential t x) t

lemma electricField_eq (A : ElectromagneticPotential) :
    A.electricField = fun t x =>
      - ∇ (A.scalarPotential t) x - ∂ₜ (fun t => A.vectorPotential t x) t := rfl

/-!

#### E.3.1. Relation between the electric field and the field strength matrix

-/

lemma electricField_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (i : Fin 3) (hA : Differentiable ℝ A) :
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

#### E.3.2. Differentiability of the electric field

-/

lemma electricField_differentiable {A : ElectromagneticPotential}
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
    ∘ (toTimeAndSpace (d := 3)).symm)
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable (hA)
  · exact ContinuousLinearEquiv.differentiable toTimeAndSpace.symm

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

end ElectromagneticPotential

end Electromagnetism
