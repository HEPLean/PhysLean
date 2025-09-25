/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.SpaceAndTime.Space.VectorIdentities
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
- `ElectromagneticPotential.vectorPotential`: the vector potential `A^i`.
- `ElectromagneticPotential.electricField`: the electric field `E^i`.
- `ElectromagneticPotential.magneticField`: the magnetic field `B^i`.

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
noncomputable abbrev ElectromagneticPotential :=
  SpaceTime → Lorentz.Vector

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A.1. The action on the space-time derivatives

Given a ElectromagneticPotential `A^μ`, we can consider its derivative `∂_μ A^ν`.
Under a Lorentz transformation `Λ`, this transforms as
`∂_ μ (fun x => Λ • A (Λ⁻¹ • x))`, we write an expression for this in terms of the tenosr.
`∂_ ρ A (Λ⁻¹ • x) κ`.

-/

lemma spaceTime_deriv_action_eq_sum {μ ν : Fin 1 ⊕ Fin 3}
    (Λ : LorentzGroup 3) (A : ElectromagneticPotential) (hA : Differentiable ℝ A) :
    ∂_ μ (fun x => Λ • A (Λ⁻¹ • x)) x ν =
    ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ := by
  calc _
    _ = ((Λ • (∂_ μ  (fun x => A (Λ⁻¹ • x) ) x)) ν) := by
      have hdif  : ∀ i, DifferentiableAt ℝ (fun x => A (Λ⁻¹ • x) i) x := by
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
        rw [← differentiableAt_pi ]
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
      simp
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
    _ =  (((Λ • (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x)))) ν) := by
      rw [SpaceTime.deriv_comp_lorentz_action]
      · exact hA
    _ = (∑ κ, Λ.1 ν κ * (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) := by
      rw [Lorentz.Vector.smul_eq_sum]
      rfl
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun ρ _ => ?_)
  simp
  ring

/-!

## A.2. Differentiability

We show that the components of field strength tensor are differentiable if the potential is.
-/

lemma differentiable_component
    (A : ElectromagneticPotential) (hA : Differentiable ℝ A) (μ : Fin 1 ⊕ Fin 3) :
    Differentiable ℝ (fun x => A x μ) := by
  revert μ
  rw [← differentiable_pi]
  exact hA

/-!

## A.3. Varitational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

noncomputable local instance : InnerProductSpace ℝ SpaceTime :=  SpaceTime.innerProductSpace  3

open ContDiff
lemma hasVarAdjDerivAt_component  (μ : Fin 1 ⊕ Fin 3) (A : SpaceTime → Lorentz.Vector)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime → Lorentz.Vector) x => A' x μ)
          (fun (A' : SpaceTime → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime → Lorentz.Vector → ℝ := fun x v => v μ
  let f' : SpaceTime → Lorentz.Vector → ℝ → Lorentz.Vector  := fun x _ c => c • Lorentz.Vector.basis μ
  change  HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
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
  simp
  left
  let fCLM : Lorentz.Vector →L[ℝ] ℝ := {
    toFun := fun v => v μ,
    map_add' := by intros; simp,
    map_smul' := by intros; simp
    cont := by fun_prop
  }
  change _ = (fderiv ℝ fCLM A) u
  simp only [ContinuousLinearMap.fderiv]
  rfl

/-!

## A.4 Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt (μ ν : Fin 1 ⊕ Fin 3) (A : SpaceTime → Lorentz.Vector)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime → Lorentz.Vector) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime → Lorentz.Vector) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  simp
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)


/-!

## B. The derivative tensor of the electricomagnetic potential

We define the derivative as a tensor in `Lorentz.CoVector ⊗[ℝ] Lorentz.Vector` for the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/

/-- The derivative of the electric potential, `∂_μ A^ν`. -/
noncomputable def deriv  (A : ElectromagneticPotential) :
    SpaceTime → Lorentz.CoVector ⊗[ℝ] Lorentz.Vector := fun x =>
  ∑ μ, ∑ ν, (∂_ μ A x ν) • Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν

/-!

## B.1. Equivariance of the derivative tensor

We show that the derivative tensor is equivariant under the action of the Lorentz group.
That is, `∂_μ (fun x => Λ • A (Λ⁻¹ • x)) = Λ • (∂_μ A (Λ⁻¹ • x))`, or in words:
applying the Lorentz transformation to the potential and then taking the derivative is the same
as taking the derivative and then applying the Lorentz transformation to the resulting tensor.

-/
lemma deriv_equivariant {x : SpaceTime} (A : ElectromagneticPotential) (Λ : LorentzGroup 3)
    (hf : Differentiable ℝ A) : deriv (fun x => Λ • A (Λ⁻¹ • x)) x = Λ • (deriv A (Λ⁻¹ • x)) := by
    calc  _
      _ =  ∑ μ, ∑ ν, ∑ κ, ∑ ρ, (Λ.1 ν κ * (Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) •
          (Lorentz.CoVector.basis μ) ⊗ₜ[ℝ]
          Lorentz.Vector.basis ν := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν  _ => ?_)
        rw [spaceTime_deriv_action_eq_sum Λ A hf]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        congr 1
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul]
        ring
      _ =  ∑ μ, ∑ ν, ∑ κ, ∑ ρ, ( ∂_ ρ A (Λ⁻¹ • x) κ) •
          (Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
         (Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν  _ => ?_)
        refine Finset.sum_congr rfl (fun κ _ => ?_)
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [smul_tmul, tmul_smul, tmul_smul, smul_smul, smul_smul]
        congr 1
        simp
        ring
      _ = ∑ κ, ∑ ρ, ∑ μ, ∑ ν, ( ∂_ ρ A (Λ⁻¹ • x) κ) •
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

### B.2. The elements of the derivative tensor in terms of the basis

We show that in the standard basis, the elements of the derivative tensor
are just equal to `∂_ μ A x ν`.

-/

@[simp]
lemma deriv_basis_repr_apply {μν : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)} (A : ElectromagneticPotential)
    (x : SpaceTime)  :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) μν =
    ∂_ μν.1 A x μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv]
  simp
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply (A : ElectromagneticPotential)
    (x : SpaceTime)  (b : ComponentIdx (S := realLorentzTensor) (Sum.elim ![Color.down] ![Color.up] ∘ ⇑finSumFinEquiv.symm)) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A x)) b =
    ∂_ (finSumFinEquiv.symm (b 0)) A x (finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := 3)).reindex Lorentz.CoVector.indexEquiv.symm).tensorProduct
          (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
          ((Lorentz.CoVector.basis (d := 3)).tensorProduct (Lorentz.Vector.basis (d := 3))).reindex
          (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm ) := by
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
/-- The field strength from an electromagnetic potential, as a tensor `F_μ^ν`.  -/
noncomputable def toFieldStrength (A : ElectromagneticPotential) :
    SpaceTime → Lorentz.Vector ⊗[ℝ] Lorentz.Vector := fun x =>
  Tensorial.toTensor.symm
  (permT id (PermCond.auto) {(η 3 | μ μ' ⊗ A.deriv x | μ' ν) + - (η 3 | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ)

/-!

### C.1. Basic equalitites

-/

lemma toFieldStrength_eq_add (A : ElectromagneticPotential) (x : SpaceTime) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id (PermCond.auto) {(η 3 | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (PermCond.auto) {(η 3 | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength]
  simp only [map_add, map_neg]
  rw [sub_eq_add_neg]
  apply congrArg₂
  · rfl
  · rw [permT_permT]
    rfl

lemma toTensor_toFieldStrength (A : ElectromagneticPotential) (x : SpaceTime) :
    Tensorial.toTensor (toFieldStrength A x) =
    (permT id (PermCond.auto) {(η 3 | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - (permT ![1, 0] (PermCond.auto) {(η 3 | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ):= by
  rw [toFieldStrength_eq_add]
  simp


/-!

## C.2. Elements of the field strength tensor in terms of basis

-/

lemma toTensor_toFieldStrength_basis_repr (A : ElectromagneticPotential) (x : SpaceTime)
    (b : ComponentIdx (S := realLorentzTensor)
      (Sum.elim ![Color.up] ![Color.up] ∘ ⇑finSumFinEquiv.symm)) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    ∑ κ, (η (finSumFinEquiv.symm (b 0)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 1)) -
      η (finSumFinEquiv.symm (b 1)) κ * ∂_ κ A x (finSumFinEquiv.symm (b 0))) := by
  rw [toTensor_toFieldStrength]
  simp only [ Tensorial.self_toTensor_apply, map_sub,
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
  simp only [Nat.reduceAdd, Fin.isValue, Equiv.symm_apply_apply]


lemma toFieldStrength_tensor_basis_eq_basis  (A : ElectromagneticPotential) (x : SpaceTime)
    (b : ComponentIdx (S := realLorentzTensor)
      (Sum.elim ![Color.up] ![Color.up] ∘ ⇑finSumFinEquiv.symm)) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (toFieldStrength A x)
      (finSumFinEquiv.symm (b 0), finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.Vector.basis (d := 3)).reindex Lorentz.Vector.indexEquiv.symm).tensorProduct
          (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
          ((Lorentz.Vector.basis (d := 3)).tensorProduct (Lorentz.Vector.basis (d := 3))).reindex
          (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm ) := by
        ext b
        match b with
        | ⟨i, j⟩ =>
        simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply]
  congr 1

lemma toFieldStrength_basis_repr_apply {μν : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)} (A : ElectromagneticPotential)
    (x : SpaceTime)  :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
     ∑ κ, ((η μν.1 κ * ∂_ κ A x μν.2) - η μν.2 κ * ∂_ κ A x μν.1) := by
  match μν with
  | (μ, ν) =>
  trans  (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => finSumFinEquiv μ | 1 => finSumFinEquiv ν); swap
  · rw [toTensor_toFieldStrength_basis_repr]
    simp
  rw [toFieldStrength_tensor_basis_eq_basis]
  congr 1
  change _  = (finSumFinEquiv.symm (finSumFinEquiv μ), finSumFinEquiv.symm (finSumFinEquiv ν))
  simp


lemma toFieldStrength_basis_repr_apply_eq_single {μν : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)} (A : ElectromagneticPotential)
    (x : SpaceTime)  :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
     ((η μν.1 μν.1 * ∂_ μν.1 A x μν.2) - η μν.2 μν.2 * ∂_ μν.2 A x μν.1) := by
  rw [toFieldStrength_basis_repr_apply]
  simp
  rw [Finset.sum_eq_single μν.1, Finset.sum_eq_single μν.2]
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp
    exact id (Ne.symm hb)
  · simp
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp
    exact id (Ne.symm hb)
  · simp

/-!

## C.3. The field strength matrix

We define the field strength matrix to be the matrix representation of the field strength tensor
in the standard basis.

This is currently not used as much as it could be.
-/
open ContDiff

/-- The matrix corresponding to the field strength in the standard basis. -/
noncomputable abbrev fieldStrengthMatrix (A : ElectromagneticPotential) (x : SpaceTime) :=
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x)

/-!

### C.3.1. Differentiability of the field strength matrix

-/

lemma fieldStrengthMatrix_differentiable {A : ElectromagneticPotential}
    {μν} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (A.fieldStrengthMatrix · μν) := by
  have diff_partial (μ) :  ∀ ν,  Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le hA (by simp))
    · fun_prop
  conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply Differentiable.sub
  apply Differentiable.const_mul
  · exact diff_partial _ _
  apply Differentiable.const_mul
  · exact diff_partial _ _

/-!

### C.4. The antisymmetry of the field strength tensor

We show that the field strength tensor is antisymmetric.

-/

lemma toFieldStrength_antisymmetric (A : ElectromagneticPotential) (x : SpaceTime) :
    {A.toFieldStrength x | μ ν = - (A.toFieldStrength x | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_toFieldStrength_basis_repr]
  rw [permT_basis_repr_symm_apply, map_neg]
  simp only [Nat.reduceAdd, Fin.isValue, Nat.reduceSucc, Function.comp_apply, Finsupp.coe_neg,
    Pi.neg_apply]
  rw [toTensor_toFieldStrength_basis_repr]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [Fin.isValue, Nat.reduceAdd, Fin.cast_eq_self, neg_sub]
  rfl

lemma fieldStrengthMatrix_antisymm (A : ElectromagneticPotential) (x : SpaceTime)
    (μ ν : Fin 1 ⊕ Fin 3) :
    A.fieldStrengthMatrix x (μ, ν) = - A.fieldStrengthMatrix x (ν, μ):= by
  rw [toFieldStrength_basis_repr_apply, toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp

@[simp]
lemma fieldStrengthMatrix_diag_eq_zero (A : ElectromagneticPotential) (x : SpaceTime)
    (μ : Fin 1 ⊕ Fin 3) :
   A.fieldStrengthMatrix x (μ, μ) = 0 := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp

/-!

## C.5. Equivariance of the field strength tensor

We show that the field strength tensor is equivariant under the action of the Lorentz group.
That is transforming the potential and then taking the field strength is the same
as taking the field strength and then transforming the resulting tensor.

-/

lemma toFieldStrength_equivariant (A : ElectromagneticPotential) (Λ : LorentzGroup 3)
    (hf : Differentiable ℝ A) (x : SpaceTime) :
    toFieldStrength (fun x => Λ • A (Λ⁻¹ • x)) x =
      Λ • toFieldStrength A (Λ⁻¹ • x) := by
  rw [toFieldStrength, deriv_equivariant A Λ hf, ← actionT_contrMetric Λ, toFieldStrength]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, map_neg,
    permT_equivariant, map_add, ← Tensorial.smul_toTensor_symm, Tensorial.smul_add,
    Tensorial.smul_neg]


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

/-!

#### E.3.1 Relation between the electric field and the field strength matrix

-/

lemma electricField_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (i : Fin 3) (hA : Differentiable ℝ A) :
    A.electricField t x i = -
    A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x)) (Sum.inl 0, Sum.inr i)  := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp
  rw [electricField]
  simp
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
    simp
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

#### E.3.2 Differentiability of the electric field

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


/-!

#### E.4.1 Relation between the magnetic field and the field strength matrix

-/

lemma magneticField_fst_eq_fieldStrengthMatrix (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField t x 0 =
    - A.fieldStrengthMatrix (SpaceTime.toTimeAndSpace.symm (t, x))  (Sum.inr 1, Sum.inr 2) := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp
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
  simp
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp
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
  simp
  rw [magneticField]
  simp [Space.curl, Space.coord]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr _ hA]
    simp
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

### E.6 Field strength matrix in terms of the electric and magnetic fields

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
    |  0, 1 => - A.magneticField t x 2
    |  0, 2 =>  A.magneticField t x 1
    |  1,  0 =>  A.magneticField t x 2
    |  1,  1 => 0
    | 1, 2 => - A.magneticField t x 0
    |  2, 0 => - A.magneticField t x 1
    |  2, 1 => A.magneticField t x 0
    | 2, 2 => 0 := by
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => simp
  | Sum.inl 0, Sum.inr i => simp [electricField_eq_fieldStrengthMatrix A t x i hA]
  | Sum.inr i, Sum.inl 0 =>
    simp [electricField_eq_fieldStrengthMatrix A t x i hA]
    exact fieldStrengthMatrix_antisymm A (toTimeAndSpace.symm (t, x)) (Sum.inr i) (Sum.inl 0)
  | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0,  0 => simp
    |  0,  1 =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
    |  0,  2 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
    | 1,  0  =>
      simp [magneticField_thd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    |  1,  1 => simp
    |  1,  2 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
    |  2,  0 =>
      simp [magneticField_snd_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    |  2,  1 =>
      simp [magneticField_fst_eq_fieldStrengthMatrix A t x hA]
      rw [fieldStrengthMatrix_antisymm]
    |  2,  2 => simp



/-!

## D. The kinetic term

The kinetic term is `- 1/4 F_μν F^μν`. We define this and show that it is
Lorentz invariant.

-/

/-- The kinetic energy from an electromagnetic potential. -/
noncomputable def kineticTerm (A : ElectromagneticPotential) : SpaceTime → ℝ := fun x =>
  - 1/4 * {η' 3 | μ μ' ⊗ η' 3 | ν ν' ⊗
    A.toFieldStrength x | μ ν ⊗ A.toFieldStrength  x | μ' ν'}ᵀ.toField

/-!

### D.1. Lorentz invariance of the kinetic term

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

### D.2. Kinetic term equal sum

-/

lemma kineticTerm_eq_sum (A : ElectromagneticPotential) (x : SpaceTime) :
    A.kineticTerm x =
    - 1/4 * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η  μ μ' * η  ν ν' *
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
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν  * ∂_ ν A x μ) := by
  calc _
    _ = - 1/4 * ∑ μ, ∑ ν, ∑ μ', ∑ ν', η  μ μ' * η  ν ν' *
      (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
      * (η μ' μ' * ∂_ μ' A x ν' - η ν' ν' * ∂_ ν' A x μ') := by
      rw [kineticTerm_eq_sum]
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      apply Finset.sum_congr rfl (fun ν' _ => ?_)
      rw [toFieldStrength_basis_repr_apply_eq_single, toFieldStrength_basis_repr_apply_eq_single]
    _ = - 1/4 * ∑ μ, ∑ ν, ∑ μ', η  μ μ' * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ' μ' * ∂_ μ' A x ν - η ν ν * ∂_ ν A x μ') := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      apply Finset.sum_congr rfl (fun μ' _ => ?_)
      rw [Finset.sum_eq_single ν]
      · intro b _ hb
        nth_rewrite 2 [minkowskiMatrix.off_diag_zero]
        simp
        exact id (Ne.symm hb)
      · simp
    _ = - 1/4 * ∑ μ, ∑ ν, η  μ μ * η ν ν *
        (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Finset.sum_eq_single μ]
      · intro b _ hb
        rw [minkowskiMatrix.off_diag_zero]
        simp
        exact id (Ne.symm hb)
      · simp
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ) ^ 2 * η ν ν  * ∂_ μ A x ν - (η ν ν) ^ 2 * η μ μ  * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/4 * ∑ μ, ∑ ν,
        (η ν ν  * ∂_ μ A x ν - η μ μ  * ∂_ ν A x μ)
        * (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) := by simp
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - (η ν ν) ^ 2  * ∂_ μ A x ν  * ∂_ ν A x μ) + (-
        (η μ μ) ^ 2  * ∂_ ν A x μ  *  ∂_ μ A x ν + η μ μ * η ν ν  * (∂_ ν A x μ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1/4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν  * ∂_ ν A x μ) +
        (- ∂_ ν A x μ  *  ∂_ μ A x ν + η μ μ * η ν ν  * (∂_ ν A x μ)^2)) := by  simp
    _ = - 1 / 4 * ∑ μ, ∑ ν,
        ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν  * ∂_ ν A x μ) +
        (- ∂_ μ A x ν  * ∂_ ν A x μ + η ν ν * η μ μ * (∂_ μ A x ν )^2)) := by
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
        (2 * (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν  * ∂_ ν A x μ)) := by
      congr 1
      apply Finset.sum_congr rfl (fun μ _ => ?_)
      apply Finset.sum_congr rfl (fun ν _ => ?_)
      ring
    _ = - 1 / 2 * ∑ μ, ∑ ν,
        (η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν  * ∂_ ν A x μ) := by
      conv_lhs =>
        enter [2, 2, μ]
        rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      ring

/-!

### E.5. The kinetic term in terms of the electric and magnetic fields

-/
open InnerProductSpace

lemma kineticTerm_eq_electric_magnetic (A : ElectromagneticPotential) (t : Time)
    (x : Space)  (hA : Differentiable ℝ A) :
    A.kineticTerm (SpaceTime.toTimeAndSpace.symm (t, x)) =
    1/2 * (‖A.electricField t x‖ ^ 2 - ‖A.magneticField t x‖ ^ 2) := by
  rw [kineticTerm_eq_sum]
  simp
  conv_lhs =>
    enter [2, 2, μ, 2, ν, 2, μ', 2, ν']
    rw [fieldStrengthMatrix_eq_electric_magnetic A t x hA,
      fieldStrengthMatrix_eq_electric_magnetic A t x hA]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq ]
  simp [Fin.sum_univ_three]
  ring

/-!

## F. Variational gradient of the kinetic term

We define the variational gradient of the kinetic term, which is the left-hand side
of Gauss's law and Ampère's law in vacuum.

-/


/-- The variational gradient of the kinetic term of an electromagnetic potential. -/
noncomputable def gradKineticTerm (A : ElectromagneticPotential) : SpaceTime → Lorentz.Vector :=
  (δ (q':=A), ∫ x, kineticTerm q' x)


/-!

### F.1. Variational gradient in terms of fderiv

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
        -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * (fun x' => η μν.1 μν.1 * η μν.2 μν.2 * ψ x') x') x)
              (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
      -(-(fderiv ℝ (fun x' => ψ x' * ∂_ μν.2 A x' μν.1) x) (Lorentz.Vector.basis μν.1) • Lorentz.Vector.basis μν.2 +
          -(fderiv ℝ (fun x' => ∂_ μν.1 A x' μν.2 * ψ x') x) (Lorentz.Vector.basis μν.2) • Lorentz.Vector.basis μν.1))
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
    convert HasVarAdjDerivAt.sum  _ _ A (hA) (fun i => F_hasVarAdjDerivAt i)
    exact Eq.symm (Fintype.sum_prod_type fun x => F x _ _)
  have hF_mul := HasVarAdjDerivAt.const_mul _ _ A F_sum_hasVarAdjDerivAt (c := -1/2)
  change HasVarGradientAt (fun A' x => -1 / 2 * ∑ μ, ∑ ν, F (μ, ν) A' x) _ A
  apply HasVarGradientAt.intro _ hF_mul
  rfl


/-!

### F.2. Writing the variational gradient as a sums over double derivatives of the potential

We rewrite the variational gradient as a simple double sum over
second derivatives of the potential.

-/

lemma gradKineticTerm_eq_sum_sum (A : ElectromagneticPotential) (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
    A.gradKineticTerm x =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν  := by
  have diff_partial (μ) :  ∀ ν,  Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  rw [gradKineticTerm_eq_sum_fderiv A ha]
  calc _
      _ =  ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν  : (Fin 1 ⊕ Fin 3)),
      (- (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2 )  * ∂_ μ A x' ν) x) (Lorentz.Vector.basis μ) •
          Lorentz.Vector.basis ν  +
        -(fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2 ) * ∂_ μ A x' ν  ) x) (Lorentz.Vector.basis μ)
        • Lorentz.Vector.basis ν +
      -(-(fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ ) • Lorentz.Vector.basis ν +
          -(fderiv ℝ (fun x' => -1 / 2  * ∂_ μ A x' ν ) x) (Lorentz.Vector.basis ν) • Lorentz.Vector.basis μ)) := by
        dsimp
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        simp
        ring_nf
      _ =  ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν  : (Fin 1 ⊕ Fin 3)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2 ) * ∂_ μ A x' ν) x) (Lorentz.Vector.basis μ) +
      ((fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ ))) • Lorentz.Vector.basis ν +
        (fderiv ℝ (fun x' => -1 / 2  * ∂_ μ A x' ν ) x) (Lorentz.Vector.basis ν) • Lorentz.Vector.basis μ) := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        rw [neg_add, ← add_assoc, ← neg_smul, ← add_smul]
        congr 1
        · ring_nf
        · simp [← neg_smul]
      _ =  ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν  : (Fin 1 ⊕ Fin 3)),
      ((- 2 * (fderiv ℝ (fun x' => (η μ μ * η ν ν * -1 / 2 ) * ∂_ μ A x' ν) x) (Lorentz.Vector.basis μ) +
      2 * ((fderiv ℝ (fun x' => -1 / 2 * ∂_ ν A x' μ) x) (Lorentz.Vector.basis μ ))) ) • Lorentz.Vector.basis ν := by
        conv_lhs => enter [2, μ]; rw [Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
        conv_lhs => enter [2]; rw [Finset.sum_comm]
        rw [← Finset.sum_add_distrib]
        conv_lhs => enter [2, μ]; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        rw [← add_smul]
        ring_nf
      _ =  ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν  : (Fin 1 ⊕ Fin 3)),
      ((- 2 * ((η μ μ * η ν ν * -1 / 2 ) * ∂_ μ (fun x' =>  ∂_ μ A x' ν) x) +
      2 * (( -1 / 2 *  ∂_ μ (fun x' => ∂_ ν A x' μ) x))) ) • Lorentz.Vector.basis ν := by
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
      _ =  ∑ (μ : (Fin 1 ⊕ Fin 3)), ∑ (ν  : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by
        apply Finset.sum_congr rfl (fun μ _ => ?_)
        apply Finset.sum_congr rfl (fun ν _ => ?_)
        ring_nf
      _ = ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by rw [Finset.sum_comm]

/-!

### F.3. Variational gradient as a sums over fieldStrengthMatrix

We rewrite the variational gradient as a simple double sum over the
fieldStrengthMatrix.

-/

lemma gradKineticTerm_eq_fieldStrength (A : ElectromagneticPotential) (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
      A.gradKineticTerm x =   ∑ (ν  : (Fin 1 ⊕ Fin 3)), η ν ν •
          (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
  have diff_partial (μ) :  ∀ ν,  Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  calc _
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η μ μ * η ν ν * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        ∂_ μ (fun x' => ∂_ ν A x' μ) x) • Lorentz.Vector.basis ν := by
          rw [gradKineticTerm_eq_sum_sum A x ha]
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (η μ μ * ∂_ μ (fun x' => ∂_ μ A x' ν) x -
        η ν ν * ∂_ μ (fun x' => ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          ring_nf
          simp
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν) x -
            ∂_ μ (fun x' => η ν ν *  ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial μ ν
          · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_const_mul]
            rfl
            apply diff_partial ν μ
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (fun x' => η μ μ * ∂_ μ A x' ν -
            η ν ν *  ∂_ ν A x' μ) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq, fderiv_fun_sub]
          simp
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial μ ν
          · conv => enter [2, x]; rw [SpaceTime.deriv_eq]
            apply Differentiable.differentiableAt
            apply Differentiable.const_mul
            exact diff_partial ν μ
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), ∑ (μ : (Fin 1 ⊕ Fin 3)),
        (η ν ν * (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x)) • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          apply Finset.sum_congr rfl (fun μ _ => ?_)
          congr
          funext x
          rw [toFieldStrength_basis_repr_apply_eq_single]
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), (η ν ν *
          ∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [← Finset.sum_smul, Finset.mul_sum]
      _ =  ∑ (ν  : (Fin 1 ⊕ Fin 3)), η ν ν •
          (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x))
          • Lorentz.Vector.basis ν := by
          apply Finset.sum_congr rfl (fun ν _ => ?_)
          rw [smul_smul]

/-!

### F.4. Variational gradient in terms of the Guass's and Ampère laws

We rewrite the variational gradient in terms of the electric and magnetic fields,
explicitly relating it to Gauss's law and Ampère's law.

-/
open Time

lemma eulerLagrangeOp_eq_electric_magnetic(A : ElectromagneticPotential) (x : SpaceTime) (ha : ContDiff ℝ ∞ A) :
      A.gradKineticTerm x =
      Space.div (A.electricField (toTimeAndSpace x).1) (toTimeAndSpace x).2 • Lorentz.Vector.basis (Sum.inl 0) +
    ∑ i, (∂ₜ (fun t => A.electricField t (toTimeAndSpace x).2) (toTimeAndSpace x).1 i-
          Space.curl (A.magneticField (toTimeAndSpace x).1) (toTimeAndSpace x).2 i) •
          Lorentz.Vector.basis (Sum.inr i):= by
  have diff_partial (μ) :  ∀ ν,  Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [← differentiable_pi]
    refine Differentiable.clm_apply ?_ ?_
    · exact differentiable_fderiv _ (ContDiff.of_le ha ENat.LEInfty.out)
    · fun_prop
  have hdiff (μ ν) : Differentiable ℝ fun x => (A.fieldStrengthMatrix x) (μ , ν) := by
    conv => enter [2, x]; rw [ toFieldStrength_basis_repr_apply_eq_single,
      SpaceTime.deriv_eq, SpaceTime.deriv_eq]
    apply Differentiable.sub
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).1 (μ, ν).2
    apply Differentiable.const_mul
    · exact diff_partial (μ, ν).2 (μ, ν).1
  calc _
      _ = ∑ (ν  : (Fin 1 ⊕ Fin 3)), η ν ν •
          (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x)) • Lorentz.Vector.basis ν := by
          rw [gradKineticTerm_eq_fieldStrength A x ha]
  have term_inl_0 : (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inl 0)) x)) =
       (∇ ⬝ A.electricField (toTimeAndSpace x).1) (toTimeAndSpace x).2 := by
      simp [Fintype.sum_sum_type]
      conv_lhs =>
        enter [2, i]
        rw [SpaceTime.deriv_sum_inr _ (hdiff _ _)]
        simp
        enter [2, y]
        rw [fieldStrengthMatrix_eq_electric_magnetic _ _ _ (ha.differentiable (by simp))]
      simp
      rw [Space.div]
      simp [Space.coord]
  have term_inr (i : Fin 3) : (∑ (μ : (Fin 1 ⊕ Fin 3)), (∂_ μ (A.fieldStrengthMatrix · (μ, Sum.inr i)) x)) =
       (-∂ₜ (fun t => A.electricField t (toTimeAndSpace x).2) (toTimeAndSpace x).1 i +
         (∇ × (A.magneticField (toTimeAndSpace x).1)) (toTimeAndSpace x).2 i) := by
      simp [Fintype.sum_sum_type]
      congr
      conv_lhs =>
        rw [SpaceTime.deriv_sum_inl _ (hdiff _ _)]
        simp
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
        simp
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
