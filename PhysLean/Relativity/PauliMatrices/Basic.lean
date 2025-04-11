/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Lemmas
import PhysLean.Relativity.PauliMatrices.AsTensor
import PhysLean.Relativity.Tensors.Contraction.Basis
/-!

## Pauli matrices

The Pauli matrices are an invariant complex Lorentz tensor with three indices,
two fermionic and one bosonic.

-/
open IndexNotation
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
noncomputable section

namespace PauliMatrix
open Fermion
open complexLorentzTensor
/-!

## Definitions.

-/
open TensorSpecies
open Tensor

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ^α^{dot β}`. -/
abbrev pauliContr : ℂT[.up, .upL, .upR] := fromConstTriple PauliMatrix.asConsTensor

@[inherit_doc pauliContr]
scoped[PauliMatrix] notation "σ^^^" => PauliMatrix.pauliContr

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
abbrev pauliCo : ℂT[.down, .upL, .upR] :=
  permT id (PermCond.auto) {η' | μ ν ⊗ σ^^^ | ν α β}ᵀ

@[inherit_doc pauliCo]
scoped[PauliMatrix] notation "σ_^^" => PauliMatrix.pauliCo

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_{dot β}_α`. -/
abbrev pauliCoDown : ℂT[.down, .downR, .downL] :=
  permT id (PermCond.auto) {σ_^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ

@[inherit_doc pauliCoDown]
scoped[PauliMatrix] notation "σ___" => PauliMatrix.pauliCoDown

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_{dot β}_α`. -/
abbrev pauliContrDown : ℂT[.up, .downR, .downL] :=
    permT id (PermCond.auto) {pauliContr | μ α β ⊗ εR' | β β' ⊗ εL' | α α'}ᵀ

@[inherit_doc pauliContrDown]
scoped[PauliMatrix] notation "σ^__" => PauliMatrix.pauliContrDown

/-!

## Different forms
-/
open Lorentz
lemma pauliContr_eq_fromConstTriple : σ^^^ = fromConstTriple PauliMatrix.asConsTensor := by
  rfl

lemma pauliContr_eq_fromTripleT : σ^^^ = fromTripleT PauliMatrix.asTensor := by
  rw [pauliContr_eq_fromConstTriple, fromConstTriple]
  erw [PauliMatrix.asConsTensor_apply_one]

lemma pauliContr_eq_basis : pauliContr =
    Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [pauliContr_eq_fromTripleT, PauliMatrix.asTensor_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equivalence.symm_inverse, Fin.isValue, map_sub,
    map_add, _root_.map_smul]
  rw [show complexContrBasis (Sum.inl 0) = complexContrBasisFin4 0 by {simp}]
  rw [show complexContrBasis (Sum.inr 0) = complexContrBasisFin4 1 by {simp}]
  rw [show complexContrBasis (Sum.inr 1) = complexContrBasisFin4 2 by {simp}]
  rw [show complexContrBasis (Sum.inr 2) = complexContrBasisFin4 3 by {simp}]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 1, 1]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 2]
    erw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [2]
    erw [fromTripleT_apply_basis]
  rfl

lemma pauliContr_eq_ofRat : pauliContr = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, -1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, 1⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 3 ∧ b 2 = 3 then ⟨-1, 0⟩ else 0) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliContr_eq_basis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [basis_eq_ofRat]
  simp only [Fin.isValue, map_sub, map_add, _root_.map_smul, Finsupp.coe_sub, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.sub_apply, Pi.add_apply, ofRat_basis_repr_apply, Pi.smul_apply,
    smul_eq_mul, PhysLean.RatComplexNum.I_mul_toComplexNum, mul_ite, ne_eq, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  simp only [Fin.isValue, ← map_add, ← map_sub]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCo_eq_ofRat : pauliCo = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨-1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, 1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, -1⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨-1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCo]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, pauliContr_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCoDown_eq_ofRat : pauliCoDown = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, -1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, 1⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨-1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCoDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, pauliCo_eq_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliContrDown_ofRat : pauliContrDown = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨-1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, 1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, -1⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨-1, 0⟩ else 0) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliContrDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat,ofRat_basis_repr_apply, pauliContr_eq_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-!

## Group actions

-/

/-- The tensor `pauliContr` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliContr (g : SL(2,ℂ)) : g • pauliContr = pauliContr := by
  rw [pauliContr_eq_fromConstTriple]
  rw [actionT_fromConstTriple]

/-- The tensor `pauliCo` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliCo (g : SL(2,ℂ)) : g • pauliCo = pauliCo := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliContr, actionT_coMetric]

/-- The tensor `pauliCoDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliCoDown (g : SL(2,ℂ)) : g • pauliCoDown = pauliCoDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliCo, actionT_altLeftMetric, actionT_altRightMetric]

/-- The tensor `pauliContrDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliContrDown (g : SL(2,ℂ)) : g • pauliContrDown = pauliContrDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliContr, actionT_altLeftMetric, actionT_altRightMetric]

end PauliMatrix
