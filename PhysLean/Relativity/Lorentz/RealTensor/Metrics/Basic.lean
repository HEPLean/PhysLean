/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.PermContr
import PhysLean.Relativity.Lorentz.RealTensor.Basic
/-!

## Metrics as real Lorentz tensors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace realLorentzTensor
open Fermion

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
def coMetric (d : ℕ := 3) := (TensorTree.constTwoNodeE (realLorentzTensor d)
  .down .down (Lorentz.preCoMetric d)).tensor

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
def contrMetric (d : ℕ := 3) := (TensorTree.constTwoNodeE (realLorentzTensor d)
  .up .up (Lorentz.preContrMetric d)).tensor

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `coMetric`. -/
lemma tensorNode_coMetric {d : ℕ} : {η' d | μ ν}ᵀᵀ.tensor =
    (TensorTree.constTwoNodeE (realLorentzTensor d)
    .down .down (Lorentz.preCoMetric d)).tensor := by
  rfl

/-- The definitional tensor node relation for `contrMetric`. -/
lemma tensorNode_contrMetric : {η d | μ ν}ᵀᵀ.tensor =
    (TensorTree.constTwoNodeE (realLorentzTensor d)
    .up .up (Lorentz.preContrMetric d)).tensor := by
  rfl

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
lemma action_coMetric {d : ℕ} (g : LorentzGroup d) : {g •ₐ η' d | μ ν}ᵀᵀ.tensor =
    {η' d | μ ν}ᵀᵀ.tensor := by
  rw [tensorNode_coMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
lemma action_contrMetric (g : LorentzGroup d) : {g •ₐ η d | μ ν}ᵀᵀ.tensor =
    {η d | μ ν}ᵀᵀ.tensor := by
  rw [tensorNode_contrMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-

## There value with respect to a basis

-/

lemma coMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : (j : Fin (Nat.succ 0).succ) →
      Fin ((realLorentzTensor d).repDim (![Color.down, Color.down] j))) :
    ((realLorentzTensor d).tensorBasis _).repr (coMetric d) b =
    minkowskiMatrix (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm (b 1)) := by
  simp [coMetric]
  erw [Lorentz.preCoMetric_apply_one]
  simp [Lorentz.preCoMetricVal]
  erw [Lorentz.coCoToMatrixRe_symm_expand_tmul]
  simp only [map_sum, _root_.map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fin.isValue]
  conv_lhs =>
    enter [2, x, 2, y, 2]
    erw [TensorSpecies.pairIsoSep_tensorBasis_repr]
    change (((Lorentz.coBasisFin d).tensorProduct (Lorentz.coBasisFin d)).repr
        ((Lorentz.coBasis d) x ⊗ₜ[ℝ] (Lorentz.coBasis d) y)) (b 0, b 1)
    simp [Fin.isValue, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, Lorentz.coBasisFin]
    rw [Finsupp.single_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 0))]
  · rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 1))]
    · simp
    · intro y _ hy
      simp only [Fin.isValue, Equiv.apply_symm_apply, ↓reduceIte, mul_one, mul_ite, mul_zero,
        ite_eq_right_iff]
      intro hy2
      rw [← hy2] at hy
      simp at hy
    · simp
  · intro y _ hy
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Fintype.sum_sum_type,
      Finset.univ_unique, Fin.default_eq_zero, finSumFinEquiv_apply_left, Finset.sum_singleton,
      finSumFinEquiv_apply_right, Finset.sum_const_zero, ite_eq_right_iff]
    intro hy2
    rw [← hy2] at hy
    simp at hy
  · simp

lemma contrMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : (j : Fin (Nat.succ 0).succ) → Fin ((realLorentzTensor d).repDim (![.up, .up] j))) :
    ((realLorentzTensor d).tensorBasis _).repr (contrMetric d) b =
    minkowskiMatrix (finSumFinEquiv.symm (b 0)) (finSumFinEquiv.symm (b 1)) := by
  simp [contrMetric]
  erw [Lorentz.preContrMetric_apply_one]
  simp [Lorentz.preContrMetricVal]
  erw [Lorentz.contrContrToMatrixRe_symm_expand_tmul]
  simp only [map_sum, _root_.map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
  Pi.smul_apply, smul_eq_mul, Fin.isValue]
  conv_lhs =>
    enter [2, x, 2, y, 2]
    erw [TensorSpecies.pairIsoSep_tensorBasis_repr]
    change (((Lorentz.contrBasisFin d).tensorProduct (Lorentz.contrBasisFin d)).repr
      ((Lorentz.contrBasis d) x ⊗ₜ[ℝ] (Lorentz.contrBasis d) y)) (b 0, b 1)
    simp [Fin.isValue, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, Lorentz.contrBasisFin]
    rw [Finsupp.single_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 0))]
  · rw [Finset.sum_eq_single (finSumFinEquiv.symm (b 1))]
    · simp
    · intro y _ hy
      simp only [Fin.isValue, Equiv.apply_symm_apply, ↓reduceIte, mul_one, mul_ite, mul_zero,
        ite_eq_right_iff]
      intro hy2
      rw [← hy2] at hy
      simp at hy
    · simp
  · intro y _ hy
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Fintype.sum_sum_type,
      Finset.univ_unique, Fin.default_eq_zero, finSumFinEquiv_apply_left, Finset.sum_singleton,
      finSumFinEquiv_apply_right, Finset.sum_const_zero, ite_eq_right_iff]
    intro hy2
    rw [← hy2] at hy
    simp at hy
  · simp

end realLorentzTensor
