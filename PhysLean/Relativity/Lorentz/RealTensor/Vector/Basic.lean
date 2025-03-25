/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
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

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
abbrev Vector (d : ℕ := 3) := ℝT[d, .up]

namespace Vector

set_option quotPrecheck false in
/-- The actoin of the Lorentz group on a Lorentz vector. -/
scoped infixl:60 "•" => ((realLorentzTensor _).F.obj (OverColor.mk ![Color.up])).ρ

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin 1 ⊕ Fin d :=
  let e :((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin (1 + d) := {
    toFun := fun f => Fin.cast (by rfl) (f 0)
    invFun := fun x => (fun j => Fin.cast (by simp) x)
    left_inv := fun f => by
      ext j
      fin_cases j
      simp
    right_inv := fun x => by rfl}
  e.trans finSumFinEquiv.symm

/-- The coordinates of a Lorentz vector as a linear map. -/
def toCoord {d : ℕ} : Vector d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) := Equiv.toLinearEquiv
  (((realLorentzTensor d).tensorBasis ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    {
      map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, _root_.map_smul,
          RingHom.id_apply]
        rfl
    }

lemma toCoord_apply {d : ℕ} (p : Vector d) : toCoord p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    ((realLorentzTensor d).tensorBasis _).repr p) := rfl

lemma toCoord_injective {d : ℕ} : Function.Injective (@toCoord d) := by
  exact toCoord.toEquiv.injective

instance : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) := ⟨toCoord⟩

lemma toCoord_tprod {d : ℕ} (p : (i : Fin 1) →
    ↑((realLorentzTensor d).FD.obj { as := ![Color.up] i }).V) (i : Fin 1 ⊕ Fin d) :
    toCoord (PiTensorProduct.tprod ℝ p) i =
      ((Lorentz.contrBasisFin d).repr (p 0))
      (indexEquiv.symm i 0) := by
  rw [toCoord_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, OverColor.mk_left, Functor.id_obj,
    OverColor.mk_hom, Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  erw [TensorSpecies.TensorBasis.tensorBasis_repr_tprod]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, C_eq_color,
    Finset.prod_singleton, cons_val_zero]
  rfl

lemma tensorNode_repr_apply {d : ℕ} (p : Vector d)
    (b : (j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) :
    ((realLorentzTensor d).tensorBasis _).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord_apply, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

/-- The Minkowski product of Lorentz vectors in the +--- convention.. -/
def innerProduct {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.field

@[inherit_doc innerProduct]
notation "⟪" p ", " q "⟫ₘ" => innerProduct p q

open TensorTree
lemma innerProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [innerProduct, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue]
  rw [TensorTree.field_eq_repr]
  rw [contr_tensorBasis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, x]
    rw [prod_tensorBasis_repr_apply]
    rw [contr_tensorBasis_repr_apply_eq_fin]
    rw [tensorNode_repr_apply]
    enter [1, 2, y]
    rw [prod_tensorBasis_repr_apply]
    rw [tensorNode_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue, Fin.succAbove_zero,
    Function.comp_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one, Fin.cast_eq_self,
    Fin.succ_one_eq_two, tensorNode_tensor]
  conv_lhs =>
    enter [2, x, 2, 3]
    simp only [Fin.isValue]
    change finSumFinEquiv.symm x
  conv_lhs =>
    enter [2, x, 1, 2, y, 2, 3]
    change finSumFinEquiv.symm y
  conv_lhs =>
    enter [2, x, 1, 2, y, 1]
    simp only [Fin.isValue]
    change minkowskiMatrix (finSumFinEquiv.symm y) (finSumFinEquiv.symm x)
  conv_lhs =>
    enter [2, x, 1]
    rw [← finSumFinEquiv.sum_comp]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true,
    minkowskiMatrix.off_diag_zero, zero_mul, Finset.sum_const_zero, _root_.add_zero,
    _root_.zero_add]
  congr 1
  rw [minkowskiMatrix.inl_0_inl_0]
  simp only [Fin.isValue, one_mul]
  rw [← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · rw [minkowskiMatrix.inr_i_inr_i]
    simp
  · intro y _ hy
    rw [minkowskiMatrix.off_diag_zero (by simp [hy])]
    simp
  · simp

@[simp]
lemma innerProduct_zero_left {d : ℕ} (q : Vector d) :
    ⟪0, q⟫ₘ = 0 := by
  rw [innerProduct_toCoord]
  simp [toCoord]

@[simp]
lemma innerProduct_zero_right {d : ℕ} (p : Vector d) :
    ⟪p, 0⟫ₘ = 0 := by
  rw [innerProduct_toCoord]
  simp [toCoord]

@[simp]
lemma innerProduct_invariant {d : ℕ} (p q : Vector d) (Λ : LorentzGroup d) :
    ⟪Λ • p, Λ • q⟫ₘ = ⟪p, q⟫ₘ := by
  rw [innerProduct]
  have h1 (q : Vector d) :
    (tensorNode (Λ • q)).tensor
    = (action Λ (tensorNode q)).tensor := by simp [action_tensor]
  rw [field]
  rw [contr_tensor_eq <| prod_tensor_eq_snd <| h1 q]
  rw [contr_tensor_eq <| prod_tensor_eq_fst
    <| contr_tensor_eq <| prod_tensor_eq_snd <| h1 p]
  have h2 : (tensorNode (realLorentzTensor.coMetric d)).tensor
      = (action Λ (tensorNode (realLorentzTensor.coMetric d))).tensor := by
    rw [action_coMetric]
  rw [contr_tensor_eq <| prod_tensor_eq_fst
    <| contr_tensor_eq <| prod_tensor_eq_fst <| h2]
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <|
    prod_action _ _ _]
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_action _ _]
  rw [contr_tensor_eq <| prod_action _ _ _]
  rw [contr_action _]
  rw [← field]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue, Fin.succAbove_zero,
    action_field]
  rw [innerProduct]

instance : FiniteDimensional ℝ (Vector d) := by
  apply FiniteDimensional.of_fintype_basis ((realLorentzTensor d).tensorBasis _)

/-!

## Smoothness

-/

section smoothness

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
  NormedAddCommGroup.induced ↑(Vector d).V (Fin 1 ⊕ Fin d → ℝ)
  (@toCoord d) (toCoord_injective)

instance isNormedSpace (d : ℕ) :
    haveI := isNormedAddCommGroup d
    NormedSpace ℝ (Vector d) :=
  NormedSpace.induced ℝ (Vector d) (Fin 1 ⊕ Fin d → ℝ) (@toCoord d)

/-- The `toCoord` map as a `ContinuousLinearEquiv`. -/
def toCoordContinuous {d : ℕ} : Vector d ≃L[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv toCoord

@[fun_prop]
lemma toCoord_differentiable {d : ℕ} :
    Differentiable ℝ (@toCoord d) := by
  exact toCoordContinuous.differentiable

lemma toCoord_fderiv {d : ℕ} (x : ↑(Vector d).V) :
    (fderiv ℝ (@toCoord d) x).toLinearMap = toCoord.toLinearMap := by
  change (fderiv ℝ toCoordContinuous x).toLinearMap = toCoord.toLinearMap
  rw [ContinuousLinearEquiv.fderiv]
  rfl

/-- The coordinates of a Lorentz vector as a linear map. -/
def toCoordFull {d : ℕ} : Vector d ≃ₗ[ℝ]
    (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ) :=
  Equiv.toLinearEquiv
  (((realLorentzTensor d).tensorBasis ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite)
    {
      map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, _root_.map_smul,
          RingHom.id_apply]
        rfl
    }

lemma toCoord_apply_eq_toCoordFull_apply {d : ℕ} (p : Vector d) :
    toCoord p = (Equiv.piCongrLeft' _ indexEquiv) (toCoordFull p) := by
  rfl

/-- The `toCoordFull` map as a `ContinuousLinearEquiv`. -/
def fromCoordFullContinuous {d : ℕ} :
    (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ) ≃L[ℝ]
    Vector d :=
  LinearEquiv.toContinuousLinearEquiv toCoordFull.symm

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

end smoothness

/-!

## The Lorentz action

-/

lemma action_apply_eq_sum (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  revert p
  refine fun p ↦
    PiTensorProduct.induction_on' p ?_ (by
    intro a b hx hy
    simp at hx hy ⊢
    rw [hx, hy]
    simp [mul_add, Finset.sum_add_distrib]
    ring)
  intro r p
  simp only [TensorSpecies.F_def, Nat.reduceAdd, OverColor.mk_left,
    Functor.id_obj, OverColor.mk_hom, PiTensorProduct.tprodCoeff_eq_smul_tprod, _root_.map_smul,
    Pi.smul_apply, smul_eq_mul]
  conv_lhs =>
    enter [2, 2]
    simp only [C_eq_color, OverColor.lift, OverColor.lift.obj', LaxBraidedFunctor.of_toFunctor,
      Nat.succ_eq_add_one, Nat.reduceAdd]
    /- I beleive this erw is needed becuase of (realLorentzTensor d).G and
      LorentzGroup d are different. -/
    erw [OverColor.lift.objObj'_ρ_tprod]
  conv_rhs =>
    enter [2, x]
    rw [← mul_assoc, mul_comm _ r, mul_assoc]
  rw [← Finset.mul_sum]
  congr
  simp_all only [Nat.succ_eq_add_one, OverColor.mk_left, _root_.zero_add, Functor.id_obj,
    C_eq_color, OverColor.mk_hom]
  erw [toCoord_tprod]
  change ((contrBasisFin d).repr (Λ *ᵥ _)) _ = _
  rw [contrBasisFin_repr_apply]
  rw [ContrMod.mulVec_val]
  rw [mulVec_eq_sum]
  simp only [Fin.isValue, op_smul_eq_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Finset.sum_apply,
    Pi.smul_apply, transpose_apply, smul_eq_mul]
  congr
  funext j
  rw [mul_comm]
  congr
  · match i with
    | Sum.inl 0 => rfl
    | Sum.inr i => simp [finSumFinEquiv, indexEquiv]
  · erw [toCoord_tprod]
    rw [contrBasisFin_repr_apply]
    congr
    match j with
    | Sum.inl 0 => rfl
    | Sum.inr j => simp [finSumFinEquiv, indexEquiv]

lemma action_toCoord_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    toCoord (Λ • p) = Λ.1 *ᵥ (toCoord p) := by
  funext i
  rw [action_apply_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

end Vector

end Lorentz
