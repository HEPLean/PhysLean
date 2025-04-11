/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
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
open OverColor.Discrete
noncomputable section

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
abbrev Vector (d : ℕ := 3) := ℝT[d, .up]

namespace Vector

open TensorSpecies
open Tensor

set_option quotPrecheck false in

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.up] ≃ Fin 1 ⊕ Fin d :=
  let e : (ComponentIdx (S := (realLorentzTensor d)) ![Color.up])
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
  ((Tensor.basis (S := (realLorentzTensor d)) ![.up]).repr.toEquiv.trans <|
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
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toCoord_injective {d : ℕ} : Function.Injective (@toCoord d) := by
  exact toCoord.toEquiv.injective

instance : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) := ⟨toCoord⟩

lemma toCoord_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.up]) (i : Fin 1 ⊕ Fin d) :
    toCoord p.toTensor i = ((Lorentz.contrBasisFin d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toCoord_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, OverColor.mk_left, Functor.id_obj,
    OverColor.mk_hom, Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  rw [Tensor.basis_repr_pure]
  simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, C_eq_color,
    Finset.prod_singleton, cons_val_zero]
  rfl

lemma basis_repr_apply {d : ℕ} (p : Vector d)
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up]) :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord_apply, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

/-- The Minkowski product of Lorentz vectors in the +--- convention.. -/
def innerProduct {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.toField

@[inherit_doc innerProduct]
notation "⟪" p ", " q "⟫ₘ" => innerProduct p q

lemma innerProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [innerProduct, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue]
  rw [toField_eq_repr]
  rw [contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, x]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply_eq_fin]
    enter [1, 2, y]
    rw [prodT_basis_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue, Fin.succAbove_zero,
    Function.comp_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one, Fin.cast_eq_self,
    Fin.succ_one_eq_two]
  conv_lhs =>
    enter [2, x, 1, 2, y, 1]
    simp only [Fin.isValue]
    change minkowskiMatrix (finSumFinEquiv.symm y) (finSumFinEquiv.symm x)
  conv_lhs =>
    enter [2, x, 2]
    rw [basis_repr_apply]
    enter [3]
    change finSumFinEquiv.symm x
  conv_lhs =>
    enter [2, x, 1, 2, y, 2]
    simp only [Fin.isValue]
    rw [basis_repr_apply]
    enter [3]
    change finSumFinEquiv.symm y
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
  rw [innerProduct, ← actionT_coMetric Λ]
  rw [prodT_equivariant, contrT_equivariant, prodT_equivariant, contrT_equivariant,
    toField_equivariant]
  rfl

instance : FiniteDimensional ℝ (Vector d) := by
  apply FiniteDimensional.of_fintype_basis (Tensor.basis _)

/-!

## Smoothness

-/

section smoothness

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
  NormedAddCommGroup.induced (Vector d) (Fin 1 ⊕ Fin d → ℝ)
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

lemma toCoord_fderiv {d : ℕ} (x : (Vector d)) :
    (fderiv ℝ (@toCoord d) x).toLinearMap = toCoord.toLinearMap := by
  change (fderiv ℝ toCoordContinuous x).toLinearMap = toCoord.toLinearMap
  rw [ContinuousLinearEquiv.fderiv]
  rfl

/-- The coordinates of a Lorentz vector as a linear map. -/
def toCoordFull {d : ℕ} : Vector d ≃ₗ[ℝ]
    (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ) :=
  Equiv.toLinearEquiv
  ((Tensor.basis (S := realLorentzTensor d) ![.up]).repr.toEquiv.trans <|
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

lemma action_apply_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure]
    rw [toCoord_pure]
    conv_lhs =>
      enter [1, 2]
      change Λ.1 *ᵥ (p 0)
    rw [contrBasisFin_repr_apply]
    conv_lhs => simp [indexEquiv]
    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply]
    congr
    funext j
    simp only [Fin.isValue, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, mul_eq_mul_left_iff]
    left
    rw [toCoord_pure, contrBasisFin_repr_apply]
    congr
    simp [indexEquiv]
  · intro r t h
    simp only [actionT_smul, _root_.map_smul, Pi.smul_apply, smul_eq_mul]
    rw [h]
    rw [Finset.mul_sum]
    congr
    funext x
    ring
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, Pi.add_apply, h1, h2]
    rw [← Finset.sum_add_distrib]
    congr
    funext x
    ring

lemma action_toCoord_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    toCoord (Λ • p) = Λ.1 *ᵥ (toCoord p) := by
  funext i
  rw [action_apply_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  fun i => v (Sum.inr i)

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

end Vector

end Lorentz
