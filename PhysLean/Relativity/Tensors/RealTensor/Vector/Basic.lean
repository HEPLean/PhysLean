/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import PhysLean.Relativity.Tensors.Elab
/-!

# Lorentz Vectors

In this module we define Lorentz vectors as real Lorentz tensors with a single up index.
We create an API around Lorentz vectors to make working with them as easy as possible.

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
noncomputable section

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
abbrev Vector (d : ℕ := 3) := ℝT[d, .up]

namespace Vector

open TensorSpecies
open Tensor

/-!

## toCoord

-/

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
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul,
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
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, OverColor.mk_left, Functor.id_obj,
    OverColor.mk_hom, Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  rw [Tensor.basis_repr_pure]
  simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.prod_singleton, cons_val_zero]
  rfl

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Basis.reindex (Tensor.basis (S := realLorentzTensor d) ![Color.up]) indexEquiv

lemma tensor_basis_repr_apply {d : ℕ} (p : Vector d)
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up]) :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord_apply, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

lemma toCoord_tensor_basis_apply {d : ℕ} (μ : Fin (1 + d)) (ν : Fin 1 ⊕ Fin d) :
    toCoord (Tensor.basis (S := realLorentzTensor d) ![Color.up] (fun _ => Fin.cast (by simp) μ)) ν
    = (Finsupp.single (finSumFinEquiv.symm μ) 1) ν := by
  rw [Tensor.basis_apply]
  rw [toCoord_pure]
  simp [contrBasisFin, Pure.basisVector]
  conv_lhs =>
    enter [1, 2]
    change (contrBasisFin d) μ
  simp [contrBasisFin]
  simp [indexEquiv]

lemma basis_repr_eq_toCoord {d : ℕ} :
    basis.repr = toCoord.trans (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin d)).symm := by
  ext p i
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, basis, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, LinearEquiv.trans_apply]
  simp only [indexEquiv, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero,
    Fin.cast_eq_self, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk]
  rfl

lemma basis_repr_apply_eq_toCoord {d : ℕ} (p : Vector d) :
    basis.repr p = toCoord p := by
  rw [basis_repr_eq_toCoord]
  rfl

lemma toMatrix_basis_mulVec_toCoord {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    (LinearMap.toMatrix basis basis f) *ᵥ p.toCoord = (f p).toCoord := by
  rw [← basis_repr_apply_eq_toCoord, LinearMap.toMatrix_mulVec_repr]
  rfl

@[simp]
lemma toCoord_basis {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    toCoord (basis μ) ν = if μ = ν then 1 else 0 := by
  rw [← basis_repr_apply_eq_toCoord]
  simp [Finsupp.single, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

lemma toCoord_map_apply {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    toCoord (f p) = (LinearMap.toMatrix basis basis) f *ᵥ (toCoord p) := by
  rw [← basis_repr_apply_eq_toCoord, ← basis_repr_apply_eq_toCoord]
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

/-!

## The action of the Lorentz group

-/

lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
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
      MulOpposite.unop_op, Nat.succ_eq_add_one, Nat.reduceAdd, mul_eq_mul_left_iff]
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

lemma toCoord_smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    toCoord (Λ • p) = Λ.1 *ᵥ (toCoord p) := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

lemma smul_toCoord_symm_eq_mulVec {d} (Λ : LorentzGroup d) (p : Fin 1 ⊕ Fin d → ℝ) :
    Λ • toCoord.symm p = toCoord.symm (Λ.1 *ᵥ p) := by
  apply toCoord_injective
  rw [toCoord_smul_eq_mulVec]
  simp

lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = -(Λ • p) := by
  obtain ⟨p', rfl⟩ := toCoord.symm.surjective p
  rw [smul_toCoord_symm_eq_mulVec, smul_toCoord_symm_eq_mulVec]
  simp [neg_mulVec]

lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simpa [smul_toCoord_symm_eq_mulVec] using fun x => h (toCoord.symm x)

/-!

## Spatial part

-/

/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  fun i => v (Sum.inr i)

lemma spatialPart_apply_eq_toCoord {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialPart v i = v (Sum.inr i) := rfl

@[simp]
lemma spatialPart_basis_natAdd {d : ℕ} (i : Fin d) (j : Fin d) :
    spatialPart (Tensor.basis (S := realLorentzTensor d) ![Color.up] (fun _ =>
      Fin.cast (by simp) (Fin.natAdd 1 i))) j =
      (Finsupp.single (Sum.inr i : Fin 1 ⊕ Fin d) 1) (Sum.inr j) := by
  rw [spatialPart, toCoord_tensor_basis_apply]
  simp

@[simp]
lemma spatialPart_basis_castAdd {d : ℕ} (i : Fin d) :
    spatialPart (Tensor.basis (S := realLorentzTensor d) ![Color.up] (fun _ =>
      Fin.cast (by simp) (Fin.castAdd d (0 : Fin 1)))) i = 0 := by
  rw [spatialPart, toCoord_tensor_basis_apply]
  simp

/-!

## The time component

-/

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

@[simp]
lemma timeComponent_basis_natAdd {d : ℕ} (i : Fin d) :
    timeComponent (Tensor.basis (S := realLorentzTensor d) ![Color.up] (fun _ =>
      Fin.cast (by simp) (Fin.natAdd 1 i))) = 0 := by
  rw [timeComponent, toCoord_tensor_basis_apply]
  simp

@[simp]
lemma timeComponent_basis_castAdd {d : ℕ} :
    timeComponent (Tensor.basis (S := realLorentzTensor d) ![Color.up] (fun _ =>
      Fin.cast (by simp) (Fin.castAdd d (0 : Fin 1)))) = 1 := by
  rw [timeComponent, toCoord_tensor_basis_apply]
  simp

/-!

## Smoothness

-/

instance : FiniteDimensional ℝ (Vector d) := by
  apply FiniteDimensional.of_fintype_basis (Tensor.basis _)

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
  NormedAddCommGroup.induced (Vector d) (Fin 1 ⊕ Fin d → ℝ)
  (@toCoord d) (toCoord_injective)

instance isNormedSpace (d : ℕ) :
    haveI := isNormedAddCommGroup d
    NormedSpace ℝ (Vector d) :=
  NormedSpace.induced ℝ (Vector d) (Fin 1 ⊕ Fin d → ℝ) (@toCoord d)

open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

/-!

## Smoothness properties of toCoord

-/

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

@[fun_prop]
lemma toCoord_symm_differentiable {d : ℕ} :
    Differentiable ℝ (toCoord.symm : (Fin 1 ⊕ Fin d → ℝ) → Vector d) := by
  change Differentiable ℝ (toCoordContinuous.symm : (Fin 1 ⊕ Fin d → ℝ) → Vector d)
  fun_prop

/-- The coordinates of a Lorentz vector as a linear map. -/
def toCoordFull {d : ℕ} : Vector d ≃ₗ[ℝ]
    (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ) :=
  Equiv.toLinearEquiv
  ((Tensor.basis (S := realLorentzTensor d) ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite)
    {
      map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul,
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

end Vector

end Lorentz
