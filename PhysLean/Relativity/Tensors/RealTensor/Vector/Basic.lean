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
open Module IndexNotation
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
def Vector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

namespace Vector

open TensorSpecies
open Tensor

instance {d} : AddCommMonoid (Vector d) :=
  inferInstanceAs (AddCommMonoid (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

instance {d} : Module ℝ (Vector d) :=
  inferInstanceAs (Module ℝ (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

instance {d} : AddCommGroup (Vector d) :=
  inferInstanceAs (AddCommGroup (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

instance {d} : FiniteDimensional ℝ (Vector d) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 1 ⊕ Fin d → ℝ))

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

instance isNormedSpace (d : ℕ) :
    NormedSpace ℝ (Vector d) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

instance {d} : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl

@[simp]
lemma apply_add {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl

@[simp]
lemma apply_sub {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by rfl

@[simp]
lemma neg_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : Vector d) i = 0 := rfl
/-!

## Tensorial

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

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.up] (Vector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul]
        rfl}

open Tensorial

lemma toTensor_symm_apply {d : ℕ} (p : ℝT[d, .up]) :
    (toTensor (self := tensorial)).symm p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.up]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.contrBasisFin d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toTensor_symm_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  rw [Tensor.basis_repr_pure]
  simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.prod_singleton, cons_val_zero]
  rfl

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Pi.basisFun ℝ _

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  erw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up] (indexEquiv.symm μ)) =
    basis μ := by
  rw [Tensor.basis_apply]
  funext i
  rw [toTensor_symm_pure]
  simp [contrBasisFin, Pure.basisVector]
  conv_lhs =>
    enter [1, 2]
    change (contrBasisFin d) (indexEquiv.symm μ 0)
  simp [contrBasisFin, indexEquiv, Finsupp.single_apply]

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.up] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp

lemma basis_eq_map_tensor_basis : basis =
    ((Tensor.basis (S := realLorentzTensor) ![Color.up]).map toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp

lemma tensor_basis_map_eq_basis_reindex :
    (Tensor.basis (S := realLorentzTensor) ![Color.up]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp

lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : Vector d) (μ : ComponentIdx ![Color.up]) :
    (Tensor.basis ![Color.up]).repr (toTensor p) μ =
    p (indexEquiv μ) := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply]
  apply induction_on_pure (t := p)
  · intro p
    rw [Tensor.basis_repr_pure]
    simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.prod_singleton, cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [toTensor_symm_pure]
    simp
    rfl
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]

lemma basis_repr_apply {d : ℕ} (p : Vector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  erw [Pi.basisFun_repr]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

/-!

## The action of the Lorentz group

-/

lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure]
    rw [toTensor_symm_pure]
    conv_lhs =>
      enter [1, 2]
      change Λ.1 *ᵥ (p 0)
    rw [contrBasisFin_repr_apply]
    conv_lhs => simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, indexEquiv,
      cons_val_zero, Fin.cast_eq_self, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, ContrMod.mulVec_val]
    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply]
    congr
    funext j
    simp only [Fin.isValue, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Nat.succ_eq_add_one, Nat.reduceAdd, mul_eq_mul_left_iff]
    left
    rw [toTensor_symm_pure, contrBasisFin_repr_apply]
    congr
    simp [indexEquiv]
  · intro r t h
    simp only [actionT_smul, _root_.map_smul]
    change r * toTensor (self := tensorial).symm (Λ • t) i = _
    rw [h]
    rw [Finset.mul_sum]
    congr
    funext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, apply_smul]
    ring
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, h1, h2, apply_add]
    rw [← Finset.sum_add_distrib]
    congr
    funext x
    ring

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • p = Λ.1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp

@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]

lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : Vector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]

lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]

lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = - (Λ • p) := by
  funext i
  rw [smul_eq_sum, neg_apply, smul_eq_sum]
  simp

lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simpa only [smul_eq_mulVec] using fun x => h x

/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    Vector d →L[ℝ] Vector d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Λ • v
      map_add' := smul_add Λ
      map_smul' := fun c v => by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, RingHom.id_apply]
        funext i
        simp [smul_eq_sum]
        ring_nf
        congr
        rw [Finset.mul_sum]
        congr
        funext j
        ring}

lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    actionCLM Λ p = Λ • p := rfl

lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ.1 ν μ • basis ν := by
  funext i
  rw [smul_eq_sum]
  simp only [basis_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  trans ∑ ν, ((Λ.1 ν μ • basis ν) i)
  · simp
  rw [Fintype.sum_apply]

/-!

## Spatial part

-/

/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  fun i => v (Sum.inr i)

lemma spatialPart_apply_eq_toCoord {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialPart v i = v (Sum.inr i) := rfl

lemma spatialPart_basis_sum_inr {d : ℕ} (i : Fin d) (j : Fin d) :
    spatialPart (basis (Sum.inr i)) j =
      (Finsupp.single (Sum.inr i : Fin 1 ⊕ Fin d) 1) (Sum.inr j) := by
  simp [spatialPart, basis_apply]
  rw [Finsupp.single_apply]
  simp

lemma spatialPart_basis_sum_inl {d : ℕ} (i : Fin d) :
    spatialPart (basis (Sum.inl 0)) i = 0 := by simp

/-!

## The time component

-/

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

lemma timeComponent_basis_sum_inr {d : ℕ} (i : Fin d) :
    timeComponent (basis (Sum.inr i)) = 0 := by simp

lemma timeComponent_basis_sum_inl {d : ℕ} :
    timeComponent (d := d) (basis (Sum.inl 0)) = 1 := by simp
/-!

## Smoothness

-/

open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

end Vector

end Lorentz
