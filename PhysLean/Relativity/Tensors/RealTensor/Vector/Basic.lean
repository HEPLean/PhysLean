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

/-!

## B. Defining the tensorial instance

-/

/-!

## B.1. The instance of a module

-/

instance {d} : AddCommMonoid (Vector d) :=
  inferInstanceAs (AddCommMonoid ((Fin 1 ⊕ Fin d)→ ℝ ))

instance {d} : Module ℝ (Vector d) :=
  inferInstanceAs (Module ℝ ((Fin 1 ⊕ Fin d)→ ℝ ))


/-!

## B.2. Equivalence of indexing sets

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

/-!

## B.3. The tensorial instance

-/

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.up] (Vector d) where
  toTensor :=
    (LinearEquiv.piCongrLeft' ℝ _ indexEquiv).symm.trans <|
    (Finsupp.linearEquivFunOnFinite ℝ ℝ
        (ComponentIdx (S := realLorentzTensor d) ![.up])).symm.trans <|
    (Tensor.basis (S := realLorentzTensor d) ![.up]).repr.symm

/-!

## B.4. Basic properties of toTensor

-/

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

## C. Topology and smoothness

-/

/-!

### C.1. Induced instance of a normed space

-/

instance {d : ℕ} : NormedSpace ℝ (Vector d) := Tensorial.normedSpace

/-!

### C.2. Instance of a charted space

-/

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance {d} : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

/-!

### C.3. Structure of a smooth manifold

-/

open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-!

## D. As functions

-/

instance {d} : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v

/-!

### D.1. Relation to EuclideanSpace

-/

lemma apply_eq_toEuclideanSpace {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    v i = (toEuclideanSpace v) (indexEquiv.symm i) := by
  simp [Tensorial.toEuclideanSpace, Tensor.toEuclideanSpace, toTensor]
  erw [LinearEquiv.piCongrLeft'_symm_apply]
  rw [Equiv.piCongrLeft'_symm_apply]
  simp

/-!

### D.2. Linearlity of function application

-/

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl

@[simp]
lemma apply_add {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl

@[simp]
lemma apply_sub {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by
  rw [apply_eq_toEuclideanSpace (v := v - w)]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, PiLp.sub_apply]
  simp [← apply_eq_toEuclideanSpace]

@[simp]
lemma neg_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := by
  rw [apply_eq_toEuclideanSpace (v := -v)]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_neg, PiLp.neg_apply]
  simp [← apply_eq_toEuclideanSpace]

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : Vector d) i = 0 := rfl

/-!

## E. The Basis

We define the basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`.
-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Pi.basisFun ℝ _

/-!

### E.1. Components of the basis vectors

-/

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  erw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

/-!

### E.2. Components of a vector in the basis

-/

lemma basis_repr_apply {d : ℕ} (p : Vector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  erw [Pi.basisFun_repr]

/-!

### E.3. Relation to tensorial basis

-/

lemma basis_eq_tensorial_basis {d : ℕ} :
    basis = (Tensorial.basis (Vector d)).reindex indexEquiv := by
  ext μ
  simp
  rw [Tensorial.basis]
  simp
  rw [Tensor.basis_apply]
  funext i
  rw [toTensor_symm_pure]
  simp [contrBasisFin, Pure.basisVector]
  conv_rhs =>
    enter [1, 2]
    change (contrBasisFin d) (indexEquiv.symm μ 0)
  simp [contrBasisFin, indexEquiv, Finsupp.single_apply]

lemma tensorial_basis_eq_basis {d : ℕ} :
    (Tensorial.basis (Vector d)) = basis.reindex indexEquiv.symm := by
  rw [basis_eq_tensorial_basis]
  ext μ
  simp

/-!

### E.4. Relation to the tensor basis

-/

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.up] (indexEquiv.symm μ) := by
  rw [basis_eq_tensorial_basis]
  simp [Tensorial.toTensor_basis]

lemma toTensor_symm_tensor_basis_eq_basis {d : ℕ}
    (μ : ComponentIdx (S := realLorentzTensor d) ![Color.up]) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up] μ) =
    basis (indexEquiv μ) := by
  apply toTensor.injective
  rw [toTensor_basis_eq_tensor_basis]
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

/-!

### E.5. Maps in terms of the basis

-/

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

/-!

## F. The action of the Lorentz group

The action of the Lorentz group is given to us for free by the `Tensorial` instance.
-/

/-!

### F.1. Components of the action

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

/-!

### F.2. As a matrix multiplication

-/

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • p = Λ.1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

/-!

### F.3. Applying the negative of a Lorentz transformation

-/

lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = - (Λ • p) := by
  funext i
  rw [smul_eq_sum, neg_apply, smul_eq_sum]
  simp

/-!

### F.4. The action is faithful

-/

lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simpa only [smul_eq_mulVec] using fun x => h x

/-!

### F.5. The action on the basis

-/

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

## G. The spatial and time parts

-/

/-!

### G.1. The spatial part

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

### G.2. The time part

-/

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

lemma timeComponent_basis_sum_inr {d : ℕ} (i : Fin d) :
    timeComponent (basis (Sum.inr i)) = 0 := by simp

lemma timeComponent_basis_sum_inl {d : ℕ} :
    timeComponent (d := d) (basis (Sum.inl 0)) = 1 := by simp

end Vector

end Lorentz
