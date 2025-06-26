/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import PhysLean.Relativity.Tensors.Elab
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

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Basis.reindex (Tensor.basis (S := realLorentzTensor d) ![Color.up]) indexEquiv

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

lemma tensor_basis_repr_apply {d : ℕ} (p : Vector d)
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up]) :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord_apply, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

lemma basis_repr_eq_toCoord {d : ℕ} :
    basis.repr = toCoord.trans (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin d)).symm := by
  ext p i
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, basis, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, LinearEquiv.trans_apply]
  simp only [indexEquiv, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue, cons_val_zero,
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

# The minkowskiProduct

-/

/-- The Minkowski product of Lorentz vectors in the +--- convention.. -/
def minkowskiProductMap {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.toField

lemma minkowskiProductMap_toCoord {d : ℕ} (p q : Vector d) :
    minkowskiProductMap p q = p (Sum.inl 0) * q (Sum.inl 0) -
    ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [minkowskiProductMap, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue]
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
    rw [tensor_basis_repr_apply]
    enter [3]
    change finSumFinEquiv.symm x
  conv_lhs =>
    enter [2, x, 1, 2, y, 2]
    simp only [Fin.isValue]
    rw [tensor_basis_repr_apply]
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

lemma minkowskiProductMap_symm {d : ℕ} (p q : Vector d) :
    minkowskiProductMap p q = minkowskiProductMap q p := by
  rw [minkowskiProductMap_toCoord, minkowskiProductMap_toCoord]
  congr 1
  · ring
  · congr
    funext i
    ring

@[simp]
lemma minkowskiProductMap_add_fst {d : ℕ} (p q r : Vector d) :
    minkowskiProductMap (p + q) r = minkowskiProductMap p r + minkowskiProductMap q r := by
  rw [minkowskiProductMap_toCoord, minkowskiProductMap_toCoord, minkowskiProductMap_toCoord]
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, Pi.add_apply]
  conv_lhs =>
    enter [2, 2, x]
    simp [add_mul]
  rw [Finset.sum_add_distrib]
  ring

@[simp]
lemma minkowskiProductMap_add_snd {d : ℕ} (p q r : Vector d) :
    minkowskiProductMap p (q + r) = minkowskiProductMap p q + minkowskiProductMap p r := by
  rw [minkowskiProductMap_symm, minkowskiProductMap_add_fst]
  congr 1
  · exact minkowskiProductMap_symm q p
  · exact minkowskiProductMap_symm r p

@[simp]
lemma minkowskiProductMap_smul_fst {d : ℕ} (c : ℝ) (p q : Vector d) :
    minkowskiProductMap (c • p) q = c * minkowskiProductMap p q := by
  rw [minkowskiProductMap_toCoord, minkowskiProductMap_toCoord]
  rw [mul_sub]
  congr 1
  · simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_smul,
    Pi.smul_apply, smul_eq_mul]
    ring
  · rw [Finset.mul_sum]
    congr
    funext i
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

@[simp]
lemma minkowskiProductMap_smul_snd {d : ℕ} (c : ℝ) (p q : Vector d) :
    minkowskiProductMap p (c • q) = c * minkowskiProductMap p q := by
  rw [minkowskiProductMap_symm, minkowskiProductMap_smul_fst]
  congr 1
  exact minkowskiProductMap_symm q p

/-- The Minkowski product of two Lorentz vectors as a linear map. -/
def minkowskiProduct {d : ℕ} : Vector d →ₗ[ℝ] Vector d →ₗ[ℝ] ℝ where
  toFun p := {
    toFun := fun q => minkowskiProductMap p q
    map_add' := fun q r => by
      simp
    map_smul' := fun c q => by
      simp [minkowskiProductMap_smul_fst c p q]
  }
  map_add' := fun p r => by
    apply LinearMap.ext
    intro x
    simp
  map_smul' := fun c p => by
    apply LinearMap.ext
    intro x
    simp

@[inherit_doc minkowskiProduct]
scoped notation "⟪" p ", " q "⟫ₘ" => minkowskiProduct p q

lemma minkowskiProduct_apply {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = minkowskiProductMap p q := rfl

lemma minkowskiProduct_symm {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = ⟪q, p⟫ₘ := by
  rw [minkowskiProduct_apply, minkowskiProductMap_symm]
  rfl

lemma minkowskiProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  rw [minkowskiProduct_apply, minkowskiProductMap_toCoord]

lemma minkowskiProduct_toCoord_minkowskiMatrix {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = ∑ μ, minkowskiMatrix μ μ * (toCoord p μ) * (toCoord q μ) := by
  rw [minkowskiProduct_toCoord]
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0,
    one_mul, minkowskiMatrix.inr_i_inr_i, neg_mul, Finset.sum_neg_distrib]
  rfl

@[simp]
lemma minkowskiProduct_invariant {d : ℕ} (p q : Vector d) (Λ : LorentzGroup d) :
    ⟪Λ • p, Λ • q⟫ₘ = ⟪p, q⟫ₘ := by
  rw [minkowskiProduct_apply, minkowskiProductMap, ← actionT_coMetric Λ]
  rw [prodT_equivariant, contrT_equivariant, prodT_equivariant, contrT_equivariant,
    toField_equivariant]
  rfl

open InnerProductSpace in
lemma minkowskiProduct_eq_timeComponent_spatialPart {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p.timeComponent * q.timeComponent -
      ⟪p.spatialPart, q.spatialPart⟫_ℝ := by
  rw [minkowskiProduct_toCoord]
  congr
  funext i
  simp [spatialPart_apply_eq_toCoord]
  ring

lemma minkowskiProduct_self_eq_timeComponent_spatialPart {d : ℕ} (p : Vector d) :
    ⟪p, p⟫ₘ = ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  congr 1
  · rw [@RCLike.norm_sq_eq_def_ax]
    simp
  · exact real_inner_self_eq_norm_sq p.spatialPart

@[simp]
lemma minkowskiProduct_basis_left {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Vector d) :
    ⟪basis μ, p⟫ₘ = minkowskiMatrix μ μ * toCoord p μ := by
  rw [minkowskiProduct_toCoord_minkowskiMatrix]
  simp

@[simp]
lemma minkowskiProduct_basis_right {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Vector d) :
    ⟪p, basis μ⟫ₘ = minkowskiMatrix μ μ * toCoord p μ := by
  rw [minkowskiProduct_symm, minkowskiProduct_basis_left]

@[simp]
lemma minkowskiProduct_eq_zero_forall_iff {d : ℕ} (p : Vector d) :
    (∀ q : Vector d, ⟪p, q⟫ₘ = 0) ↔ p = 0 := by
  constructor
  · intro h
    apply toCoord_injective
    ext μ
    rw [← minkowskiMatrix.mul_η_diag_eq_iff (μ := μ)]
    rw [← minkowskiProduct_basis_right, h (basis μ)]
    simp
  · intro h
    subst h
    simp

lemma map_minkowskiProduct_eq_self_forall_iff {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    (∀ p q : Vector d, ⟪f p, q⟫ₘ = ⟪p, q⟫ₘ) ↔ f = LinearMap.id := by
  constructor
  · intro h
    ext p
    have h1 := h p
    have h2 : ∀ q, ⟪f p - p, q⟫ₘ = 0 := by
      intro q
      simp [h1 q]
    rw [minkowskiProduct_eq_zero_forall_iff] at h2
    simp
    rw [sub_eq_zero] at h2
    exact h2
  · intro h
    subst h
    simp

/-!

## The adjoint of a linear map

-/

/-- The adjoint of a linear map from `Vector d` to itself with respect to
  the `minkowskiProduct`. -/
def adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) : Vector d →ₗ[ℝ] Vector d :=
  (LinearMap.toMatrix Vector.basis Vector.basis).symm <|
  minkowskiMatrix.dual <|
  LinearMap.toMatrix Vector.basis Vector.basis f

lemma map_minkowskiProduct_eq_adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p q : Vector d) :
    ⟪f p, q⟫ₘ = ⟪p, adjoint f q⟫ₘ := by
  rw [minkowskiProduct_toCoord_minkowskiMatrix, minkowskiProduct_toCoord_minkowskiMatrix]
  simp only [toCoord_map_apply]
  conv_rhs =>
    enter [2, x]
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, adjoint, LinearMap.toMatrix_symm,
      LinearMap.toMatrix_toLin, mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
      transpose_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    enter [2, y]
    rw [minkowskiMatrix.dual_apply]
    ring_nf
    simp
  conv_lhs =>
    enter [2, x]
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, mulVec_eq_sum, op_smul_eq_smul,
      Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

lemma minkowskiProduct_map_eq_adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p q : Vector d) :
    ⟪p, f q⟫ₘ = ⟪adjoint f p, q⟫ₘ := by
  rw [minkowskiProduct_symm, map_minkowskiProduct_eq_adjoint f q p,
    minkowskiProduct_symm]

/-- A linear map `Vector d →ₗ[ℝ] Vector d` satsfies `IsLorentz` if it preserves
  the minkowski product. -/
def IsLorentz {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    Prop := ∀ p q : Vector d, ⟪f p, f q⟫ₘ = ⟪p, q⟫ₘ

lemma isLorentz_iff {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ ∀ p q : Vector d, ⟪f p, f q⟫ₘ = ⟪p, q⟫ₘ := by
  rfl

lemma isLorentz_iff_basis {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ ∀ μ ν : Fin 1 ⊕ Fin d, ⟪f (basis μ), f (basis ν)⟫ₘ = ⟪basis μ, basis ν⟫ₘ := by
  rw [isLorentz_iff]
  constructor
  · exact fun a μ ν => a (basis μ) (basis ν)
  intro h p q
  have hp : p = ∑ μ, toCoord p μ • basis μ := by
    rw [← basis_repr_apply_eq_toCoord]
    exact Eq.symm (Basis.sum_repr basis p)
  have hq : q = ∑ ν, toCoord q ν • basis ν := by
    rw [← basis_repr_apply_eq_toCoord]
    exact Eq.symm (Basis.sum_repr basis q)
  generalize toCoord p = fp at hp
  generalize toCoord q = fq at hq
  subst hp hq
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, map_sum, map_smul, LinearMap.coeFn_sum,
    Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, minkowskiProduct_basis_left, toCoord_basis,
    mul_ite, mul_one, mul_zero, h]

lemma isLorentz_iff_comp_adjoint_eq_id {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ adjoint f ∘ₗ f = LinearMap.id := by
  rw [isLorentz_iff]
  conv_lhs =>
    enter [p, q]
    rw [minkowskiProduct_map_eq_adjoint]
  change (∀ (p q : Vector d), (minkowskiProduct ((adjoint f ∘ₗ f) p)) q =
    (minkowskiProduct p) q) ↔ _
  rw [map_minkowskiProduct_eq_self_forall_iff]

lemma isLorentz_iff_toMatrix_mem_lorentzGroup {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ LinearMap.toMatrix Vector.basis Vector.basis f ∈ LorentzGroup d := by
  rw [isLorentz_iff_comp_adjoint_eq_id]
  rw [LorentzGroup.mem_iff_dual_mul_self]
  trans LinearMap.toMatrix Vector.basis Vector.basis (adjoint f ∘ₗ f) =
    LinearMap.toMatrix Vector.basis Vector.basis (LinearMap.id : Vector d →ₗ[ℝ] Vector d)
  · exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (LinearMap.toMatrix basis basis))
  simp
  rw [LinearMap.toMatrix_comp Vector.basis Vector.basis]
  simp [adjoint]

end Vector

end Lorentz
