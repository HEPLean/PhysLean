/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Basic
/-!

# Tensors associated with a tensor species

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

namespace Tensor

variable {k G : Type} [CommRing k] [Group G]
  {S : TensorSpecies k G} {n n' n2 : ℕ} {c : Fin n → S.C} {c' : Fin n' → S.C}
  {c2 : Fin n2 → S.C}

/-!

## Product

And its interaction with
- actions
- permutations

-/

TODO "6VZ3N" "Change products of tensors to use `Fin.append` rather then
  `Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm`."

/-- The equivalence between `ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)` and
  `Π (i : Fin n1 ⊕ Fin n2), Fin (S.repDim (Sum.elim c c1 i))`. -/
def ComponentIdx.prodEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) ≃
    Π (i : Fin n1 ⊕ Fin n2), Fin (S.repDim (Sum.elim c c1 i)) :=
  (Equiv.piCongr finSumFinEquiv (fun _ => finCongr (by simp))).symm

/-- The product of two component indices. -/
def ComponentIdx.prod {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (b : ComponentIdx c) (b1 : ComponentIdx c1) :
    ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) :=
  ComponentIdx.prodEquiv.symm fun | Sum.inl i => b i | Sum.inr i => b1 i

lemma ComponentIdx.prod_apply_finSumFinEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (b : ComponentIdx c) (b1 : ComponentIdx c1) (i : Fin n1 ⊕ Fin n2) :
    ComponentIdx.prod b b1 (finSumFinEquiv i) =
    match i with
    | Sum.inl i => Fin.cast (by simp) (b i)
    | Sum.inr i => Fin.cast (by simp) (b1 i) := by
  rw [ComponentIdx.prod]
  rw [prodEquiv]
  simp only [Equiv.symm_symm]
  rw [Equiv.piCongr_apply_apply]
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

/-- The equivalence between `ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)` and
  `ComponentIdx c × ComponentIdx c1` formed by products. -/
def ComponentIdx.splitEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) ≃ ComponentIdx c × ComponentIdx c1 where
  toFun p := (fun i => (prodEquiv p) (Sum.inl i), fun i => (prodEquiv p) (Sum.inr i))
  invFun p := ComponentIdx.prod (p.1) (p.2)
  left_inv p := by
    simp only
    funext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rw [prod_apply_finSumFinEquiv]
    match i with
    | Sum.inl i =>
      rfl
    | Sum.inr i =>
      rfl
  right_inv p := by
    ext i
    simp only
    · rw [prodEquiv]
      rw [Equiv.piCongr_symm_apply]
      simp only [Function.comp_apply, Sum.elim_inl, finCongr_symm,
        finCongr_apply, Fin.coe_cast]
      rw [prod_apply_finSumFinEquiv]
      rfl
    · rw [prodEquiv]
      simp only [Function.comp_apply]
      erw [Equiv.piCongr_symm_apply]
      simp only [Function.comp_apply, Sum.elim_inr, finCongr_symm,
        finCongr_apply, Fin.coe_cast]
      rw [prod_apply_finSumFinEquiv]
      rfl

/-- The equivalence between pure tensors based on a product of lists of indices, and
  the type `Π (i : Fin n1 ⊕ Fin n2), S.FD.obj (Discrete.mk ((Sum.elim c c1) i))`. -/
def Pure.prodEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) ≃
    Π (i : Fin n1 ⊕ Fin n2), S.FD.obj (Discrete.mk ((Sum.elim c c1) i)) :=
  (Equiv.piCongr finSumFinEquiv
  (fun _ => ((Action.forget _ _).mapIso
    (S.FD.mapIso (Discrete.eqToIso (by simp)))).toLinearEquiv.toEquiv)).symm

/-- Given two pure tensors `p1 : Pure S c` and `p2 : Pure S c`, `prodP p p2` is the tensor
  product of those tensors returning an element in
  `Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)`. -/
def Pure.prodP {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p1 : Pure S c) (p2 : Pure S c1) : Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) :=
  Pure.prodEquiv.symm fun | Sum.inl i => p1 i | Sum.inr i => p2 i

lemma Pure.prodP_apply_finSumFinEquiv {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1 ⊕ Fin n2) :
    Pure.prodP p1 p2 (finSumFinEquiv i) =
    match i with
    | Sum.inl i => S.FD.map (eqToHom (by simp)) (p1 i)
    | Sum.inr i => S.FD.map (eqToHom (by simp)) (p2 i) := by
  rw [Pure.prodP]
  rw [prodEquiv]
  simp only [Equiv.symm_symm]
  rw [Equiv.piCongr_apply_apply]
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

@[simp]
lemma Pure.prodP_apply_castAdd {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1) :
    Pure.prodP p1 p2 (Fin.castAdd n2 i) =
    S.FD.map (eqToHom (by simp)) (p1 i) := by
  trans Pure.prodP p1 p2 (finSumFinEquiv (Sum.inl i))
  · rfl
  rw [Pure.prodP_apply_finSumFinEquiv]
  simp

@[simp]
lemma Pure.prodP_apply_natAdd {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) :
    Pure.prodP p1 p2 (Fin.natAdd n1 i) =
    S.FD.map (eqToHom (by simp)) (p2 i) := by
  trans Pure.prodP p1 p2 (finSumFinEquiv (Sum.inr i))
  · rfl
  rw [Pure.prodP_apply_finSumFinEquiv]
  simp

lemma Pure.prodP_basisVector {n n1 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C}
    (b : ComponentIdx c) (b1 : ComponentIdx c1) :
    Pure.prodP (Pure.basisVector c b) (Pure.basisVector c1 b1) =
    Pure.basisVector _ (b.prod b1) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Pure.prodP_apply_finSumFinEquiv]
  have basis_congr {c1 c2 : S.C} (h : c1 = c2) (x : Fin (S.repDim c1))
    (y : Fin (S.repDim c2)) (hxy : y = Fin.cast (by simp [h]) x) :
      S.FD.map (eqToHom (by simp [h])) ((S.basis c1) x) =
      (S.basis c2) y := by
    subst h hxy
    simp
  match i with
  | Sum.inl i =>
    simp only [Function.comp_apply, basisVector]
    apply basis_congr
    · rw [ComponentIdx.prod_apply_finSumFinEquiv]
    · simp
  | Sum.inr i =>
    simp only [Function.comp_apply, basisVector]
    apply basis_congr
    · rw [ComponentIdx.prod_apply_finSumFinEquiv]
    · simp

/-- The equivalence between the type `S.F.obj (OverColor.mk (Sum.elim c c1))` and the type
  `S.Tensor (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)`. -/
noncomputable def prodEquiv {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    S.F.obj (OverColor.mk (Sum.elim c c1)) ≃ₗ[k] S.Tensor (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) :=
  ((Action.forget _ _).mapIso (S.F.mapIso (OverColor.equivToIso finSumFinEquiv))).toLinearEquiv

TODO "6VZ3U" "Determine in `prodEquiv_symm_pure` why in `rw (transparency := .instances) [h1]`
  `(transparency := .instances)` is needed. As a first step adding this as a comment here."

lemma prodEquiv_symm_pure {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p : Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)) :
    prodEquiv.symm p.toTensor = PiTensorProduct.tprod k (Pure.prodEquiv p) := by
  rw [prodEquiv]
  change (S.F.map (OverColor.equivToIso finSumFinEquiv).inv).hom p.toTensor = _
  rw [Pure.toTensor]
  have h1 := OverColor.lift.map_tprod S.FD (equivToIso finSumFinEquiv).inv p
  simp only [F_def]
  rw (transparency := .instances) [h1]
  rfl

/-- The tensor product of two tensors as a bi-linear map from
  `S.Tensor c` and `S.Tensor c1` to `S.Tensor (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)`. -/
noncomputable def prodT {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    S.Tensor c →ₗ[k] S.Tensor c1 →ₗ[k] S.Tensor (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) := by
  refine LinearMap.mk₂ k ?_ ?_ ?_ ?_ ?_
  · exact fun t1 t2 => prodEquiv ((Functor.LaxMonoidal.μ S.F _ _).hom (t1 ⊗ₜ t2))
  · intro t1 t2 t3
    simp [TensorProduct.add_tmul]
  · intro n t1 t2
    simp [TensorProduct.smul_tmul]
  · intro t1 t2 t3
    simp [TensorProduct.tmul_add]
  · intro n t1 t2
    simp [TensorProduct.tmul_smul]

lemma prodT_pure {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (t : Pure S c) (t1 : Pure S c1) :
    (t.toTensor).prodT (t1.toTensor) = (Pure.prodP t t1).toTensor := by
  simp only [prodT, LinearMap.mk₂_apply]
  conv_lhs =>
    enter [2]
    rw [Pure.μ_toTensor_tmul_toTensor]
  change prodEquiv.toEquiv _ = _
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp only [instMonoidalCategoryStruct_tensorObj_left, instMonoidalCategoryStruct_tensorObj_hom,
    Functor.id_obj, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe]
  rw [prodEquiv_symm_pure]
  congr
  simp only [Pure.prodP, Equiv.apply_symm_apply]
  ext i
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

/-

## Product Maps

These maps are used in permutations of tensors.
-/

/-- Given a map `σ : Fin n → Fin n'`, the induced map `Fin (n + n2) → Fin (n' + n2)`. -/
def prodLeftMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n + n2) → Fin (n' + n2) :=
    finSumFinEquiv ∘ Sum.map σ id ∘ finSumFinEquiv.symm

@[simp]
lemma prodLeftMap_id {n2 n: ℕ} :
    prodLeftMap (n := n) n2 id = id := by
  simp [prodLeftMap]

/-- Given a map `σ : Fin n → Fin n'`, the induced map `Fin (n2 + n) → Fin (n2 + n')`. -/
def prodRightMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n2 + n) → Fin (n2 + n') :=
    finSumFinEquiv ∘ Sum.map id σ ∘ finSumFinEquiv.symm

@[simp]
lemma prodRightMap_id {n2 n: ℕ} :
    prodRightMap (n := n) n2 id = id := by
  simp [prodRightMap]

/-- The map between `Fin (n1 + n2 + n3)` and `Fin (n1 + (n2 + n3))` formed by casting. -/
def prodAssocMap (n1 n2 n3 : ℕ) : Fin (n1 + n2 + n3) → Fin (n1 + (n2 + n3)) :=
    Fin.cast (Nat.add_assoc n1 n2 n3)

@[simp]
lemma prodAssocMap_castAdd_castAdd {n1 n2 n3 : ℕ} (i : Fin n1) :
    prodAssocMap n1 n2 n3 (Fin.castAdd n3 (Fin.castAdd n2 i)) =
    finSumFinEquiv (Sum.inl i) := by
  simp [prodAssocMap, Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap_castAdd_natAdd {n1 n2 n3 : ℕ} (i : Fin n2) :
    prodAssocMap n1 n2 n3 (Fin.castAdd n3 (Fin.natAdd n1 i)) =
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))) := by
  simp [prodAssocMap, Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap_natAdd {n1 n2 n3 : ℕ} (i : Fin (n3)) :
    prodAssocMap n1 n2 n3 (Fin.natAdd (n1 + n2) i) =
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))) := by
  simp only [prodAssocMap, finSumFinEquiv_apply_right, Fin.ext_iff, Fin.coe_cast, Fin.coe_natAdd]
  omega

/-- The map between `Fin (n1 + (n2 + n3))` and `Fin (n1 + n2 + n3)` formed by casting. -/
def prodAssocMap' (n1 n2 n3 : ℕ) : Fin (n1 + (n2 + n3)) → Fin (n1 + n2 + n3) :=
    Fin.cast (Nat.add_assoc n1 n2 n3).symm

@[simp]
lemma prodAssocMap'_castAdd {n1 n2 n3 : ℕ} (i : Fin n1) :
    prodAssocMap' n1 n2 n3 (Fin.castAdd (n2 + n3) i) =
    finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) := by
  simp [prodAssocMap', Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap'_natAdd_castAdd {n1 n2 n3 : ℕ} (i : Fin n2) :
    prodAssocMap' n1 n2 n3 (Fin.natAdd n1 (Fin.castAdd n3 i)) =
    finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) := by
  simp [prodAssocMap', Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap'_natAdd_natAdd {n1 n2 n3 : ℕ} (i : Fin n3) :
    prodAssocMap' n1 n2 n3 (Fin.natAdd n1 (Fin.natAdd n2 i)) =
    finSumFinEquiv (Sum.inr i) := by
  simp only [prodAssocMap', finSumFinEquiv_apply_right, Fin.ext_iff, Fin.coe_cast, Fin.coe_natAdd]
  omega

/-- The map between `Fin (n1 + n2)` and `Fin (n2 + n1)` formed by swapping elements. -/
def prodSwapMap (n1 n2 : ℕ) : Fin (n1 + n2) → Fin (n2 + n1) :=
    finSumFinEquiv ∘ Sum.swap ∘ finSumFinEquiv.symm

@[simp]
lemma prodLeftMap_permCond {σ : Fin n' → Fin n} (c2 : Fin n2 → S.C) (h : PermCond c c' σ) :
    PermCond (Sum.elim c c2 ∘ finSumFinEquiv.symm)
      (Sum.elim c' c2 ∘ finSumFinEquiv.symm) (prodLeftMap n2 σ) := by
  apply And.intro
  · rw [prodLeftMap]
    refine (Equiv.comp_bijective (Sum.map σ id ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map σ id)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact h.1
    · exact Function.bijective_id
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodLeftMap, Function.comp_apply, Equiv.symm_apply_apply]
    match i with
    | Sum.inl i => simp [h.2]
    | Sum.inr i => rfl

@[simp]
lemma prodRightMap_permCond {σ : Fin n' → Fin n} (c2 : Fin n2 → S.C) (h : PermCond c c' σ) :
    PermCond (Sum.elim c2 c ∘ finSumFinEquiv.symm)
      (Sum.elim c2 c' ∘ finSumFinEquiv.symm) (prodRightMap n2 σ) := by
  apply And.intro
  · rw [prodRightMap]
    refine (Equiv.comp_bijective (Sum.map id σ ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map id σ)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact Function.bijective_id
    · exact h.1
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodRightMap, Function.comp_apply, Equiv.symm_apply_apply]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => simp [h.2]

@[simp]
lemma prodSwapMap_permCond {n1 n2 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C} :
    PermCond (Sum.elim c c2 ∘ finSumFinEquiv.symm)
      (Sum.elim c2 c ∘ finSumFinEquiv.symm) (prodSwapMap n2 n1) := by
  apply And.intro
  · dsimp only [prodSwapMap]
    refine (Equiv.comp_bijective (Sum.swap ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm Sum.swap).mpr ?_
    exact Function.bijective_iff_has_inverse.mpr ⟨Sum.swap, by simp⟩
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodSwapMap, Function.comp_apply, Equiv.symm_apply_apply]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl

@[simp]
lemma prodAssocMap_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    {c3 : Fin n3 → S.C} :
    PermCond (Sum.elim c (Sum.elim c2 c3 ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv.symm)
    (Sum.elim (Sum.elim c c2 ∘ finSumFinEquiv.symm) c3 ∘ finSumFinEquiv.symm)
    (prodAssocMap n1 n2 n3) := by
  apply And.intro
  · simp only [prodAssocMap]
    change Function.Bijective (finCongr (by ring))
    exact (finCongr _).bijective
  · intro i
    simp only [prodAssocMap, Function.comp_apply]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      match i with
      | Sum.inl i =>
        suffices Fin.cast (Nat.add_assoc n1 n2 n3)
          ((finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))) =
          finSumFinEquiv (Sum.inl i) by {rw [this]; simp}
        simp [Fin.ext_iff]
      | Sum.inr i =>
        suffices Fin.cast (Nat.add_assoc n1 n2 n3)
          ((finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))))) =
          finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))) by {rw [this]; simp}
        simp [Fin.ext_iff]
    | Sum.inr i =>
      suffices Fin.cast (Nat.add_assoc n1 n2 n3) (finSumFinEquiv (Sum.inr i)) =
          finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))) by {rw [this]; simp}
      simp only [finSumFinEquiv_apply_right, Fin.ext_iff, Fin.coe_cast, Fin.coe_natAdd]
      exact Nat.add_assoc n1 n2 ↑i

@[simp]
lemma prodAssocMap'_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    {c3 : Fin n3 → S.C} : PermCond
      (Sum.elim (Sum.elim c c2 ∘ finSumFinEquiv.symm) c3 ∘ finSumFinEquiv.symm)
      (Sum.elim c (Sum.elim c2 c3 ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv.symm)
      (prodAssocMap' n1 n2 n3) := by
  apply And.intro
  · simp only [prodAssocMap']
    change Function.Bijective (finCongr (by ring))
    exact (finCongr _).bijective
  · intro i
    simp only [prodAssocMap', Function.comp_apply]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      suffices ((Fin.cast (Nat.add_assoc n1 n2 n3).symm (finSumFinEquiv (Sum.inl i))))
        = finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) by {rw [this]; simp}
      simp [Fin.ext_iff]
    | Sum.inr i =>
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      match i with
      | Sum.inl i =>
        suffices (Fin.cast (Nat.add_assoc n1 n2 n3).symm
          (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i)))))
          = finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) by {rw [this]; simp}
        simp [Fin.ext_iff]
      | Sum.inr i =>
        suffices (Fin.cast (Nat.add_assoc n1 n2 n3).symm
          (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i)))))
          = (finSumFinEquiv (Sum.inr i)) by {rw [this]; simp}
        simp only [finSumFinEquiv_apply_right, Fin.ext_iff, Fin.coe_cast, Fin.coe_natAdd]
        exact Eq.symm (Nat.add_assoc n1 n2 ↑i)

/-!

## Relationships assocaited with products

-/

lemma Pure.prodP_component {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (p : Pure S c) (p1 : Pure S c1)
    (b : ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)) :
    (p.prodP p1).component b = p.component (ComponentIdx.splitEquiv b).1 *
    p1.component (ComponentIdx.splitEquiv b).2 := by
  simp only [component, Function.comp_apply]
  rw [← finSumFinEquiv.prod_comp]
  conv_lhs =>
    enter [2, x]
    rw [prodP_apply_finSumFinEquiv]
  simp only [Function.comp_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fintype.prod_sum_type]
  congr
  · funext x
    generalize_proofs h1 h2
    simp only [Discrete.mk.injEq] at h2
    rw [S.basis_congr_repr h2]
    rfl
  · funext x
    generalize_proofs h1 h2
    simp only [Discrete.mk.injEq] at h2
    rw [S.basis_congr_repr h2]
    rfl

lemma prodT_basis_repr_apply {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (t : Tensor S c) (t1 : Tensor S c1)
    (b : ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)) :
    (basis (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)).repr (prodT t t1) b =
    (basis c).repr t (ComponentIdx.splitEquiv b).1 *
    (basis c1).repr t1 (ComponentIdx.splitEquiv b).2 := by
  apply induction_on_pure (t := t)
  · apply induction_on_pure (t := t1)
    · intro p p1
      rw [prodT_pure]
      rw [basis_repr_pure, basis_repr_pure, basis_repr_pure]
      rw [Pure.prodP_component]
    · intro r t hp p
      simp only [basis_repr_pure, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
      rw [hp]
      ring
    · intro t1 t2 hp1 hp2 p
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, hp1, basis_repr_pure, hp2]
      ring_nf
  · intro r t hp
    simp only [map_smul, LinearMap.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
    rw [hp]
    ring
  · intro t1 t2 hp1 hp2
    simp only [map_add, LinearMap.add_apply, Finsupp.coe_add, Pi.add_apply, hp1, hp2]
    ring_nf

@[simp]
lemma Pure.prodP_equivariant {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (g : G) (p : Pure S c) (p1 : Pure S c1) :
    prodP (g • p) (g • p1) = g • prodP p p1 := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  conv_rhs =>
    rw [actionP_eq]
    simp only
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, prodP_apply_castAdd]
    generalize_proofs h
    have h1 := (S.FD.map (eqToHom h)).comm g
    have h1' := congrFun (congrArg (fun x => x.hom) h1) (p i)
    simp only [Function.comp_apply, ModuleCat.hom_comp, Rep.ρ_hom, LinearMap.coe_comp] at h1'
    exact h1'
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, prodP_apply_natAdd]
    generalize_proofs h
    have h1 := (S.FD.map (eqToHom h)).comm g
    have h1' := congrFun (congrArg (fun x => x.hom) h1) (p1 i)
    simp only [Function.comp_apply, ModuleCat.hom_comp, Rep.ρ_hom, LinearMap.coe_comp] at h1'
    exact h1'

@[simp]
lemma prodT_equivariant {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (g : G) (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT (g • t) (g • t1) = g • prodT t t1 := by
  let P (t : S.Tensor c) := prodT (g • t) (g • t1) = g • prodT t t1
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT (g • p.toTensor) (g • t1) = g • prodT p.toTensor t1
    change P t1
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, actionT_pure, actionT_pure, prodT_pure, actionT_pure]
      simp
    · intro r t h1
      simp_all only [actionT_smul, map_smul, P]
    · intro t1 t2 h1 h2
      simp_all only [actionT_add, map_add, P]
  · intro r t h1
    simp_all only [actionT_smul, map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [actionT_add, map_add, LinearMap.add_apply, P]

lemma Pure.prodP_swap {n n1} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C}
    (p : Pure S c) (p1 : Pure S c1) :
    Pure.prodP p p1 = permP (prodSwapMap n n1) (prodSwapMap_permCond) (Pure.prodP p1 p) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, Function.comp_apply, prodP_apply_castAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 i) (by simp [prodSwapMap])]
    simp [map_map_apply]
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, Function.comp_apply, prodP_apply_natAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.castAdd n i) (by simp [prodSwapMap])]
    simp [map_map_apply]

lemma prodT_swap {n n1} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C}
    (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond) (prodT t1 t) := by
  let P (t : S.Tensor c) := prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond)
    (prodT t1 t)
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT p.toTensor t1 = permT (prodSwapMap n n1)
      (prodSwapMap_permCond) (prodT t1 p.toTensor)
    change P t1
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, prodT_pure, permT_pure, Pure.prodP_swap]
    · intro r t h1
      simp_all only [map_smul, LinearMap.smul_apply, P]
    · intro t1 t2 h1 h2
      simp_all only [map_add, LinearMap.add_apply, P]
  · intro r t h1
    simp_all only [actionT_smul, map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [actionT_add, map_add, LinearMap.add_apply, P]

@[simp]
lemma Pure.prodP_permP_left {n n'} {c : Fin n → S.C} {c' : Fin n' → S.C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    Pure.prodP (permP σ h p) p2 = permP (prodLeftMap n2 σ)
      (prodLeftMap_permCond c2 h) (Pure.prodP p p2) := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [permP, prodLeftMap, Pure.prodP_apply_castAdd]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))))
      (finSumFinEquiv (Sum.inl (σ i)))
      (by simp)
    rw [← h1]
    simp [finSumFinEquiv_apply_left, prodP_apply_castAdd, Function.comp_apply, permP,
      map_map_apply]
  | Sum.inr i =>
    simp only [permP, prodLeftMap, Pure.prodP_apply_natAdd]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))))
      (finSumFinEquiv (Sum.inr i))
      (by simp)
    rw [← h1]
    simp [permP, map_map_apply]

@[simp]
lemma prodT_permT_left {n n'} {c : Fin n → S.C} {c' : Fin n' → S.C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT (permT σ h t) t2 = permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT t t2) := by
  let P (t : S.Tensor c) := prodT (permT σ h t) t2 =
    permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT t t2)
  change P t
  apply induction_on_pure
  · intro p
    let P (t2 : S.Tensor c2) := prodT (permT σ h p.toTensor) t2 =
      permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT p.toTensor t2)
    change P t2
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, permT_pure, permT_pure, prodT_pure]
      congr
      simp
    · intro r t h1
      simp_all only [actionT_smul, map_smul, P]
    · intro t1 t2 h1 h2
      simp_all only [actionT_add, map_add, P]
  · intro r t h1
    simp_all only [actionT_smul, map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [actionT_add, map_add, LinearMap.add_apply, P]

@[simp]
lemma Pure.prodP_permP_right {n n'} {c : Fin n → S.C} {c' : Fin n' → S.C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    prodP p2 (permP σ h p) = permP (prodRightMap n2 σ)
      (prodRightMap_permCond c2 h) (Pure.prodP p2 p) := by
  conv_lhs => rw [prodP_swap]
  conv_rhs => rw [prodP_swap]
  simp only [prodP_permP_left, prodSwapMap_permCond, permP_permP]
  apply Pure.permP_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodLeftMap, prodSwapMap, Function.comp_apply, Equiv.symm_apply_apply, prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl
  · rfl

@[simp]
lemma prodT_permT_right {n n'} {c : Fin n → S.C} {c' : Fin n' → S.C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT t2 (permT σ h t) = permT (prodRightMap n2 σ)
    (prodRightMap_permCond c2 h) (prodT t2 t) := by
  conv_lhs => rw [prodT_swap]
  conv_rhs => rw [prodT_swap]
  simp only [prodT_permT_left, prodSwapMap_permCond, permT_permT]
  apply permT_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodLeftMap, prodSwapMap, Function.comp_apply, Equiv.symm_apply_apply, prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl
  · rfl

lemma Pure.prodP_assoc {n n1 n2} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP (Pure.prodP p p1) p2 =
    permP (prodAssocMap n n1 n2) (prodAssocMap_permCond) (Pure.prodP p (Pure.prodP p1 p2)) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      simp only [finSumFinEquiv_apply_left, Function.comp_apply, prodP_apply_castAdd, permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_castAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
    | Sum.inr i =>
      simp only [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, Function.comp_apply,
        prodP_apply_castAdd, prodP_apply_natAdd, permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_natAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, Function.comp_apply, prodP_apply_natAdd, permP]
    rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_natAdd i)]
    simp [map_map_apply]

lemma prodT_assoc {n n1 n2} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT (prodT t t1) t2 =
    permT (prodAssocMap n n1 n2) (prodAssocMap_permCond) (prodT t (prodT t1 t2)) := by
  let P (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) := prodT (prodT t t1) t2 =
    permT (prodAssocMap n n1 n2) (prodAssocMap_permCond) (prodT t (prodT t1 t2))
  let P1 (t : S.Tensor c) := P t t1 t2
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap_permCond, P1, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap_permCond, P1, P]) t
  intro p
  let P2 (t1 : S.Tensor c1) := P p.toTensor t1 t2
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap_permCond, P2, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap_permCond, P2, P]) t1
  intro p1
  let P3 (t2 : S.Tensor c2) := P p.toTensor p1.toTensor t2
  change P3 t2
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap_permCond, P3, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap_permCond, P3, P]) t2
  intro p2
  simp only [P3, P, P2, P1]
  rw [prodT_pure, prodT_pure, prodT_pure, prodT_pure, permT_pure, Pure.prodP_assoc]

lemma Pure.prodP_assoc' {n n1 n2} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP p (prodP p1 p2) =
    permP (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodP (prodP p p1) p2) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, Function.comp_apply, prodP_apply_castAdd, permP]
    rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_castAdd i)]
    simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
  | Sum.inr i =>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Function.comp_apply,
        prodP_apply_natAdd, prodP_apply_castAdd, permP]
      rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_natAdd_castAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
    | Sum.inr i =>
      simp only [finSumFinEquiv_apply_right, Function.comp_apply, prodP_apply_natAdd, permP]
      rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_natAdd_natAdd i)]
      simp [map_map_apply]

lemma prodT_assoc' {n n1 n2} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C} {c2 : Fin n2 → S.C}
    (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT t (prodT t1 t2) =
    permT (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodT (prodT t t1) t2) := by
  let P (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) := prodT t (prodT t1 t2) =
    permT (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodT (prodT t t1) t2)
  let P1 (t : S.Tensor c) := P t t1 t2
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap'_permCond, P1, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap'_permCond, P1, P]) t
  intro p
  let P2 (t1 : S.Tensor c1) := P p.toTensor t1 t2
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap'_permCond, P2, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap'_permCond, P2, P]) t1
  intro p1
  let P3 (t2 : S.Tensor c2) := P p.toTensor p1.toTensor t2
  change P3 t2
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap'_permCond, P3, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap'_permCond, P3, P]) t2
  intro p2
  simp only [P3, P, P2, P1]
  rw [prodT_pure, prodT_pure, prodT_pure, prodT_pure, permT_pure, Pure.prodP_assoc']

lemma Pure.prodP_zero_right_permCond {n} {c : Fin n → S.C}
    {c1 : Fin 0 → S.C} : PermCond c (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) id := by
  simp only [Nat.add_zero, PermCond.on_id, Function.comp_apply]
  intro i
  obtain ⟨j, hi⟩ := finSumFinEquiv.surjective (Fin.cast (by rfl) i : Fin (n + 0))
  simp only [Nat.add_zero, Fin.cast_eq_self] at hi
  subst hi
  simp only [Equiv.symm_apply_apply]
  match j with
  | Sum.inl j => rfl
  | Sum.inr j => exact Fin.elim0 j

lemma Pure.prodP_zero_right {n} {c : Fin n → S.C}
    {c1 : Fin 0 → S.C} (p : Pure S c) (p0 : Pure S c1) :
    prodP p p0 = permP id (prodP_zero_right_permCond) p := by
  ext i
  obtain ⟨j, hi⟩ := finSumFinEquiv.surjective (Fin.cast (by rfl) i : Fin (n + 0))
  simp only [Nat.add_zero, Fin.cast_eq_self] at hi
  subst hi
  rw (transparency := .instances) [prodP_apply_finSumFinEquiv]
  match j with
  | Sum.inl j => rfl
  | Sum.inr j => exact Fin.elim0 j

lemma prodT_default_right {n} {c : Fin n → S.C}
    {c1 : Fin 0 → S.C} (t : S.Tensor c) :
    prodT t (Pure.toTensor default : S.Tensor c1) =
    permT id (Pure.prodP_zero_right_permCond) t := by
  let P (t : S.Tensor c) := prodT t (Pure.toTensor default : S.Tensor c1)
    = permT id (Pure.prodP_zero_right_permCond) t
  change P t
  apply induction_on_pure
  · intro p
    simp only [Nat.add_zero, P]
    rw (transparency := .instances) [prodT_pure]
    rw [Pure.prodP_zero_right]
    rw [permT_pure]
  · intro r t h1
    simp_all only [map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [map_add, LinearMap.add_apply, P]

end Tensor

end TensorSpecies
