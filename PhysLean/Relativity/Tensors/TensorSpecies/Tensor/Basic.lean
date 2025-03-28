/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Contractions.ContrMap
/-!

# Tensors associated with a tensor species

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] (S : TensorSpecies k)

noncomputable abbrev Tensor {n : ℕ} (c : Fin n → S.C) : Type := (S.F.obj (OverColor.mk c))

namespace Tensor

variable  {S : TensorSpecies k} {n n' n2 : ℕ} {c : Fin n → S.C} {c' : Fin n' → S.C}
  {c2 : Fin n2 → S.C}

abbrev ComponentIdx {n : ℕ} (c : Fin n → S.C) : Type := Π j, Fin (S.repDim (c j))

lemma ComponentIdx.congr_right {n : ℕ} {c : Fin n → S.C} (b : ComponentIdx c)
    (i j : Fin n) (h : i = j) : b i = Fin.cast (by simp [h]) (b j) := by
  subst h
  rfl

/-!

## Pure tensors

-/

/-- The type of tensors specified by a map to colors `c : OverColor S.C`. -/
abbrev Pure (S : TensorSpecies k) (c : Fin n → S.C) : Type :=
    (i : Fin n) → S.FD.obj (Discrete.mk (c i))

namespace Pure

@[simp]
lemma congr_right {n : ℕ} {c : Fin n → S.C} (p : Pure S c)
    (i j : Fin n) (h : i = j) : S.FD.map (eqToHom (by rw [h])) (p j) =p i  := by
  subst h
  simp

lemma congr_mid {n : ℕ} {c : Fin n → S.C} (c' : S.C) (p : Pure S c)
    (i j : Fin n) (h : i = j) (hi : c i = c') (hj : c j = c') :
    S.FD.map (eqToHom (by rw [hi] :  { as := c i } = { as := c' } ))  (p i)  =
    S.FD.map (eqToHom (by rw [hj] :  { as := c j } = { as := c' } ))  (p j)  := by
  subst hi
  simp
  symm
  apply congr_right
  exact h

lemma map_map_apply {n : ℕ} {c : Fin n → S.C} (c1 c2 : S.C) (p : Pure S c) (i : Fin n)
   (f :  ({ as := c i } : Discrete S.C) ⟶  { as := c1 })
   (g :  ({ as := c1 } : Discrete S.C) ⟶ { as := c2 }):
    (ConcreteCategory.hom (S.FD.map g))
    ((ConcreteCategory.hom (S.FD.map f)) (p i)) =
    S.FD.map (f ≫ g) (p i) := by
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]

noncomputable def toTensor {n : ℕ} {c : Fin n → S.C} (p : Pure S c) : S.Tensor c :=
  PiTensorProduct.tprod k p

lemma toTensor_apply {n : ℕ} (c : Fin n → S.C) (p : Pure S c) :
    toTensor p = PiTensorProduct.tprod k p := rfl

def update {n : ℕ} {c : Fin n → S.C}  [inst : DecidableEq (Fin n)]  (p : Pure S c) (i : Fin n)
    (x : S.FD.obj (Discrete.mk (c i))) : Pure S c := Function.update p i x

@[simp]
lemma update_same {n : ℕ} {c : Fin n → S.C} [inst : DecidableEq (Fin n)]  (p : Pure S c) (i : Fin n)
    (x : S.FD.obj (Discrete.mk (c i))) : (update p i x) i = x := by
  simp [update]

@[simp]
lemma toTensor_update_add {n : ℕ} {c : Fin n → S.C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (x y : S.FD.obj (Discrete.mk (c i))) :
    (update p i (x + y)).toTensor = (update p i x).toTensor + (update p i y).toTensor := by
  simp [toTensor, update]

@[simp]
lemma toTensor_update_smul {n : ℕ} {c : Fin n → S.C} [inst : DecidableEq (Fin n)] (p : Pure S c)
    (i : Fin n) (r : k) (y : S.FD.obj (Discrete.mk (c i))) :
    (update p i (r • y)).toTensor = r • (update p i y).toTensor := by
  simp [toTensor, update]

def drop {n : ℕ} {c : Fin (n + 1) → S.C} (p : Pure S c) (i : Fin (n + 1)) :
    Pure S (c ∘ i.succAbove) :=
  fun j => p (i.succAbove j)

@[simp]
lemma update_succAbove_drop {n : ℕ} {c : Fin (n + 1) → S.C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (k : Fin n) (x : S.FD.obj (Discrete.mk (c (i.succAbove k)))) :
    (update p (i.succAbove k) x).drop i = (p.drop i).update k x := by
  ext j
  simp [update, drop]
  by_cases h : j = k
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne]
    · rfl
    · simp
      rw [Function.Injective.eq_iff (Fin.succAbove_right_injective (p := i))]
      exact h

@[simp]
lemma update_drop_self {n : ℕ} {c : Fin (n + 1) → S.C} [inst : DecidableEq (Fin (n + 1))]
    (p : Pure S c) (i : Fin (n + 1)) (x : S.FD.obj (Discrete.mk (c i))) :
    (update p i x).drop i = p.drop i := by
  ext k
  simp [update, drop]
  rw [Function.update_of_ne]
  exact Fin.succAbove_ne i k

lemma μ_toTensor_tmul_toTensor {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
      (t : Pure S c) (t1 : Pure S c1) :
      ((Functor.LaxMonoidal.μ S.F _ _).hom (t.toTensor ⊗ₜ t1.toTensor)) =
      PiTensorProduct.tprod k (fun | Sum.inl i => t i | Sum.inr i => t1 i) := by
  change lift.μModEquiv _ _ _ (t.toTensor ⊗ₜ t1.toTensor) = _
  rw [lift.μModEquiv]
  simp only [lift.objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_tensorObj_V,
    Functor.id_obj, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [LinearEquiv.trans_apply]
  rw [toTensor, toTensor]
  rw [PhysLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  simp
  congr
  funext i
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

/-!

## Components

-/

def component {n : ℕ} {c : Fin n → S.C} (p : Pure S c) (b : ComponentIdx c) : k :=
    ∏ i, (S.basis (c i)).repr (p i) (b i)

lemma component_eq {n : ℕ} {c : Fin n → S.C} (p : Pure S c) (b : ComponentIdx c) :
    p.component b = ∏ i, (S.basis (c i)).repr (p i) (b i) := by rfl

lemma component_eq_drop {n : ℕ} {c : Fin (n + 1) → S.C} (p : Pure S c) (i : Fin (n + 1)) (b : ComponentIdx c) :
    p.component b = ((S.basis (c i)).repr (p i) (b i)) *
    ((drop p i).component (fun j => b (i.succAbove j))) := by
  simp only [component, Nat.succ_eq_add_one, Function.comp_apply]
  rw [Fin.prod_univ_succAbove _ i]
  rfl

@[simp]
lemma component_update_add {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → S.C} (p : Pure S c) (i : Fin n)
    (x y : S.FD.obj (Discrete.mk (c i))) (b : ComponentIdx c) :
    (update p i (x + y)).component b = (update p i x).component b +
    (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  rename_i n
  rw [component_eq_drop _ i, component_eq_drop _ i, component_eq_drop _ i]
  simp [add_mul]

@[simp]
lemma component_update_smul {n : ℕ} [inst : DecidableEq (Fin n)]
    {c : Fin n → S.C} (p : Pure S c) (i : Fin n)
    (x : k) (y : S.FD.obj (Discrete.mk (c i))) (b : ComponentIdx c) :
    (update p i (x • y)).component b = x * (update p i y).component b := by
  cases n
  · exact Fin.elim0 i
  rename_i n
  rw [component_eq_drop _ i, component_eq_drop _ i]
  simp only [update_same, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, update_drop_self]
  ring

noncomputable def componentMap {n : ℕ} (c : Fin n → S.C) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i))) (ComponentIdx c → k) where
  toFun p := fun b => component p b
  map_update_add' p i x y := by
    ext b
    change component (update p i (x + y)) b =
      component (update p i x) b + component (update p i y) b
    exact component_update_add p i x y b
  map_update_smul' p i x y := by
    ext b
    change component (update p i (x • y)) b = x * component (update p i y) b
    exact component_update_smul p i x y b

@[simp]
lemma componentMap_apply {n : ℕ} (c : Fin n → S.C)
    (p : Pure S c) : componentMap c p = p.component := by
  rfl

noncomputable def basisVector {n : ℕ} (c : Fin n → S.C) (b : ComponentIdx c) : Pure S c :=
  fun i => S.basis (c i) (b i)

@[simp]
lemma component_basisVector {n : ℕ} (c : Fin n → S.C) (b1 b2 : ComponentIdx c) :
    (basisVector c b1).component b2 = if b1 = b2 then 1 else 0 := by
  simp only [basisVector, component_eq, funext_iff]
  simp only [component, MultilinearMap.coe_mk,
    Basis.repr_self]
  by_cases h : b1 = b2
  · subst h
    simp
  · rw [funext_iff] at h
    simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    split
    next h => simp_all only [not_true_eq_false]
    next h =>
      simp_all only [not_forall]
      obtain ⟨w, h⟩ := h
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Finsupp.single_eq_of_ne hi]

end Pure

lemma induction_on_pure {n : ℕ} {c : Fin n → S.C} {P : S.Tensor c → Prop}
    (h : ∀ (p : Pure S c), P p.toTensor)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) :  P t := by
  refine PiTensorProduct.induction_on' t ?_ ?_
  · intro r p
    simpa using hsmul r _ (h p)
  · intro t1 t2
    exact fun a a_1 => hadd t1 t2 a a_1

/-!

## The basis

-/

noncomputable section Basis

/-- The linear map from tensors to coordinates. -/
def componentMap {n : ℕ} (c : Fin n → S.C) : S.Tensor c →ₗ[k] (ComponentIdx c → k) :=
  PiTensorProduct.lift (Pure.componentMap c)

@[simp]
lemma componentMap_pure {n : ℕ} (c : Fin n → S.C)
    (p : Pure S c) : componentMap c (p.toTensor) = Pure.componentMap c p := by
  simp only [componentMap, Pure.toTensor]
  change (PiTensorProduct.lift (Pure.componentMap c)) ((PiTensorProduct.tprod k) p) = _
  simp [PiTensorProduct.lift_tprod]

def ofComponents {n : ℕ} (c : Fin n → S.C) : (ComponentIdx c → k) →ₗ[k] S.F.obj (OverColor.mk c) where
  toFun f := ∑ b, f b • (Pure.basisVector c b).toTensor
  map_add' fb gb := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' fb r := by
    simp [smul_smul, Finset.smul_sum]

@[simp]
lemma componentMap_ofComponents {n : ℕ} (c : Fin n → S.C) (f : ComponentIdx c → k) :
    componentMap c (ofComponents c f) = f := by
  ext b
  simp [ofComponents]

@[simp]
lemma ofComponents_componentMap {n : ℕ} (c : Fin n → S.C) (t : S.Tensor c) :
    ofComponents c (componentMap c t) = t := by
  simp [ofComponents, LinearMap.comp_apply, PiTensorProduct.lift_tprod]
  apply induction_on_pure ?_ ?_ ?_ t
  · intro p
    simp only [componentMap_pure, Pure.componentMap_apply]
    have h1 (x : ComponentIdx c) : p.component x • (Pure.basisVector c x).toTensor =
        Pure.toTensor (fun i => ((S.basis (c i)).repr (p i)) (x i) • (S.basis (c i)) (x i)) := by
      rw [Pure.component_eq, Pure.toTensor]
      exact Eq.symm (MultilinearMap.map_smul_univ (PiTensorProduct.tprod k)
          (fun i => ((S.basis (c i)).repr (p i)) (x i)) fun i => (S.basis (c i)) (x i))
    conv_lhs =>
      enter [2, x]
      rw [h1]
    trans (PiTensorProduct.tprod k) fun i =>
      ∑ x, ((S.basis (c i)).repr (p i)) x • (S.basis (c i)) x
    · exact (MultilinearMap.map_sum (PiTensorProduct.tprod k) fun i j =>
        ((S.basis (c i)).repr (p i)) j • (S.basis (c i)) j).symm
    congr
    funext i
    exact Basis.sum_equivFun (S.basis (c i)) (p i)
  · intro r t ht
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, ← smul_smul]
    conv_rhs => rw [← ht]
    exact Eq.symm Finset.smul_sum
  · intro t1 t2 h1 h2
    simp [add_smul, Finset.sum_add_distrib, h1, h2]

/-- The basis of tensors. -/
def basis {n : ℕ} (c : Fin n → S.C) : Basis (ComponentIdx c) k (S.Tensor c) where
  repr := (LinearEquiv.mk (componentMap c) (ofComponents c)
    (fun x => by simp) (fun x => by simp)).trans
    (Finsupp.linearEquivFunOnFinite k k ((j : Fin n) → Fin (S.repDim (c j)))).symm

lemma basis_apply {n : ℕ} (c : Fin n → S.C) (b : ComponentIdx c) :
    basis c b = (Pure.basisVector c b).toTensor := by
  change ofComponents c _ = _
  simp [ofComponents]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb
    rw [Pi.single_apply]
    simp [hb]
  · simp

lemma induction_on_basis {n : ℕ} {c : Fin n → S.C} {P : S.Tensor c → Prop}
    (h : ∀ b, P (basis c b)) (hzero : P 0)
    (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t1 t2, P t1 → P t2 → P (t1 + t2)) (t : S.Tensor c) : P t := by
  let Pt (t : S.Tensor c)
      (ht : t ∈ Submodule.span k (Set.range (basis c))) := P t
  change Pt t (Basis.mem_span _ t)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨b, rfl⟩ := Set.mem_range.mp hx
    exact h b
  · simp [Pt, hzero]
  · intro t1 t2 h1 h2
    exact fun a a_1 => hadd t1 t2 a a_1
  · intro r t ht
    exact fun a => hsmul r t a

end Basis
/-!

## The action
-/

namespace Pure

noncomputable instance actionP : MulAction S.G (Pure S c) where
  smul g p := fun i => (S.FD.obj _).ρ g (p i)
  one_smul p := by
    ext i
    change (S.FD.obj _).ρ 1 (p i) = p i
    simp
  mul_smul g g' p := by
    ext i
    change (S.FD.obj _).ρ (g * g') (p i) = (S.FD.obj _).ρ g ((S.FD.obj _).ρ g' (p i))
    simp

noncomputable instance : SMul (S.G) (Pure S c) := actionP.toSMul

lemma actionP_eq {g : S.G} {p : Pure S c} : g • p = fun i => (S.FD.obj _).ρ g (p i) := rfl

@[simp]
lemma drop_actionP  {n : ℕ} {c : Fin (n + 1) → S.C} {i : Fin (n + 1)} {p : Pure S c} (g : S.G) :
    (g • p).drop i = g • (p.drop i) := by
  ext j
  rw [drop, actionP_eq, actionP_eq]
  simp only [Function.comp_apply]
  rfl

end Pure

noncomputable instance actionT : MulAction S.G (S.Tensor c) where
  smul g t := (S.F.obj (OverColor.mk c)).ρ g t
  one_smul t := by
    change (S.F.obj (OverColor.mk c)).ρ 1 t = t
    simp
  mul_smul g g' t := by
    change (S.F.obj (OverColor.mk c)).ρ (g * g') t =
      (S.F.obj (OverColor.mk c)).ρ g ((S.F.obj (OverColor.mk c)).ρ g' t)
    simp

lemma actionT_eq {g : S.G} {t : S.Tensor c} : g • t = (S.F.obj (OverColor.mk c)).ρ g t := rfl

lemma actionT_pure {g : S.G} {p : Pure S c} :
    g • p.toTensor = Pure.toTensor (g • p) := by
  rw [actionT_eq, Pure.toTensor]
  simp [F_def, lift, lift.obj']
  rw [OverColor.lift.objObj'_ρ_tprod]
  rfl

@[simp]
lemma actionT_add {g : S.G} {t1 t2 : S.Tensor c} :
    g • (t1 + t2) = g • t1 + g • t2 := by
  rw [actionT_eq, actionT_eq, actionT_eq]
  simp

@[simp]
lemma actionT_smul {g : S.G} {r : k} {t : S.Tensor c} :
    g • (r • t) = r • (g • t) := by
  rw [actionT_eq, actionT_eq]
  simp

@[simp]
lemma actionT_zero {g : S.G} : g • (0 : S.Tensor c) = 0 := by
  simp [actionT_eq]

/-!

## Permutations

And their interactions with
- actions
-/

def PermCond {n m : ℕ} (c : Fin n → S.C) (c1 : Fin m → S.C)
      (σ : Fin m → Fin n) : Prop :=
    Function.Bijective σ ∧ ∀ i, c (σ i) = c1 i

def PermCond.inv {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin m → Fin n) (h : PermCond c c1 σ) : Fin n → Fin m :=
  Fintype.bijInv h.1

def PermCond.toEquiv {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
      Fin n ≃ Fin m where
  toFun := PermCond.inv σ h
  invFun := σ
  left_inv := Fintype.rightInverse_bijInv h.1
  right_inv := Fintype.leftInverse_bijInv h.1

lemma PermCond.preserve_color {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
      ∀ (x : Fin m), c1 x = (c ∘ σ) x := by
  intro x
  obtain ⟨y, rfl⟩ := h.toEquiv.surjective x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [h.2]

def PermCond.toHom {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
      OverColor.mk c ⟶ OverColor.mk c1 :=
    equivToHomEq (h.toEquiv) (h.preserve_color)

lemma PermCond.ofHom {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ  : OverColor.mk c ⟶ OverColor.mk c1) :
      PermCond c c1 (Hom.toEquiv σ).symm := by
  apply And.intro
  · exact Equiv.bijective (Hom.toEquiv σ).symm
  · intro x
    simpa [OverColor.mk_hom] using Hom.toEquiv_symm_apply σ x

lemma PermCond.comp {n n1 n2 : ℕ} {c : Fin n → S.C} {c1 : Fin n1 → S.C}
      {c2 : Fin n2 → S.C} {σ : Fin n1 → Fin n} {σ2 : Fin n2 → Fin n1}
      (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2) :
      PermCond c c2 (σ ∘ σ2) := by
  apply And.intro
  · refine Function.Bijective.comp h.1 h2.1
  · intro x
    simp only [Function.comp_apply]
    rw [h.2, h2.2]

lemma fin_cast_permCond (n n1 : ℕ) {c : Fin n → S.C}  (h : n1 = n) :
      PermCond c (c ∘ Fin.cast h) (Fin.cast h) := by
    apply And.intro
    · exact Equiv.bijective (finCongr h)
    · intro i
      rfl
/-!

## Permutations

-/
def Pure.permP {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin m → Fin n) (h : PermCond c c1 σ) (p : Pure S c) : Pure S c1 :=
    fun i => S.FD.map (eqToHom (by simp [h.preserve_color])) (p (σ i))

@[simp]
lemma Pure.permP_basisVector {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin m → Fin n) (h : PermCond c c1 σ) (b : ComponentIdx c) :
      Pure.permP σ h (Pure.basisVector c b) =
      Pure.basisVector c1 (fun i => Fin.cast (by simp [h.preserve_color]) (b (σ i))) := by
  ext i
  simp [permP, Pure.basisVector]
  have h1 {c1 c2 : S.C} (h : c1 = c2)  (x : Fin (S.repDim c1)) :
      S.FD.map (eqToHom (by simp [h])) ((S.basis (c1)) x) =
      (S.basis c2) (Fin.cast (by simp [h]) x) := by
    subst h
    simp
  apply h1
  simp [h.preserve_color]

noncomputable def permT {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      (σ : Fin m → Fin n) (h : PermCond c c1 σ) : S.Tensor c →ₗ[k] S.Tensor c1 where
  toFun t := (ConcreteCategory.hom (S.F.map h.toHom).hom) t
  map_add' t1 t2 := by
    simp
  map_smul' r t := by
    simp

lemma permT_pure {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin m → Fin n} (h : PermCond c c1 σ) (p : Pure S c) :
      permT σ h p.toTensor = (p.permP σ h).toTensor := by
  simp only [F_def, permT, Pure.toTensor, LinearMap.coe_mk, AddHom.coe_mk]
  rw [OverColor.lift.map_tprod]
  rfl

@[simp]
lemma permT_equivariant {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ : Fin m → Fin n} (h : PermCond c c1 σ) (g : S.G) (t : S.Tensor c) :
      permT σ h (g • t) = g • permT σ h t := by
  simp [permT, actionT_eq]
  exact Rep.hom_comm_apply (S.F.map h.toHom) g t

@[congr]
lemma Pure.permP_congr {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ σ1 : Fin m → Fin n} {h : PermCond c c1 σ} {h1 : PermCond c c1 σ1}
      {p p1 : Pure S c} (hmap : σ = σ1) (hpure : p = p1) :
      Pure.permP σ h p = Pure.permP σ1 h1 p1 := by
  subst hmap hpure
  rfl

@[congr]
lemma permT_congr {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
      {σ σ1 : Fin m → Fin n} {h : PermCond c c1 σ} {h1 : PermCond c c1 σ1}
      (hmap : σ = σ1) {t  t1: S.Tensor c} (htensor : t = t1) :
      permT σ h t = permT σ1 h1 t1 := by
  subst hmap htensor
  rfl

@[simp]
lemma Pure.permP_permP {n m1 m2 : ℕ} {c : Fin n → S.C} {c1 : Fin m1 → S.C} {c2 : Fin m2 → S.C}
      {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2)
      (p : Pure S c) :
      Pure.permP σ2 h2 (Pure.permP σ h p) = Pure.permP (σ ∘ σ2) (PermCond.comp h h2) p := by
  ext i
  simp [permP, Pure.permP, Function.comp_apply, map_map_apply]

@[simp]
lemma permT_permT {n m1 m2 : ℕ} {c : Fin n → S.C} {c1 : Fin m1 → S.C} {c2 : Fin m2 → S.C}
      {σ : Fin m1 → Fin n} {σ2 : Fin m2 → Fin m1} (h : PermCond c c1 σ) (h2 : PermCond c1 c2 σ2)
      (t : S.Tensor c) :
      permT σ2 h2 (permT σ h t) = permT (σ ∘ σ2) (PermCond.comp h h2) t := by
  let P (t : S.Tensor c) := permT σ2 h2 (permT σ h t) = permT (σ ∘ σ2) (PermCond.comp h h2) t
  change P t
  apply induction_on_basis
  · intro b
    simp [P]
    rw [basis_apply, permT_pure, permT_pure, permT_pure]
    simp
  · simp [P]
  · intro r t h1
    simp_all [P]
  · intro t1 t2 h1 h2
    simp_all [P]
/-!

## Product

And its interaction with
- actions
- permutations

-/


def ComponentIdx.prodEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    ComponentIdx (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) ≃
    Π (i : Fin n1 ⊕ Fin n2), Fin (S.repDim (Sum.elim c c1 i))  :=
   (Equiv.piCongr finSumFinEquiv (fun _ => finCongr (by simp))).symm

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


def Pure.prodEquiv {n1 n2 : ℕ} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) ≃
    Π (i : Fin n1 ⊕ Fin n2), S.FD.obj (Discrete.mk ((Sum.elim c c1) i)) :=
  (Equiv.piCongr finSumFinEquiv
  (fun _ => ((Action.forget _ _).mapIso
    (S.FD.mapIso (Discrete.eqToIso (by simp)))).toLinearEquiv.toEquiv)).symm

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
    (y :  Fin (S.repDim c2)) (hxy : y = Fin.cast (by simp [h]) x) :
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

noncomputable def prodEquiv {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C} :
    S.F.obj (OverColor.mk (Sum.elim c c1)) ≃ₗ[k] S.Tensor (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm) :=
  ((Action.forget _ _).mapIso (S.F.mapIso (OverColor.equivToIso finSumFinEquiv))).toLinearEquiv

TODO "Determine in `prodEquiv_symm_pure` why in `rw (transparency := .instances) [h1]`
  `(transparency := .instances)` is needed. As a first step adding this as a comment here."

lemma prodEquiv_symm_pure {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (p : Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)) :
    prodEquiv.symm p.toTensor = PiTensorProduct.tprod k (Pure.prodEquiv p) := by
  rw [prodEquiv]
  change (S.F.map (OverColor.equivToIso finSumFinEquiv).inv).hom p.toTensor = _
  rw [Pure.toTensor]
  have h1 := OverColor.lift.map_tprod S.FD (equivToIso finSumFinEquiv).inv p
  simp [F_def]
  rw (transparency := .instances) [h1]
  rfl

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

lemma prodT_pure  {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
    (t : Pure S c) (t1 : Pure S c1) :
    prodT (t.toTensor) (t1.toTensor) = (Pure.prodP t t1).toTensor := by
  simp only [prodT, LinearMap.mk₂_apply]
  conv_lhs =>
    enter [2]
    rw [Pure.μ_toTensor_tmul_toTensor]
  change prodEquiv.toEquiv _ = _
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp
  rw [prodEquiv_symm_pure]
  congr
  simp [Pure.prodP]
  ext i
  match i with
  | Sum.inl i =>
    rfl
  | Sum.inr i =>
    rfl

/--

## Product Maps

These maps are used in permutations of tensors.
-/


def prodLeftMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n + n2) → Fin (n' + n2) :=
    finSumFinEquiv ∘ Sum.map σ id ∘ finSumFinEquiv.symm

def prodRightMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n2 + n) → Fin (n2 + n') :=
    finSumFinEquiv ∘ Sum.map id σ ∘ finSumFinEquiv.symm

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
  simp [prodAssocMap, Fin.castAdd, Fin.ext_iff]
  omega

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
  simp [prodAssocMap', Fin.castAdd, Fin.ext_iff]
  omega

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
    simp [prodLeftMap]
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
    simp [prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => simp [h.2]

@[simp]
lemma prodSwapMap_permCond {n1 n2 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C} :
    PermCond (Sum.elim c c2 ∘ finSumFinEquiv.symm)
      (Sum.elim c2 c ∘ finSumFinEquiv.symm) (prodSwapMap n2 n1) := by
  apply And.intro
  · dsimp [prodSwapMap]
    refine (Equiv.comp_bijective (Sum.swap ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm Sum.swap).mpr ?_
    exact Function.bijective_iff_has_inverse.mpr ⟨Sum.swap, by simp⟩
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp [prodSwapMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl


@[simp]
lemma prodAssocMap_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C}
      {c3 : Fin n3 → S.C} :
      PermCond (Sum.elim c (Sum.elim c2 c3 ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv.symm)
      (Sum.elim (Sum.elim c c2  ∘ finSumFinEquiv.symm) c3 ∘ finSumFinEquiv.symm)
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
      simp [Fin.ext_iff]
      exact Nat.add_assoc n1 n2 ↑i

@[simp]
lemma prodAssocMap'_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → S.C} {c2 : Fin n2 → S.C} {c3 : Fin n3 → S.C} :
      PermCond
      (Sum.elim (Sum.elim c c2  ∘ finSumFinEquiv.symm) c3 ∘ finSumFinEquiv.symm)
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
        suffices (Fin.cast (Nat.add_assoc n1 n2 n3).symm (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i)))))
          = finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) by {rw [this]; simp}
        simp [Fin.ext_iff]
      | Sum.inr i =>
        suffices (Fin.cast (Nat.add_assoc n1 n2 n3).symm (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i)))))
          = (finSumFinEquiv (Sum.inr i)) by {rw [this]; simp}
        simp [Fin.ext_iff]
        exact Eq.symm (Nat.add_assoc n1 n2 ↑i)

/-!

## Relationships assocaited with products

-/


@[simp]
lemma Pure.prodP_equivariant {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
      (g : S.G) (p : Pure S c) (p1 : Pure S c1) :
      prodP (g • p) (g • p1) = g • prodP p p1  := by
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
    simp at h1'
    exact h1'
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, prodP_apply_natAdd]
    generalize_proofs h
    have h1 := (S.FD.map (eqToHom h)).comm g
    have h1' := congrFun (congrArg (fun x => x.hom) h1) (p1 i)
    simp at h1'
    exact h1'

@[simp]
lemma prodT_equivariant {n1 n2} {c : Fin n1 → S.C} {c1 : Fin n2 → S.C}
      (g : S.G) (t : S.Tensor c) (t1 : S.Tensor c1) :
      prodT (g • t) (g • t1) = g • prodT t t1 := by
  let P (t : S.Tensor c) := prodT (g • t) (g • t1) = g • prodT t t1
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT (g • p.toTensor) (g • t1) = g • prodT p.toTensor t1
    change P t1
    apply induction_on_pure
    · intro q
      simp [P]
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
    simp [prodP_apply_castAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 i) (by simp [prodSwapMap])]
    simp [map_map_apply]
  | Sum.inr i =>
    simp [prodP_apply_natAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.castAdd n i) (by simp [prodSwapMap])]
    simp [map_map_apply]

lemma prodT_swap {n n1} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C}
    (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond) (prodT t1 t) := by
  let P (t : S.Tensor c) := prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond) (prodT t1 t)
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT p.toTensor t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond) (prodT t1 p.toTensor)
    change P t1
    apply induction_on_pure
    · intro q
      simp [P]
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
    Pure.prodP (permP σ h p) p2 = permP (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (Pure.prodP p p2) := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [permP, prodLeftMap,  Pure.prodP_apply_castAdd]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))))
      (finSumFinEquiv (Sum.inl (σ i)))
      (by simp)
    rw [← h1]
    simp  [finSumFinEquiv_apply_left, prodP_apply_castAdd, Function.comp_apply, permP,
      map_map_apply]
  | Sum.inr i =>
    simp only [permP, prodLeftMap, Pure.prodP_apply_natAdd]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ  id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))))
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
      simp [P]
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
    prodP p2 (permP σ h p) = permP (prodRightMap n2 σ) (prodRightMap_permCond c2 h) (Pure.prodP p2 p) := by
  conv_lhs => rw [prodP_swap]
  conv_rhs => rw [prodP_swap]
  simp
  apply Pure.permP_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp [prodSwapMap, prodLeftMap, prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl
  · rfl

@[simp]
lemma prodT_permT_right {n n'} {c : Fin n → S.C} {c' : Fin n' → S.C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT t2 (permT σ h t) = permT (prodRightMap n2 σ) (prodRightMap_permCond c2 h) (prodT t2 t) := by
  conv_lhs => rw [prodT_swap]
  conv_rhs => rw [prodT_swap]
  simp
  apply permT_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp [prodSwapMap, prodLeftMap, prodRightMap]
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
      simp [prodP_apply_castAdd, permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_castAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
    | Sum.inr i =>
      simp [permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_natAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
  | Sum.inr i =>
    simp [permP]
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
  simp [P3, P]
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
    simp [permP]
    rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_castAdd i)]
    simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
  | Sum.inr i =>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      simp [permP]
      rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_natAdd_castAdd i)]
      simp [map_map_apply, - eqToHom_refl, - Discrete.functor_map_id]
    | Sum.inr i =>
      simp [permP]
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
  simp [P3, P]
  rw [prodT_pure, prodT_pure, prodT_pure, prodT_pure, permT_pure, Pure.prodP_assoc']

end Tensor

end TensorSpecies
#lint only simpNF
