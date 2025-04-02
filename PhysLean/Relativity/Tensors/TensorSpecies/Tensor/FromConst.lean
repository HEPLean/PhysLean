/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Contraction
/-!

# Constructors of tensors.

There are a number of ways to construct explicit tensors.
-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {G : Type} [Group G] {S : TensorSpecies k G}

namespace Tensor

/-!

## Tensors with a single index.

-/

noncomputable def Pure.fromSingleP {c : S.C} : S.FD.obj {as := c} ≃ₗ[k] Pure S ![c] where
  toFun x := fun | 0 => x
  invFun x := x 0
  map_add' x y := by
    ext i
    fin_cases i
    rfl
  map_smul' r x := by
    ext i
    fin_cases i
    rfl
  left_inv x := by rfl
  right_inv x := by
    ext i
    fin_cases i
    rfl

noncomputable def fromSingleT {c : S.C} : S.FD.obj {as := c} ≃ₗ[k] S.Tensor ![c] where
  toFun x := (OverColor.forgetLiftAppCon S.FD c).symm.hom x
  invFun x := (OverColor.forgetLiftAppCon S.FD c).hom x
  map_add' x y := by
    change ((forgetLiftAppCon S.FD c).inv).hom.hom' (x + y) = _
    simp
    rfl
  map_smul' r x := by
    change ((forgetLiftAppCon S.FD c).inv).hom.hom' (r • x) = _
    simp
    rfl
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

lemma fromSingleT_symm_pure {c : S.C} (p : Pure S ![c]) :
    fromSingleT.symm p.toTensor = Pure.fromSingleP.symm p := by
  simp [fromSingleT]
  change  (forgetLiftApp S.FD c).hom.hom _ = _
  rw [forgetLiftApp_hom_hom_apply_eq]
  simp [Pure.toTensor]
  conv_lhs =>
    erw [lift.map_tprod S.FD]
  congr
  funext i
  simp [lift.discreteFunctorMapEqIso, Pure.fromSingleP]
  change (ConcreteCategory.hom ((FD S).map (eqToHom _))) (p _) = p 0
  apply Pure.congr_right
  ext
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.val_eq_zero]

lemma fromSingleT_eq_pureT {c : S.C} (x : S.FD.obj {as := c}) :
    fromSingleT x = Pure.toTensor (fun 0 => x : Pure S ![c]):= by
  change _ = Pure.toTensor (Pure.fromSingleP x)
  obtain ⟨p, rfl⟩ := Pure.fromSingleP.symm.surjective x
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply]
  rw [← fromSingleT_symm_pure]
  simp

lemma actionT_fromSingleT {c : S.C} (x : S.FD.obj {as := c}) (g : G) :
    g • fromSingleT x = fromSingleT ((S.FD.obj {as := c}).ρ g x) := by
  rw [fromSingleT_eq_pureT, actionT_pure, fromSingleT_eq_pureT]
  congr
  funext x
  fin_cases x
  rfl

lemma fromSingleT_map {c c1 : S.C} (h : ({as := c} : Discrete S.C) = {as := c1}) (x : S.FD.obj {as := c}) :
    fromSingleT (S.FD.map (eqToHom h) x) =
    permT id (by simp at h; simp [h]) (fromSingleT x) := by
  rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT, permT_pure]
  congr
  funext i
  fin_cases i
  rfl

lemma contrT_fromSingleT_fromSingleT {c : S.C} (x : S.FD.obj {as :=  c})
    (y : S.FD.obj {as := S.τ c}) :
    contrT 0 1 (by simp; change _ = S.τ (S.τ c); simp; rfl) (prodT (fromSingleT x) (fromSingleT y)) =
    (S.contr.app (Discrete.mk (c))) (x ⊗ₜ[k] y) • (Pure.toTensor default) := by
  rw [fromSingleT_eq_pureT, fromSingleT_eq_pureT]
  rw [prodT_pure, contrT_pure, ]
  simp [Pure.contrP,  Pure.contrPCoeff]
  congr 1
  · congr
    · trans Pure.prodP (fun | (0 : Fin 1) => x)
        (fun | (0 : Fin 1) => y) (finSumFinEquiv (Sum.inl 0))
      · rfl
      · rw [Pure.prodP_apply_finSumFinEquiv]
        simp
        rfl
    · trans (ConcreteCategory.hom (𝟙 (S.FD.obj { as := Sum.elim ![c] ![S.τ c] (finSumFinEquiv.symm 1) })))
        (Pure.prodP (fun | (0 : Fin 1) => x)
        (fun | (0 : Fin 1) => y) (finSumFinEquiv (Sum.inr 0))  )
      · rfl
      · rw [Pure.prodP_apply_finSumFinEquiv]
        simp
        rfl
  · congr 1
    ext i
    exact Fin.elim0 i
/-!

## Tensors with two indices.

-/
open TensorProduct

/-!

## fromPairT

-/

noncomputable def fromPairT {c1 c2 : S.C}  :
    (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V →ₗ[k] S.Tensor ![c1, c2] where
  toFun x :=
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl))
    (TensorProduct.lift prodT (TensorProduct.map (fromSingleT (c := c1))
      (fromSingleT (c := c2)) (x) : S.Tensor ![c1] ⊗[k] S.Tensor ![c2]))
  map_add' x y := by
    simp
  map_smul' r x := by
    simp

lemma fromPairT_tmul {c1 c2 : S.C} (x : S.FD.obj (Discrete.mk c1))
    (y : S.FD.obj (Discrete.mk c2)) :
    fromPairT (x ⊗ₜ[k] y) =
    permT id (And.intro Function.bijective_id (fun i => by fin_cases i <;> rfl))
    (prodT (fromSingleT x) (fromSingleT y)) := by
  rfl

lemma actionT_fromPairT {c1 c2 : S.C}
    (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V)
    (g : G) :
    g • fromPairT x = fromPairT (TensorProduct.map ((S.FD.obj (Discrete.mk c1)).ρ g)
      ((S.FD.obj (Discrete.mk c2)).ρ g) x) := by
  let P  (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) : Prop :=
    g • fromPairT x = fromPairT (TensorProduct.map ((S.FD.obj (Discrete.mk c1)).ρ g)
      ((S.FD.obj (Discrete.mk c2)).ρ g) x)
  change P x
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    simp [P]
    rw [fromPairT_tmul, ← permT_equivariant, ← prodT_equivariant,
      actionT_fromSingleT, actionT_fromSingleT]
    rfl
  · intro x y hx hy
    simp [P, hx, hy]

lemma fromPairT_map_right {c1 c2 c2' : S.C} (h :c2 = c2')
    (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) :
    fromPairT (TensorProduct.map LinearMap.id (S.FD.map (eqToHom (by rw [h]))).hom.hom' x) =
    permT id (by simp; intro i; fin_cases i <;> simp [h])
    (fromPairT x) := by
  let P (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) : Prop :=
    fromPairT (TensorProduct.map LinearMap.id (S.FD.map (eqToHom (by rw [h]))).hom.hom' x) =
    permT id (by simp; intro i; fin_cases i <;> simp [h])
    (fromPairT x)
  change P x
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    simp [P]
    rw [fromPairT_tmul]
    conv_lhs =>
      enter [2, 2]
      erw [fromSingleT_map]
    rw [prodT_permT_right, permT_permT]
    simp
    rw [fromPairT_tmul, permT_permT]
    rfl
  · intro x y hx hy
    simp [P, hx, hy]

lemma fromPairT_comm {c1 c2 : S.C}
    (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V)  :
    fromPairT (TensorProduct.comm k _ _ x) =
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
    (fromPairT x) := by
  let P (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) : Prop :=
    fromPairT (TensorProduct.comm k _ _ x) =
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
    (fromPairT x)
  change P x
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    simp [P]
    rw [fromPairT_tmul, fromPairT_tmul]
    rw [prodT_swap]
    simp
    congr
    ext i
    fin_cases i
    · rfl
    · rfl
  · intro x y hx hy
    simp [P, hx, hy]

noncomputable def fromPairTContr {c c1 c2 : S.C}
    (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c)).V)
    (y : (S.FD.obj (Discrete.mk (S.τ c))).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) :
    S.Tensor ![c1, c2] :=
  let V1 := (S.FD.obj (Discrete.mk c1))
  let V2 := (S.FD.obj (Discrete.mk c))
  let V2' := (S.FD.obj (Discrete.mk (S.τ c)))
  let V3 := (S.FD.obj (Discrete.mk c2))
  let T1 : (V1 ⊗[k] V2) ⊗[k] (V2' ⊗[k] V3) := x ⊗ₜ[k] y
  let T2 : V1 ⊗[k] (V2 ⊗[k] (V2' ⊗[k] V3)) := (α_ V1 V2 (V2' ⊗ V3)).hom.hom T1
  let T3 : V1 ⊗[k] (V2 ⊗[k] V2') ⊗[k] V3 := (V1 ◁ (α_ V2 V2' V3).inv).hom T2
  let T4 : V1 ⊗[k] k ⊗[k] V3 := (V1 ◁ ((S.contr.app (Discrete.mk c)) ▷ V3)).hom T3
  let T5 : V1 ⊗[k] V3 := (V1 ◁ (λ_ V3).hom).hom T4
  fromPairT T5

lemma fromPairTContr_tmul_tmul {c c1 c2 : S.C}
    (x1 : S.FD.obj (Discrete.mk c1))
    (x2 : S.FD.obj (Discrete.mk c))
    (y1 : S.FD.obj (Discrete.mk (S.τ c)))
    (y2 : S.FD.obj (Discrete.mk c2)) :
    fromPairTContr (x1 ⊗ₜ[k] x2) (y1 ⊗ₜ[k] y2) =
    (S.contr.app (Discrete.mk (c))) (x2 ⊗ₜ[k] y1) • fromPairT (x1 ⊗ₜ[k] y2) := by
  rw [fromPairTContr]
  conv_lhs =>
    enter [2, 2, 2, 2]
    change x1 ⊗ₜ[k] (x2 ⊗ₜ[k] y1 ⊗ₜ[k] y2)
  conv_lhs =>
    enter [2, 2, 2]
    change x1 ⊗ₜ[k] (x2 ⊗ₜ[k] y1) ⊗ₜ[k] y2
  conv_lhs =>
    enter [2, 2]
    change x1 ⊗ₜ[k] (S.contr.app (Discrete.mk (c))) (x2 ⊗ₜ[k] y1) ⊗ₜ[k] y2
  conv_lhs =>
    enter [2]
    change x1 ⊗ₜ[k] ((S.contr.app (Discrete.mk (c))) (x2 ⊗ₜ[k] y1) • y2)
  simp [tmul_smul]

/-
lemma fromPairT_contr_fromPairT_eq_fromPairTContr (c c1 c2 : S.C)
    (x : (S.FD.obj (Discrete.mk c1)).V ⊗[k] (S.FD.obj (Discrete.mk c)).V)
    (y : (S.FD.obj (Discrete.mk (S.τ c))).V ⊗[k] (S.FD.obj (Discrete.mk c2)).V) :
    contrT (n := 2) 1 2 (by simp; change _ = S.τ (S.τ c); simp; rfl)
      (prodT (fromPairT x) (fromPairT y)) =
    permT id (by simp; sorry ) (fromPairTContr (c := c) (c1 := c1) (c2 := c2) x y) := by sorry-/
/-!

## fromConstPair

-/

/-- A constant two tensor (e.g. metric and unit). -/
noncomputable def fromConstPair {c1 c2 : S.C}
      (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
      S.Tensor ![c1, c2] := fromPairT (v.hom (1 : k))


/-- Tensors formed by `fromConstPair` are invariant under the group action. -/
@[simp]
lemma actionT_fromConstPair {c1 c2 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2))
    (g : G) : g • fromConstPair v = fromConstPair v := by
  rw [fromConstPair, actionT_fromPairT]
  congr 1
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 }).ρ g))) _ = _
  erw [← v.comm g]
  simp


@[simp]
lemma fromConstPair_whiskerLeft  {c1 c2 c2' : S.C} (h : c2 = c2')
      (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
    fromConstPair (v ≫
    ((S.FD.obj ({ as := c1 } : Discrete S.C) ◁ S.FD.map (Discrete.eqToHom (h))))) =
    permT id (And.intro (Function.bijective_id) (by simp [h]))  (fromConstPair v) := by
  rw [fromConstPair]
  simp
  change  fromPairT (TensorProduct.map LinearMap.id (S.FD.map (eqToHom (by rw [h]))).hom.hom' _) = _
  rw [fromPairT_map_right h]
  rfl

@[simp]
lemma fromConstPair_braid {c1 c2 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
    fromConstPair (v ≫ (β_ _ _).hom) =
    permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
      (fromConstPair v) := by
  rw [fromConstPair]
  simp
  change fromPairT (TensorProduct.comm k _ _ _) = _
  rw [fromPairT_comm]
  rfl

/-!

## Tensors with more indices

-/

/-- A general constant node. -/
def fromConst {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep k G) ⟶ S.F.obj (OverColor.mk c)) :
    Tensor S c := (T.hom (1 : k))


/-- A constant three tensor (e.g. the Pauli matrices). -/
noncomputable def fromConstTriple {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
      S.FD.obj (Discrete.mk c3)) :
    S.Tensor ![c1, c2, c3] := (OverColor.Discrete.tripleIsoSep S.FD).hom.hom (v.hom (1 : k))

/-!

## Actions on tensors constructed from morphisms

Tensors constructed from morphisms are invariant under the group action.

-/

/-- Tensors formed by `fromConst` are invariant under the group action. -/
@[simp]
lemma actionT_fromConst {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep k G) ⟶ S.F.obj (OverColor.mk c))
    (g : G) : g • fromConst T = fromConst T:= by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    fromConstPair]
  change ((T.hom ≫ ModuleCat.ofHom ((S.F.obj _).ρ g))) _ = _
  erw [← T.comm g]
  simp [fromConst]

/-- An `action` node on a `constThreeNode` leaves the tensor invariant. -/
@[simp]
lemma action_fromConstTriple {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
      S.FD.obj (Discrete.mk c3))
    (g : G) : g • fromConstTriple v = fromConstTriple v := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq, fromConstTriple,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  change ((Discrete.tripleIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2, c3])).ρ g)) (v.hom _) = _
  erw [← (Discrete.tripleIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 } ⊗
    S.FD.obj { as := c3 }).ρ g)) ≫ (Discrete.tripleIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp


end Tensor

end TensorSpecies
