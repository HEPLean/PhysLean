/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Pre
import PhysLean.Relativity.Lorentz.ComplexTensor.Basic
/-!

## Real Lorentz tensors

Within this directory `Pre` is used to denote that the definitions are preliminary and
which are used to define `realLorentzTensor`.

-/
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace realLorentzTensor

/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color

/-- Color for complex Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h

end realLorentzTensor

noncomputable section
open realLorentzTensor in
/-- The tensor structure for complex Lorentz tensors. -/
def realLorentzTensor (d : ℕ := 3) : TensorSpecies ℝ (LorentzGroup d) where
  C := realLorentzTensor.Color
  FD := Discrete.functor fun c =>
    match c with
    | Color.up => Lorentz.Contr d
    | Color.down => Lorentz.Co d
  τ := fun c =>
    match c with
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.up => rfl
    | Color.down => rfl
  contr := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.contrCoContract
    | Discrete.mk Color.down => Lorentz.coContrContract
  metric := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.preContrMetric d
    | Discrete.mk Color.down => Lorentz.preCoMetric d
  unit := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.preCoContrUnit d
    | Discrete.mk Color.down => Lorentz.preContrCoUnit d
  repDim := fun c =>
    match c with
    | Color.up => 1 + d
    | Color.down => 1 + d
  repDim_neZero := fun c =>
    match c with
    | Color.up => by
      rw [add_comm]
      exact Nat.instNeZeroSucc
    | Color.down => by
      rw [add_comm]
      exact Nat.instNeZeroSucc
  basis := fun c =>
    match c with
    | Color.up => Lorentz.contrBasisFin d
    | Color.down => Lorentz.coBasisFin d
  contr_tmul_symm := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract_tmul_symm
    | Color.down => Lorentz.coContrContract_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.up => Lorentz.contr_preCoContrUnit
    | Color.down => Lorentz.contr_preContrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.up => Lorentz.preCoContrUnit_symm
    | Color.down => Lorentz.preContrCoUnit_symm
  contr_metric := fun c =>
    match c with
    | Color.up => by
      simp only [Discrete.functor_obj_eq_as, Action.instMonoidalCategory_tensorObj_V,
        Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_whiskerLeft_hom,
        Action.instMonoidalCategory_leftUnitor_hom_hom, Monoidal.tensorUnit_obj,
        Discrete.natTrans_app, Action.instMonoidalCategory_whiskerRight_hom,
        Action.instMonoidalCategory_associator_inv_hom,
        Action.instMonoidalCategory_associator_hom_hom, Equivalence.symm_inverse,
        Action.functorCategoryEquivalence_functor,
        Action.FunctorCategoryEquivalence.functor_obj_obj]
      exact Lorentz.contrCoContract_apply_metric
    | Color.down => by
      simp only [Discrete.functor_obj_eq_as, Action.instMonoidalCategory_tensorObj_V,
        Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_whiskerLeft_hom,
        Action.instMonoidalCategory_leftUnitor_hom_hom, Monoidal.tensorUnit_obj,
        Discrete.natTrans_app, Action.instMonoidalCategory_whiskerRight_hom,
        Action.instMonoidalCategory_associator_inv_hom,
        Action.instMonoidalCategory_associator_hom_hom, Equivalence.symm_inverse,
        Action.functorCategoryEquivalence_functor,
        Action.FunctorCategoryEquivalence.functor_obj_obj]
      exact Lorentz.coContrContract_apply_metric

namespace realLorentzTensor

/-- Notation for a real Lorentz tensor. -/
syntax (name := realLorentzTensorSyntax) "ℝT[" term,* "]" : term

macro_rules
  | `(ℝT[$termDim:term, $term:term, $terms:term,*]) =>
      `(((realLorentzTensor $termDim).F.obj (OverColor.mk (vecCons $term ![$terms,*]))))
  | `(ℝT[$termDim:term, $term:term]) =>
    `(((realLorentzTensor $termDim).F.obj (OverColor.mk (vecCons $term ![]))))
  | `(ℝT[$termDim:term]) =>`(((realLorentzTensor $termDim).F.obj (OverColor.mk (vecEmpty))))
  | `(ℝT[]) =>`(((realLorentzTensor 3).F.obj (OverColor.mk (vecEmpty))))

set_option quotPrecheck false in
/-- Notation for a real Lorentz tensor. -/
scoped[realLorentzTensor] notation "ℝT(" d "," c ")" =>
  (realLorentzTensor d).F.obj (OverColor.mk c)

/-- Color for real Lorentz tensors is decidable. -/
instance (d : ℕ) : DecidableEq (realLorentzTensor d).C := realLorentzTensor.instDecidableEqColor

@[simp]
lemma C_eq_color {d : ℕ} : (realLorentzTensor d).C = Color := rfl

/-!

## Simplyfing repDim

-/

lemma repDim_up {d : ℕ} : (realLorentzTensor d).repDim Color.up = 1 + d := rfl

lemma repDim_down {d : ℕ} : (realLorentzTensor d).repDim Color.down = 1 + d := rfl

@[simp]
lemma repDim_eq_one_plus_dim {d : ℕ} {c : (realLorentzTensor d).C} :
    (realLorentzTensor d).repDim c = 1 + d := by
  cases c
  · rfl
  · rfl

/-!

## Simplyfing τ

-/

@[simp]
lemma τ_up_eq_down {d : ℕ} : (realLorentzTensor d).τ Color.up = Color.down := rfl

@[simp]
lemma τ_down_eq_up {d : ℕ} : (realLorentzTensor d).τ Color.down = Color.up := rfl

/-!

## Simplification of contractions with respect to basis

-/

open TensorTree
open TensorSpecies

lemma contr_basis {d : ℕ} {c : (realLorentzTensor d).C}
    (i : Fin ((realLorentzTensor d).repDim c))
    (j : Fin ((realLorentzTensor d).repDim ((realLorentzTensor d).τ c))) :
    (realLorentzTensor d).castToField
      (((realLorentzTensor d).contr.app (Discrete.mk c)).hom
      ((realLorentzTensor d).basis c i ⊗ₜ
      (realLorentzTensor d).basis ((realLorentzTensor d).τ c) j))
      = (if i.val = j.val then 1 else 0) := by
  match c with
  | .up =>
    change Lorentz.contrCoContract.hom
      (Lorentz.contrBasisFin d i ⊗ₜ Lorentz.coBasisFin d j) = _
    rw [Lorentz.contrCoContract_hom_tmul]
    simp [Lorentz.contrBasisFin]
    rw [Pi.single_apply]
    refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
    simp only [eq_comm, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, repDim_up]
  | .down =>
    change Lorentz.coContrContract.hom
      (Lorentz.coBasisFin d i ⊗ₜ Lorentz.contrBasisFin d j) = _
    rw [Lorentz.coContrContract_hom_tmul]
    simp only [Action.instMonoidalCategory_tensorUnit_V, Lorentz.coBasisFin_toFin1dℝ,
      Lorentz.contrBasisFin_toFin1dℝ, dotProduct_single, mul_one]
    rw [Pi.single_apply]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_comm, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, repDim_up]

lemma contr_tensorBasis_repr_apply_eq_contrSection {n d: ℕ}
    {c : Fin (n + 1 + 1) → (realLorentzTensor d).C}
    {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {h : c (i.succAbove j) = (realLorentzTensor d).τ (c i)}
    (t : TensorTree (realLorentzTensor d) c)
    (b : Π k, Fin ((realLorentzTensor d).repDim (c (i.succAbove (j.succAbove k))))) :
    ((realLorentzTensor d).tensorBasis
    (c ∘ i.succAbove ∘ j.succAbove)).repr (contr i j h t).tensor b =
    ∑ (x : TensorBasis.ContrSection b),
    (((realLorentzTensor d).tensorBasis c).repr t.tensor x.1) *
    if (x.1 i).1 = (x.1 (i.succAbove j)).1 then 1 else 0 := by
  rw [contr_tensorBasis_repr_apply]
  congr
  funext x
  congr 1
  exact contr_basis _ _

open TensorSpecies.TensorBasis in
lemma contr_tensorBasis_repr_apply_eq_fin {n d: ℕ} {c : Fin (n + 1 + 1) → (realLorentzTensor d).C}
    {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {h : c (i.succAbove j) = (realLorentzTensor d).τ (c i)}
    (t : TensorTree (realLorentzTensor d) c)
    (b : Π k, Fin ((realLorentzTensor d).repDim (c (i.succAbove (j.succAbove k))))) :
    ((realLorentzTensor d).tensorBasis
    (c ∘ i.succAbove ∘ j.succAbove)).repr (contr i j h t).tensor b =
    ∑ (x : Fin (1 + d)),
    (((realLorentzTensor d).tensorBasis c).repr t.tensor
    (liftToContrSection b ⟨Fin.cast (by simp) x, Fin.cast (by simp) x⟩)) := by
  rw [contr_tensorBasis_repr_apply_eq_contrSection]
  rw [← (contrSectionEquiv b).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  let e : Fin ((realLorentzTensor d).repDim (c i)) ≃ Fin (1 + d) :=
    (Fin.castOrderIso (by simp)).toEquiv
  rw [← e.symm.sum_comp]
  congr
  funext x
  simp only [C_eq_color, Nat.succ_eq_add_one, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.cast (by simp) x)]
  · simp [contrSectionEquiv, e]
  · intro y _ hy
    rw [if_neg]
    · simp [contrSectionEquiv, e]
      rw [Fin.ne_iff_vne] at hy
      simp at hy
      exact fun a => hy (id (Eq.symm a))
  · simp

end realLorentzTensor
end
