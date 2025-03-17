/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Dot
import PhysLean.Relativity.Lorentz.Weyl.Metric
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Pre
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.AsTensor
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
def realLorentzTensor (d : ℕ := 3) : TensorSpecies where
  C := realLorentzTensor.Color
  G := LorentzGroup d
  G_group := inferInstance
  k := ℝ
  k_commRing := inferInstance
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

end realLorentzTensor
end
