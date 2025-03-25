/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.ComplexTensor.OfRat
import PhysLean.Relativity.Lorentz.ComplexTensor.Units.Basic
/-!

## Basis of units

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open Complex
open TensorProduct
open IndexNotation
open TensorTree
open OverColor.Discrete

namespace complexLorentzTensor

/-!

## Expansion of units in terms of the tensor basis.

-/

lemma coContrUnit_tensorBasis : coContrUnit =
    complexLorentzTensor.tensorBasis ![Color.down, Color.up] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.down, Color.up] (fun _ => 1)
    + complexLorentzTensor.tensorBasis ![Color.down, Color.up] (fun _ => 2)
    + complexLorentzTensor.tensorBasis ![Color.down, Color.up] (fun _ => 3) := by
  trans {δ' | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_coContrUnit]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  rw (transparency := .instances) [Lorentz.coContrUnit_apply_one]
  rw [Lorentz.coContrUnitVal_expand_tmul]
  simp only [Fin.isValue, map_add]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      simp [complexLorentzTensor]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Fin.mk_one, Fin.isValue, cons_val_one, head_cons,
        Lorentz.complexContrBasisFin4_apply_zero,
        Lorentz.complexContrBasisFin4_apply_two, Lorentz.complexContrBasisFin4_apply_one,
        Lorentz.complexContrBasisFin4_apply_three]
      rfl

lemma contrCoUnit_tensorBasis : contrCoUnit =
    complexLorentzTensor.tensorBasis ![Color.up, Color.down] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.down] (fun _ => 1)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.down] (fun _ => 2)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.down] (fun _ => 3) := by
  trans {δ | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_contrCoUnit]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  rw (transparency := .instances) [Lorentz.contrCoUnit_apply_one]
  rw [Lorentz.contrCoUnitVal_expand_tmul]
  simp only [Fin.isValue, map_add]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      simp [complexLorentzTensor]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Fin.mk_one, Fin.isValue, cons_val_one, head_cons,
        Lorentz.complexCoBasisFin4_apply_one, Lorentz.complexCoBasisFin4_apply_zero,
        Lorentz.complexCoBasisFin4_apply_two, Lorentz.complexCoBasisFin4_apply_three]
      rfl

lemma altLeftLeftUnit_tensorBasis : altLeftLeftUnit =
    complexLorentzTensor.tensorBasis ![Color.downL, Color.upL] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.downL, Color.upL] (fun _ => 1) := by
  trans {δL' | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_altLeftLeftUnit]
  simp only [constTwoNode_tensor, Action.instMonoidalCategory_tensorObj_V]
  rw (transparency := .instances) [Fermion.altLeftLeftUnit_apply_one]
  rw [Fermion.altLeftLeftUnitVal_expand_tmul]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add]
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, OverColor.mk_hom,
      cons_val_one, head_cons]
      rfl

lemma leftAltLeftUnit_tensorBasis : leftAltLeftUnit =
    complexLorentzTensor.tensorBasis ![Color.upL, Color.downL] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.upL, Color.downL] (fun _ => 1) := by
  trans {δL | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_leftAltLeftUnit]
  simp only [constTwoNode_tensor, Action.instMonoidalCategory_tensorObj_V]
  rw (transparency := .instances) [Fermion.leftAltLeftUnit_apply_one]
  rw [Fermion.leftAltLeftUnitVal_expand_tmul]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add]
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, OverColor.mk_hom,
      cons_val_one, head_cons]
      rfl

lemma altRightRightUnit_tensorBasis : altRightRightUnit =
    complexLorentzTensor.tensorBasis ![Color.downR, Color.upR] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.downR, Color.upR] (fun _ => 1) := by
  trans {δR' | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_altRightRightUnit]
  simp only [constTwoNode_tensor, Action.instMonoidalCategory_tensorObj_V]
  rw (transparency := .instances) [Fermion.altRightRightUnit_apply_one]
  rw [Fermion.altRightRightUnitVal_expand_tmul]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add]
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, OverColor.mk_hom,
      cons_val_one, head_cons]
      rfl

lemma rightAltRightUnit_tensorBasis : rightAltRightUnit =
    complexLorentzTensor.tensorBasis ![Color.upR, Color.downR] (fun _ => 0)
    + complexLorentzTensor.tensorBasis ![Color.upR, Color.downR] (fun _ => 1) := by
  trans {δR | μ ν}ᵀ.tensor
  · simp
  rw [tensorNode_rightAltRightUnit]
  simp only [constTwoNode_tensor, Action.instMonoidalCategory_tensorObj_V]
  rw (transparency := .instances) [Fermion.rightAltRightUnit_apply_one]
  rw [Fermion.rightAltRightUnitVal_expand_tmul]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add]
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rw [TensorSpecies.tensorBasis_eq_basisVector]
    apply congrArg
    funext i
    fin_cases i
    · simp only [complexLorentzTensor, Discrete.functor_obj_eq_as, Monoidal.tensorUnit_obj,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, OverColor.mk_hom,
      cons_val_one, head_cons]
      rfl

/-!

## As rationals tensors

-/

lemma coContrUnit_eq_ofRat : δ' = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [coContrUnit_tensorBasis]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
  simp only [← map_add, Fin.isValue]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

lemma contrCoUnit_eq_ofRat : δ = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [contrCoUnit_tensorBasis]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
  simp only [← map_add, Fin.isValue]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

  lemma altLeftLeftUnit_eq_ofRat : δL' = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
    apply (complexLorentzTensor.tensorBasis _).repr.injective
    ext b
    rw [altLeftLeftUnit_tensorBasis]
    repeat rw [tensorBasis_eq_ofRat]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
    simp only [← map_add, Fin.isValue]
    apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
    revert b
    with_unfolding_all decide

  lemma leftAltLeftUnit_eq_ofRat : δL = ofRat fun f =>
      if f 0 = f 1 then 1 else 0 := by
    apply (complexLorentzTensor.tensorBasis _).repr.injective
    ext b
    rw [leftAltLeftUnit_tensorBasis]
    repeat rw [tensorBasis_eq_ofRat]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
    simp only [← map_add, Fin.isValue]
    apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
    revert b
    with_unfolding_all decide

  lemma altRightRightUnit_eq_ofRat : δR' = ofRat fun f =>
      if f 0 = f 1 then 1 else 0 := by
    apply (complexLorentzTensor.tensorBasis _).repr.injective
    ext b
    rw [altRightRightUnit_tensorBasis]
    repeat rw [tensorBasis_eq_ofRat]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
    simp only [← map_add, Fin.isValue]
    apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
    revert b
    with_unfolding_all decide

  lemma rightAltRightUnit_eq_ofRat : δR = ofRat fun f =>
      if f 0 = f 1 then 1 else 0 := by
    apply (complexLorentzTensor.tensorBasis _).repr.injective
    ext b
    rw [rightAltRightUnit_tensorBasis]
    repeat rw [tensorBasis_eq_ofRat]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_add, Finsupp.coe_add, Pi.add_apply,
    ofRat_tensorBasis_repr_apply, Fin.isValue, cons_val_zero]
    simp only [← map_add, Fin.isValue]
    apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
    revert b
    with_unfolding_all decide

end complexLorentzTensor
