/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.FieldStrength.Basic
import PhysLean.Relativity.Tensors.RealTensor.Derivative
/-!

# Derivative of the field strength tensor

-/

namespace Electromagnetism

namespace FieldStrength
open realLorentzTensor
open IndexNotation
/-!

## Derivative of the field strength

-/
open TensorSpecies
open Tensor
open ComponentIdx
private lemma finsupp_single_prodEquiv (b : (j : Fin (Nat.succ 0 + (Nat.succ 0).succ)) →
      Fin (realLorentzTensor.repDim
        ((Sum.elim (fun (i : Fin 1) => realLorentzTensor.τ (![Color.up] i))
          ![Color.up, Color.up] ∘ ⇑finSumFinEquiv.symm) j))) :
      (Finsupp.single (fun i => Fin.cast
        (by simp : realLorentzTensor.repDim (realLorentzTensor.τ (![Color.up] i)) =
        realLorentzTensor.repDim (![Color.up] i)) ((splitEquiv b).1 i)) (1 : ℝ)) =
      (Finsupp.single (fun | 0 => b 0) 1) := by
  congr
  funext x
  fin_cases x
  rfl

private lemma mapTobasis_prodEquiv (b : (j : Fin (Nat.succ 0 + (Nat.succ 0).succ)) →
    Fin (realLorentzTensor.repDim
      ((Sum.elim (fun (i : Fin 1) => realLorentzTensor.τ (![Color.up] i))
        ![Color.up, Color.up] ∘ ⇑finSumFinEquiv.symm) j))) :
    (fun y => mapToBasis (↑(toElectricMagneticField.symm EM)) y
      (splitEquiv b).2)
    = (fun y => mapToBasis ((toElectricMagneticField.symm EM).1) y
    (fun | (0 : Fin 2) => Fin.cast (by simp) (b 1) | (1 : Fin 2) => Fin.cast (by simp) (b 2))) := by
  ext y
  congr
  funext x
  fin_cases x
  · rfl
  · rfl

lemma derivative_fromElectricMagneticField_repr_diag (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) (j : ℕ) (hj : j < 4) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨j, hj⟩ | 2 => ⟨j, hj⟩) = 0 := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  simp only [Nat.reduceAdd, C_eq_color, Fin.isValue]
  rw [finsupp_single_prodEquiv]
  rw [mapTobasis_prodEquiv]
  trans SpaceTime.deriv μ (fun y => 0) y
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp
  · simp

lemma derivative_fromElectricMagneticField_repr_zero_row (EM : ElectricField × MagneticField)
    (hdiff : Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) (j : ℕ) (hj : j + 1 < 4) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ| 1 => ⟨0, by simp⟩ | 2 => ⟨j + 1, hj⟩) =
    - SpaceTime.deriv μ (fun y => EM.1 y ⟨j, by omega⟩) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  conv_rhs => rw [SpaceTime.neg_deriv_apply]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_zero_col (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) (j : ℕ) (hj : j + 1 < 4) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨j + 1, hj⟩ | 2 => ⟨0, by simp⟩) =
    SpaceTime.deriv μ (fun y => EM.1 y ⟨j, by omega⟩) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_one_two (EM : ElectricField × MagneticField)
    (hdiff : Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨1, by simp⟩ | 2 => ⟨2, by simp⟩) =
    - SpaceTime.deriv μ (fun y => EM.2 y 2) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  conv_rhs => rw [SpaceTime.neg_deriv_apply]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_two_one (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨2, by simp⟩ | 2 => ⟨1, by simp⟩) =
    SpaceTime.deriv μ (fun y => EM.2 y 2) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_one_three (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨1, by simp⟩ | 2 => ⟨3, by simp⟩) =
    SpaceTime.deriv μ (fun y => EM.2 y 1) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_three_one (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨3, by simp⟩ | 2 => ⟨1, by simp⟩) =
    - SpaceTime.deriv μ (fun y => EM.2 y 1) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  conv_rhs => rw [SpaceTime.neg_deriv_apply]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_two_three (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨2, by simp⟩ | 2 => ⟨3, by simp⟩) =
    - SpaceTime.deriv μ (fun y => EM.2 y 3) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  conv_rhs => rw [SpaceTime.neg_deriv_apply]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr_three_two (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis _).repr (∂ (fromElectricMagneticField EM).1 y)
    (fun | 0 => μ | 1 => ⟨3, by simp⟩ | 2 => ⟨2, by simp⟩) =
    SpaceTime.deriv μ (fun y => EM.2 y 3) y := by
  simp only [Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((Tensor.basis _).repr y)) := by
      exact hdiff _
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply]
  rw [finsupp_single_prodEquiv, mapTobasis_prodEquiv]
  congr 1
  · simp only [Fin.isValue, Basis.repr_symm_apply]
    apply congrFun
    apply congrArg
    ext y
    simp [mapToBasis, toElectricMagneticField,
      ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
  · simp only [DFunLike.coe_fn_eq]
    congr
    funext x
    fin_cases x
    simp

lemma derivative_fromElectricMagneticField_repr (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1))
    (y : SpaceTime) :
    (Tensor.basis (S := realLorentzTensor 3) _).repr (∂ (fromElectricMagneticField EM).1 y)
    = Finsupp.equivFunOnFinite.symm fun b =>
      match b 0, b 1, b 2 with
      | μ, 0, 1 => - SpaceTime.deriv μ (fun y => EM.1 y 0) y
      | μ, 0, 2 => - SpaceTime.deriv μ (fun y => EM.1 y 1) y
      | μ, 0, 3 => - SpaceTime.deriv μ (fun y => EM.1 y 2) y
      | μ, 1, 0 => SpaceTime.deriv μ (fun y => EM.1 y 0) y
      | μ, 2, 0 => SpaceTime.deriv μ (fun y => EM.1 y 1) y
      | μ, 3, 0 => SpaceTime.deriv μ (fun y => EM.1 y 2) y
      | μ, 1, 2 => - SpaceTime.deriv μ (fun y => EM.2 y 2) y
      | μ, 1, 3 => SpaceTime.deriv μ (fun y => EM.2 y 1) y
      | μ, 2, 3 => - SpaceTime.deriv μ (fun y => EM.2 y 0) y
      | μ, 2, 1 => SpaceTime.deriv μ (fun y => EM.2 y 2) y
      | μ, 3, 1 => - SpaceTime.deriv μ (fun y => EM.2 y 1) y
      | μ, 3, 2 => SpaceTime.deriv μ (fun y => EM.2 y 0) y
      | _, 0, 0 => 0
      | _, 1, 1 => 0
      | _, 2, 2 => 0
      | _, 3, 3 => 0 := by
  ext b
  have hb : ∃ i j k, b = (fun | 0 => i | 1 => j | 2 => k) := by
    use (b 0), (b 1), (b 2)
    funext x
    fin_cases x <;> rfl
  obtain ⟨b1, b2, b3, rfl⟩ := hb
  match b2, b3 with
  | 0, 1 => exact derivative_fromElectricMagneticField_repr_zero_row EM hdiff y 0 _
  | 0, 2 => exact derivative_fromElectricMagneticField_repr_zero_row EM hdiff y 1 _
  | 0, 3 => exact derivative_fromElectricMagneticField_repr_zero_row EM hdiff y 2 _
  | 1, 0 => exact derivative_fromElectricMagneticField_repr_zero_col EM hdiff y 0 _
  | 2, 0 => exact derivative_fromElectricMagneticField_repr_zero_col EM hdiff y 1 _
  | 3, 0 => exact derivative_fromElectricMagneticField_repr_zero_col EM hdiff y 2 _
  | 1, 2 => exact derivative_fromElectricMagneticField_repr_one_two EM hdiff y
  | 1, 3 => exact derivative_fromElectricMagneticField_repr_one_three EM hdiff y
  | 2, 3 => exact derivative_fromElectricMagneticField_repr_two_three EM hdiff y
  | 2, 1 => exact derivative_fromElectricMagneticField_repr_two_one EM hdiff y
  | 3, 1 => exact derivative_fromElectricMagneticField_repr_three_one EM hdiff y
  | 3, 2 => exact derivative_fromElectricMagneticField_repr_three_two EM hdiff y
  | 0, 0 => exact derivative_fromElectricMagneticField_repr_diag EM hdiff y 0 _
  | 1, 1 => exact derivative_fromElectricMagneticField_repr_diag EM hdiff y 1 _
  | 2, 2 => exact derivative_fromElectricMagneticField_repr_diag EM hdiff y 2 _
  | 3, 3 => exact derivative_fromElectricMagneticField_repr_diag EM hdiff y 3 _

lemma derivative_fromElectricMagneticField (EM : ElectricField × MagneticField)
    (hdiff :Differentiable ℝ (mapToBasis (toElectricMagneticField.symm EM).1)) :
    ∂ (fromElectricMagneticField EM).1 = fun (y : SpaceTime) =>
      (Tensor.basis (S := realLorentzTensor 3) _).repr.symm <|
      Finsupp.equivFunOnFinite.symm fun b =>
      match b 0, b 1, b 2 with
      | μ, 0, 1 => - SpaceTime.deriv μ (fun y => EM.1 y 0) y
      | μ, 0, 2 => - SpaceTime.deriv μ (fun y => EM.1 y 1) y
      | μ, 0, 3 => - SpaceTime.deriv μ (fun y => EM.1 y 2) y
      | μ, 1, 0 => SpaceTime.deriv μ (fun y => EM.1 y 0) y
      | μ, 2, 0 => SpaceTime.deriv μ (fun y => EM.1 y 1) y
      | μ, 3, 0 => SpaceTime.deriv μ (fun y => EM.1 y 2) y
      | μ, 1, 2 => - SpaceTime.deriv μ (fun y => EM.2 y 2) y
      | μ, 1, 3 => SpaceTime.deriv μ (fun y => EM.2 y 1) y
      | μ, 2, 3 => - SpaceTime.deriv μ (fun y => EM.2 y 0) y
      | μ, 2, 1 => SpaceTime.deriv μ (fun y => EM.2 y 2) y
      | μ, 3, 1 => - SpaceTime.deriv μ (fun y => EM.2 y 1) y
      | μ, 3, 2 => SpaceTime.deriv μ (fun y => EM.2 y 0) y
      | _, 0, 0 => 0
      | _, 1, 1 => 0
      | _, 2, 2 => 0
      | _, 3, 3 => 0 := by
  funext y
  apply (Tensor.basis _).repr.injective
  rw [derivative_fromElectricMagneticField_repr EM hdiff y]
  simp

end FieldStrength

end Electromagnetism
