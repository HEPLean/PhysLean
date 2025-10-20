/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
/-!

# The field strength tensor

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-- The Field strength is a tensor `F^μ^ν` which is anti-symmetric.. -/
noncomputable abbrev FieldStrength (d : ℕ := 3) :
    Submodule ℝ (SpaceTime d → ℝT[d, .up, .up]) where
  carrier F := ∀ x, {F x | μ ν = - (F x | ν μ)}ᵀ
  add_mem' {F1 F2} hF1 hF2:= by
    intro x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply, Fin.isValue,
      neg_add_rev, map_add, map_neg]
    conv_lhs => rw [hF1 x, hF2 x]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_neg]
    abel
  smul_mem' {c F hF} := by
    intro x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply, Fin.isValue, map_neg,
      map_smul]
    conv_lhs => rw [hF x]
    simp
  zero_mem' := by
    intro x
    simp

namespace FieldStrength
open TensorSpecies
open Tensor

lemma mem_of_repr {d : ℕ} {F : ℝT[d, .up, .up]}
    (h : ∀ i j, (Tensor.basis _).repr F (fun | 0 => i | 1 => j) =
    - ((Tensor.basis _).repr F (fun | 0 => j | 1 => i))) :
    {F | μ ν = - (F | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_neg, Finsupp.coe_neg,
    Pi.neg_apply, permT_basis_repr_symm_apply]
  have h1 : b = fun | 0 => b 0 | 1 => b 1 := by aesop
  conv_lhs => rw [h1]
  simp only [Tensorial.self_toTensor_apply]
  rw [h]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_inj]
  congr with i
  fin_cases i <;> rfl

lemma repr_symm {d : ℕ} (F : FieldStrength d) (i j : Fin (1 + d))
    (x : SpaceTime d) :
    (Tensor.basis _).repr (F.1 x) (fun | 0 => i | 1 => j)
    = - (Tensor.basis _).repr (F.1 x) (fun | 0 => j | 1 => i) := by
  obtain ⟨F, hF⟩ := F
  simp_all only
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.mem_mk, Fin.isValue,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk] at hF
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  have hf1 := hF x
  simp only [Tensorial.self_toTensor_apply] at hf1
  conv_lhs => rw [hf1]
  rw [Tensor.permT_basis_repr_symm_apply, map_neg]
  simp only [Fin.isValue, Finsupp.coe_neg, Pi.neg_apply, neg_inj]
  congr with x
  aesop

@[simp]
lemma repr_diag_zero {d : ℕ} (F : FieldStrength d) (i : Fin (1 + d))
    (x : SpaceTime d) :
    (Tensor.basis _).repr (F.1 x) (fun | 0 => i | 1 => i)
    = 0 := by
  have hl (a : ℝ) (ha : a = -a) : a = 0 := CharZero.eq_neg_self_iff.mp ha
  exact hl _ <| repr_symm F i i x

open SpaceTime

/-- The field strength from an electric field as an element of `ℝT[d, .up, .up]`. -/
noncomputable def ofElectricFieldAux {d : ℕ} (E : ElectricField d) (x : SpaceTime d) :
    ℝT[d, .up, .up] := (Tensor.basis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
    match b 0, b 1 with
    | 0, ⟨j + 1, hj⟩ => - timeSliceLinearEquiv.symm E x ⟨j, by
      change j + 1 < 1 + d at hj
      omega⟩
    | ⟨j + 1, hj⟩, 0 => timeSliceLinearEquiv.symm E x ⟨j, by
      change j + 1 < 1 + d at hj
      omega⟩
    | _, _ => 0

lemma timeSliceLinearEquiv_ofElectricFieldAux {d : ℕ} (E : ElectricField d) (t : Time)
    (x : Space d) :
    timeSliceLinearEquiv (ofElectricFieldAux E) t x =
    ((Tensor.basis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
      match b 0, b 1 with
      | 0, ⟨j + 1, hj⟩ => - E t x ⟨j, by
        change j + 1 < 1 + d at hj
        omega⟩
      | ⟨j + 1, hj⟩, 0 => E t x ⟨j, by
        change j + 1 < 1 + d at hj
        omega⟩
      | _, _ => 0) := by
  simp [timeSliceLinearEquiv, timeSlice, ofElectricFieldAux]

/-- The field strength from an eletric field. -/
noncomputable def ofElectricField {d : ℕ} : ElectricField d →ₗ[ℝ] FieldStrength d where
  toFun E := by
    refine ⟨fun x ↦ ofElectricFieldAux E x, ?_⟩
    intro x
    apply mem_of_repr
    intro i j
    match i, j with
    | 0, 0 => simp [ofElectricFieldAux]
    | ⟨0, h0⟩, ⟨Nat.succ j, hj⟩ => simp [- Nat.succ_eq_add_one, -Fin.mk_zero', ofElectricFieldAux]
    | ⟨j + 1, hj⟩, ⟨0, h0⟩ => simp [- Nat.succ_eq_add_one, -Fin.mk_zero', ofElectricFieldAux]
    | ⟨j + 1, hj⟩, ⟨k + 1, hk⟩ => simp [- Nat.succ_eq_add_one, -Fin.mk_zero', ofElectricFieldAux]
  map_add' E1 E2 := by
    ext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
    apply (Tensor.basis _).repr.injective
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ofElectricFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_add, Pi.add_apply, PiLp.add_apply, neg_add_rev,
      Basis.repr_symm_apply, Basis.repr_linearCombination, AddMemClass.mk_add_mk]
    apply Finsupp.equivFunOnFinite.injective
    conv_rhs => rw [Finsupp.equivFunOnFinite]
    simp only [Fin.isValue, Equiv.apply_symm_apply, Set.Finite.toFinset_setOf, ne_eq,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Finsupp.coe_add, Finsupp.coe_mk]
    funext b
    simp only [Fin.isValue, Pi.add_apply]
    split <;> abel
  map_smul' c E := by
    ext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
    apply (Tensor.basis _).repr.injective <| Finsupp.equivFunOnFinite.injective _
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ofElectricFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, PiLp.smul_apply,
      smul_eq_mul, Basis.repr_symm_apply, Basis.repr_linearCombination, Equiv.apply_symm_apply,
      RingHom.id_apply, SetLike.mk_smul_mk, map_smul]
    ext x_1 : 1
    simp only [Fin.isValue, Finsupp.equivFunOnFinite_apply, Finsupp.coe_smul,
      Finsupp.coe_equivFunOnFinite_symm, Pi.smul_apply, smul_eq_mul]
    split <;> simp

lemma ofElectricField_coe {d : ℕ} (E : ElectricField d) :
    (ofElectricField E).1 = ofElectricFieldAux E := by
  rfl

/-- The field strength from a magnetic field as an element of `ℝT[3, .up, .up]`.
  This is only defined here for 4d spacetime. -/
noncomputable def ofMagneticFieldAux (B : MagneticField) (x : SpaceTime 3) :
      ℝT[3, .up, .up] := (Tensor.basis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
    match b 0, b 1 with
    | 1, 2 => - timeSliceLinearEquiv.symm B x 2
    | 1, 3 => timeSliceLinearEquiv.symm B x 1
    | 2, 3 => - timeSliceLinearEquiv.symm B x 0
    | 2, 1 => timeSliceLinearEquiv.symm B x 2
    | 3, 1 => - timeSliceLinearEquiv.symm B x 1
    | 3, 2 => timeSliceLinearEquiv.symm B x 0
    | _, _ => 0

lemma timeSliceLinearEquiv_ofMagneticFieldAux (B : MagneticField) (t : Time)
    (x : Space 3) :
    timeSliceLinearEquiv (ofMagneticFieldAux B) t x =
    ((Tensor.basis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
      match b 0, b 1 with
      | 1, 2 => - B t x 2
      | 1, 3 => B t x 1
      | 2, 3 => - B t x 0
      | 2, 1 => B t x 2
      | 3, 1 => - B t x 1
      | 3, 2 => B t x 0
      | _, _ => 0) := by
  simp [timeSliceLinearEquiv, timeSlice, ofMagneticFieldAux]

/-- The field strength from a magnetic field. -/
noncomputable def ofMagneticField : MagneticField →ₗ[ℝ] FieldStrength where
  toFun B := by
    refine ⟨fun x => ofMagneticFieldAux B x, fun x => ?_⟩
    simp only [Fin.isValue]
    apply mem_of_repr
    intro i j
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ofMagneticFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Basis.repr_symm_apply,
      Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
    fin_cases i <;> fin_cases j <;> simp
  map_add' B1 B2 := by
    ext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.coe_add, Pi.add_apply]
    apply (Tensor.basis _).repr.injective
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ofMagneticFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, PiLp.add_apply,
      neg_add_rev, Basis.repr_symm_apply, Basis.repr_linearCombination, map_add]
    apply Finsupp.equivFunOnFinite.injective
    conv_rhs => rw [Finsupp.equivFunOnFinite]
    simp only [Fin.isValue, Equiv.apply_symm_apply, Set.Finite.toFinset_setOf, ne_eq,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Finsupp.coe_add, Finsupp.coe_mk]
    funext b
    simp only [Fin.isValue, Pi.add_apply]
    split <;> abel
  map_smul' c B := by
    ext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
    apply (Tensor.basis _).repr.injective <| Finsupp.equivFunOnFinite.injective _
    simp [ofMagneticFieldAux]
    ext x_1 : 1
    simp only [Fin.isValue, Finsupp.equivFunOnFinite_apply, Finsupp.coe_smul,
      Finsupp.coe_equivFunOnFinite_symm, Pi.smul_apply, smul_eq_mul]
    split <;> simp

lemma ofMagneticField_coe (B : MagneticField) :
    (ofMagneticField B).1 = ofMagneticFieldAux B := by
  rfl

/-- The electric field given a field strength. -/
noncomputable def electricField {d : ℕ} : FieldStrength d →ₗ[ℝ] ElectricField d where
  toFun F := fun t x j => (Tensor.basis _).repr
    (timeSliceLinearEquiv F.1 t x) (fun | 0 => ⟨j + 1, by simp; omega⟩ | 1 => 0)
  map_add' F1 F2 := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.coe_add, Pi.add_apply,
      map_add, Fin.isValue, Matrix.cons_val_zero, Finsupp.coe_add]
    rfl
  map_smul' c F := by
    simp [Nat.succ_eq_add_one, Nat.reduceAdd, SetLike.val_smul, Pi.smul_apply,
      map_smul, Fin.isValue, Matrix.cons_val_zero, Finsupp.coe_smul, smul_eq_mul, RingHom.id_apply]
    rfl

lemma electricField_apply {d : ℕ} (F : FieldStrength d) (t : Time) (x : Space d) (j : Fin d) :
    electricField F t x j = (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x)
      (fun | 0 => ⟨j + 1, by simp; omega⟩ | 1 => 0) := by
  rfl

lemma timeSliceLinearEquiv_symm_electricField {d : ℕ} (F : FieldStrength d) :
    timeSliceLinearEquiv.symm (electricField F) = fun x (j : Fin d) =>
    (Tensor.basis _).repr (F.1 x) (fun | 0 => ⟨j + 1, by simp; omega⟩ | 1 => 0) := by
  rw [LinearEquiv.symm_apply_eq]
  aesop

@[simp]
lemma electricField_ofElectricField {d : ℕ} (E : ElectricField d) :
    electricField (ofElectricField E) = E := by
  ext x j
  rw [electricField_apply, ofElectricField_coe, timeSliceLinearEquiv_ofElectricFieldAux]
  aesop

/-- The magnetic field given a field strength. -/
noncomputable def magneticField : FieldStrength →ₗ[ℝ] MagneticField where
  toFun F := fun t x j =>
    match j with
    | 0 =>
      (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 3| 1 => 2)
    | 1 =>
      (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 1| 1 => 3)
    | 2 =>
      (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 2| 1 => 1)
  map_add' F1 F2 := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.coe_add, Pi.add_apply,
      map_add, Fin.isValue, Finsupp.coe_add]
    funext t x j
    fin_cases j <;> simp
  map_smul' c F := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, SetLike.val_smul, Pi.smul_apply,
      map_smul, Fin.isValue, Finsupp.coe_smul, smul_eq_mul, RingHom.id_apply]
    funext t x j
    fin_cases j <;> simp

lemma magneticField_apply (F : FieldStrength) (t : Time) (x : Space) (j : Fin 3) :
    magneticField F t x j = match j with
      | 0 => (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 3| 1 => 2)
      | 1 => (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 1| 1 => 3)
      | 2 => (Tensor.basis _).repr (timeSliceLinearEquiv F.1 t x) (fun | 0 => 2| 1 => 1) := by
  rfl

lemma timeSliceLinearEquiv_symm_magneticField (F : FieldStrength) :
    timeSliceLinearEquiv.symm (magneticField F) = fun x j =>
    match j with
    | 0 =>
      (Tensor.basis _).repr (F.1 x) (fun | 0 => 3| 1 => 2)
    | 1 =>
      (Tensor.basis _).repr (F.1 x) (fun | 0 => 1| 1 => 3)
    | 2 =>
      (Tensor.basis _).repr (F.1 x) (fun | 0 => 2| 1 => 1) := by
  rw [LinearEquiv.symm_apply_eq]
  ext t x j
  rw [magneticField_apply]
  fin_cases j <;> rfl

@[simp]
lemma magneticField_ofMagneticField (B : MagneticField) :
    magneticField (ofMagneticField B) = B := by
  ext t x j
  rw [magneticField_apply, ofMagneticField_coe, timeSliceLinearEquiv_ofMagneticFieldAux]
  fin_cases j
  all_goals
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Basis.repr_symm_apply, Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.zero_eta]
    rfl

@[simp]
lemma electricField_ofMagneticField (B : MagneticField) :
    electricField (ofMagneticField B) = 0 := by
  ext x j
  rw [electricField_apply, ofMagneticField_coe, timeSliceLinearEquiv_ofMagneticFieldAux]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Basis.repr_symm_apply,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.mk_eq_one,
    Fin.reduceEq, imp_self, implies_true, zero_ne_one]
  rfl

@[simp]
lemma magneticField_ofElectricField (E : ElectricField) :
    magneticField (ofElectricField E) = 0 := by
  ext t x j
  rw [magneticField_apply, ofElectricField_coe, timeSliceLinearEquiv_ofElectricFieldAux]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Basis.repr_symm_apply,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
  fin_cases j <;> rfl

lemma eq_ofElectricField_add_ofMagneticField (F : FieldStrength) : F =
    ofElectricField (electricField F) + ofMagneticField (magneticField F) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  ext x
  simp only [Submodule.coe_add, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply]
  apply (Tensor.basis _).repr.injective <| Finsupp.equivFunOnFinite.injective _
  conv_rhs => rw [Finsupp.equivFunOnFinite]
  simp only [Set.Finite.toFinset_setOf, ne_eq, ofElectricField, Nat.succ_eq_add_one,
    Nat.reduceAdd, ofElectricFieldAux, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk, ofMagneticField,
    ofMagneticFieldAux, map_add, Basis.repr_linearCombination, Equiv.coe_fn_mk, Finsupp.coe_add,
    Finsupp.coe_equivFunOnFinite_symm]
  funext b
  simp only [Finsupp.equivFunOnFinite_apply, Fin.isValue, Pi.add_apply]
  have h1 : ∃ i j, b = (fun | 0 => i | 1 => j) := ⟨(b 0), (b 1), by aesop⟩
  obtain ⟨i, j, rfl⟩ := h1
  simp only [Fin.isValue]
  match i, j with
  | (1 : Fin 4), (2 : Fin 4) =>
    simpa [timeSliceLinearEquiv_symm_magneticField] using repr_symm F 1 2 x
  | (1 : Fin 4), (3 : Fin 4) =>
    simp only [Fin.isValue, timeSliceLinearEquiv_symm_magneticField, Nat.succ_eq_add_one,
      Nat.reduceAdd, zero_add]
    rfl
  | (2 : Fin 4), (3 : Fin 4) =>
    simpa [timeSliceLinearEquiv_symm_magneticField] using repr_symm F 2 3 x
  | (2 : Fin 4), (1 : Fin 4) =>
    simp only [Fin.isValue, timeSliceLinearEquiv_symm_magneticField, Nat.succ_eq_add_one,
      Nat.reduceAdd, zero_add]
    rfl
  | (3 : Fin 4), (1 : Fin 4) =>
    simpa [timeSliceLinearEquiv_symm_magneticField] using repr_symm F 3 1 x
  | (3 : Fin 4), (2 : Fin 4) =>
    simp only [Fin.isValue, timeSliceLinearEquiv_symm_magneticField, Nat.succ_eq_add_one,
      Nat.reduceAdd, zero_add]
    rfl
  | ⟨0, h0⟩, ⟨0, h0'⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, Fin.zero_eta, Matrix.cons_val_one, add_zero]
    exact repr_diag_zero F 0 x
  | ⟨1, h0⟩, ⟨1, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    exact repr_diag_zero F 1 x
  | ⟨2, h0⟩, ⟨2, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    exact repr_diag_zero F 2 x
  | ⟨3, h0⟩, ⟨3, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    exact repr_diag_zero F 3 x
  | ⟨0, h0⟩, ⟨1, h1⟩ =>
    simpa [timeSliceLinearEquiv_symm_electricField] using repr_symm F 0 1 x
  | ⟨0, h0⟩, ⟨2, h1⟩ =>
    simpa [timeSliceLinearEquiv_symm_electricField] using repr_symm F 0 2 x
  | ⟨0, h0⟩, ⟨3, h1⟩ =>
    simpa [timeSliceLinearEquiv_symm_electricField] using repr_symm F 0 3 x
  | ⟨1, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.mk_one,
      Matrix.cons_val_one, Fin.zero_eta, timeSliceLinearEquiv_symm_electricField,
      Nat.succ_eq_add_one, Fin.val_zero, zero_add, add_zero]
    rfl
  | ⟨2, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      timeSliceLinearEquiv_symm_electricField, Nat.succ_eq_add_one, Fin.val_one,
      add_zero]
    rfl
  | ⟨3, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_one, Fin.zero_eta, timeSliceLinearEquiv_symm_electricField,
      Nat.succ_eq_add_one, Fin.val_two, add_zero]
    rfl

/-- The isomorphism between the field strength and the electric and magnetic fields. -/
noncomputable def toElectricMagneticField : FieldStrength ≃ₗ[ℝ] ElectricField × MagneticField where
  toFun F := ⟨electricField F, magneticField F⟩
  invFun EM := ofElectricField EM.1 + ofMagneticField EM.2
  map_add' F1 F2 := by simp
  map_smul' c F := by simp
  left_inv F := (eq_ofElectricField_add_ofMagneticField F).symm
  right_inv EM := by simp

/-- The field strength from an electric and magnetic field. -/
noncomputable abbrev fromElectricMagneticField := toElectricMagneticField.symm

/-- The field strength from an electric and magnetic field written in terms of a basis. -/
lemma fromElectricMagneticField_repr (EM : ElectricField × MagneticField) (y : SpaceTime) :
    (Tensor.basis _).repr ((fromElectricMagneticField EM).1 y) =
    Finsupp.equivFunOnFinite.symm fun b =>
      match b 0, b 1 with
      | 0, 1 => - timeSliceLinearEquiv.symm EM.1 y 0
      | 0, 2 => - timeSliceLinearEquiv.symm EM.1 y 1
      | 0, 3 => - timeSliceLinearEquiv.symm EM.1 y 2
      | 1, 0 => timeSliceLinearEquiv.symm EM.1 y 0
      | 2, 0 => timeSliceLinearEquiv.symm EM.1 y 1
      | 3, 0 => timeSliceLinearEquiv.symm EM.1 y 2
      | 1, 2 => - timeSliceLinearEquiv.symm EM.2 y 2
      | 1, 3 => timeSliceLinearEquiv.symm EM.2 y 1
      | 2, 3 => - timeSliceLinearEquiv.symm EM.2 y 0
      | 2, 1 => timeSliceLinearEquiv.symm EM.2 y 2
      | 3, 1 => - timeSliceLinearEquiv.symm EM.2 y 1
      | 3, 2 => timeSliceLinearEquiv.symm EM.2 y 0
      | _, _ => 0 := by
  simp only [fromElectricMagneticField, toElectricMagneticField, ofElectricField,
    ofElectricFieldAux, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk, ofMagneticField, ofMagneticFieldAux,
    AddMemClass.mk_add_mk, LinearEquiv.coe_symm_mk, Pi.add_apply, map_add,
    Basis.repr_linearCombination]
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finsupp.coe_add,
    Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply, Finsupp.equivFunOnFinite_symm_apply_toFun]
  have hb : ∃ i j, b = (fun | 0 => i | 1 => j) := ⟨(b 0), (b 1), by aesop⟩
  obtain ⟨i, j, rfl⟩ := hb
  fin_cases i <;> fin_cases j <;> simp

TODO "6V2OU" "Define the dual field strength."

end FieldStrength

end Electromagnetism
