/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
/-!

# Vectors from Lorents group elements

Every element of the Lorentz group defines a Lorentz vector, but it's first column.

-/
noncomputable section

namespace LorentzGroup
open Lorentz
open Vector

/-- The Lorentz vector obtained by acting the Lorentz group element `Λ` on `basis (Sum.inl 0)`. -/
def toVector {d : ℕ} (Λ : LorentzGroup d) : Lorentz.Vector d := Λ • basis (Sum.inl 0)

lemma toVector_mul {d : ℕ} (Λ₁ Λ₂ : LorentzGroup d) :
    toVector (Λ₁ * Λ₂) = Λ₁ • toVector Λ₂ := by
  rw [toVector, toVector]
  simp [mul_smul]

lemma toVector_neg {d : ℕ} (Λ : LorentzGroup d) :
    toVector (-Λ) = -toVector Λ := by
  simp [toVector, neg_smul]

@[simp]
lemma toVector_toCoord_apply {d : ℕ} (Λ : LorentzGroup d)
    (i : Fin 1 ⊕ Fin d) : toCoord (toVector Λ) i = Λ.1 i (Sum.inl 0) := by
  simp [toVector, smul_eq_sum]

lemma toVector_eq_toCoord_symm {d : ℕ} (Λ : LorentzGroup d) :
    toVector Λ = toCoord.symm (fun i => Λ.1 i (Sum.inl 0)) := by
  apply toCoord_injective
  funext i
  simp

@[fun_prop]
lemma toVector_continuous {d : ℕ} : Continuous (toVector (d := d)) := by
  change Continuous (fun Λ => toVector (d := d) Λ)
  conv =>
    enter [1, Λ]
    rw [toVector_eq_toCoord_symm]
  apply Continuous.comp
  · fun_prop
  · refine continuous_pi ?_
    intro i
    refine Continuous.matrix_elem ?_ i (Sum.inl 0)
    fun_prop

lemma toVector_timeComponent {d : ℕ} (Λ : LorentzGroup d) :
    (toVector Λ).timeComponent = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
  simp

@[simp]
lemma toVector_minkowskiProduct_self {d : ℕ} (Λ : LorentzGroup d) :
    ⟪toVector Λ, toVector Λ⟫ₘ = 1 := by
  simp [toVector, smul_eq_sum, minkowskiMatrix.inl_0_inl_0]

lemma one_le_abs_timeComponent {d : ℕ} (Λ : LorentzGroup d) :
    1 ≤ |Λ.1 (Sum.inl 0) (Sum.inl 0)| := by
  rw [← toVector_timeComponent Λ, ← one_le_sq_iff_one_le_abs, ← toVector_minkowskiProduct_self Λ]
  exact minkowskiProduct_self_le_timeComponent_sq (toVector Λ)

lemma toVector_eq_basis_iff_timeComponent_eq_one {d : ℕ} (Λ : LorentzGroup d) :
    toVector Λ = basis (Sum.inl 0) ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  constructor
  · intro h
    rw [← toVector_timeComponent Λ, h]
    simp
  · intro h
    apply toCoord_injective
    funext i
    have h1 := toVector_minkowskiProduct_self Λ
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h1
    simp [h] at h1
    simp [toVector, smul_eq_sum, h]
    match i with
    | Sum.inl 0 => simp [h]
    | Sum.inr j =>
      simp
      rw [← toVector_toCoord_apply]
      change (toVector Λ).spatialPart j = 0
      rw [h1]
      simp

lemma smul_timeComponent_eq_toVector_minkowskiProduct {d : ℕ} (Λ : LorentzGroup d)
    (v : Lorentz.Vector d) :
    (Λ • v).timeComponent = ⟪toVector Λ⁻¹, v⟫ₘ := by
  simp [timeComponent]
  rw [smul_eq_sum]
  simp
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  congr
  · simp [inv_eq_dual, minkowskiMatrix.dual_apply, minkowskiMatrix.inl_0_inl_0]
  · simp [inv_eq_dual]
    rw [← Finset.sum_neg_distrib]
    congr
    funext i
    rw [minkowskiMatrix.dual_apply]
    simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    ring

end LorentzGroup

end
