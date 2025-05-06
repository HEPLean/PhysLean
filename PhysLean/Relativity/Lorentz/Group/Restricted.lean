/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic
import PhysLean.Relativity.Lorentz.Group.Orthochronous
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/

TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
  combiniation of a boost and a rotation."
TODO "6VZNU" "Prove restricted Lorentz group equivalent to connected component of identity
  of the Lorentz group."

namespace LorentzGroup

open Matrix
open minkowskiMatrix

/-- The restricted Lorentz group comprises the proper and orthochronous elements of the
Lorentz group. -/
def restricted (d : ℕ) : Subgroup (LorentzGroup d) where
  carrier := { Λ : LorentzGroup d | IsProper Λ ∧ IsOrthochronous Λ }
  one_mem' := ⟨
    by rw [IsProper]; exact det_one,
    by rw [IsOrthochronous]; exact zero_le_one⟩
  mul_mem' := by
    rintro Λ₁ Λ₂ ⟨Λ₁_proper, Λ₁_ortho⟩ ⟨Λ₂_proper, Λ₂_ortho⟩
    exact ⟨
      by exact mul_isProper_of_isProper_isProper Λ₁_proper Λ₂_proper,
      by exact mul_othchron_of_othchron_othchron Λ₁_ortho Λ₂_ortho⟩
  inv_mem' := by
    rintro Λ ⟨Λ_proper, Λ_ortho⟩

    have h_η₀₀ : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by rfl
    have h_dual : (dual Λ.1) (Sum.inl 0) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
      rw [dual_apply, h_η₀₀, one_mul, mul_one]

    exact ⟨
      by rw [IsProper, inv_eq_dual, det_dual, Λ_proper],
      by rw [IsOrthochronous, inv_eq_dual, h_dual]; exact Λ_ortho⟩

/-- The restricted Lorentz group is a normal subgroup of the Lorentz group. -/
lemma restricted_normal_subgroup {d : ℕ} : (restricted d).Normal := by
  have h_proper {Λ P : LorentzGroup d} (hP : IsProper P) : IsProper (Λ * P * Λ⁻¹) := by
    simp only [IsProper, lorentzGroupIsGroup_mul_coe, det_mul]
    rw [hP, mul_one, ← det_mul, coe_inv, mul_inv_of_invertible, det_one]
  have h_ortho {Λ O : LorentzGroup d} (hO : IsOrthochronous O) : IsOrthochronous (Λ * O * Λ⁻¹) := by
    by_cases hΛ : IsOrthochronous Λ
    · exact mul_othchron_of_othchron_othchron
        (mul_othchron_of_othchron_othchron hΛ hO)
        (IsOrthochronous.iff_inv_isOrthochronous.mp hΛ)
    · exact mul_othchron_of_not_othchron_not_othchron
        (mul_not_othchron_of_not_othchron_othchron hΛ hO)
        (IsOrthochronous.iff_inv_isOrthochronous.not.mp hΛ)
  constructor
  rintro R ⟨R_proper, R_ortho⟩ Λ
  exact ⟨h_proper R_proper, h_ortho R_ortho⟩

/-
  Work in progress: Prove that the restricted Lorentz group is the identity component of the
  Lorentz group.
-/

open TopologicalSpace

/-- The group `ℤ₂`. -/
local notation "ℤ₂" => Multiplicative (ZMod 2)

noncomputable def lorentzMap {d : ℕ} : ContinuousMonoidHom (LorentzGroup d) (ℤ₂ × ℤ₂) where
  toFun := λ Λ => (detRep Λ, orthchroRep Λ)
  map_one' := by sorry
  map_mul' := by sorry
  continuous_toFun := by sorry

lemma lorentzMap_Kernel {d : ℕ} : (@lorentzMap d).ker = restricted d := by sorry
lemma lorentzMap_Identity_Connected {d : ℕ} : IsConnected ({(1, 1)} : Set (ℤ₂ × ℤ₂)) := by sorry
lemma lorentzMap_IsInjective {d : ℕ} : Function.Injective (@lorentzMap d) := by sorry
lemma lorentzMap_IsOpen {d : ℕ} : IsOpenMap (@lorentzMap d) := by sorry
lemma lorentzMap_Subset {d : ℕ} : ({(1, 1)} : Set (ℤ₂ × ℤ₂)) ⊆ Set.range (@lorentzMap d) := by sorry

lemma restricted.IsConnected {d : ℕ} : IsConnected (restricted d : Set (LorentzGroup d)) := by
  rw [← lorentzMap_Kernel]
  exact @IsConnected.preimage_of_isOpenMap (LorentzGroup d) (ℤ₂ × ℤ₂) _ _ {(1, 1)}
    (@lorentzMap_Identity_Connected d)
    (@lorentzMap d)
    (lorentzMap_IsInjective)
    (lorentzMap_IsOpen)
    (lorentzMap_Subset)

lemma restricted_eq_identity_component {d : ℕ} :
    (restricted d) = connectedComponent (1 : LorentzGroup d) := by
  ext x
  constructor
  · intro hx
    have h_id : 1 ∈ restricted d := by simp [restricted, IsOrthochronous]
    exact IsConnected.subset_connectedComponent (@restricted.IsConnected d) h_id hx
  · intro h
    exact ⟨(isProper_on_connected_component h).mp id_IsProper,
           (isOrthochronous_on_connected_component h).mp id_IsOrthochronous⟩

end LorentzGroup
