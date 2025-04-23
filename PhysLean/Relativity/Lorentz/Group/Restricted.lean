/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic
import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Relativity.Lorentz.Group.Orthochronous
import PhysLean.Relativity.Lorentz.Group.Proper

/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/

TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
  combiniation of a boost and a rotation."
TODO "6VZNU" "Prove restricted Lorentz group equivalent to connected component of identity
  of the Lorentz group."

namespace LorentzGroup

/-- The restricted Lorentz group comprises the proper and orthochronous elements of the
Lorentz group. -/
def Restricted (d : ℕ) : Set (LorentzGroup d) :=
  { Λ : LorentzGroup d | IsProper Λ ∧ IsOrthochronous Λ }

open Matrix
open minkowskiMatrix

/- The restricted Lorentz group is a subgroup of the Lorentz group. -/
instance restrictedLorentzGroupIsSubgroup {d : ℕ} : Subgroup (LorentzGroup d) where
  carrier := Restricted d
  one_mem' := ⟨
    by rw [IsProper]; exact det_one,
    by rw [IsOrthochronous]; exact zero_le_one⟩
  mul_mem' := by
    rintro Λ₁ Λ₂ ⟨Λ₁_proper, Λ₁_ortho⟩ ⟨Λ₂_proper, Λ₂_ortho⟩
    exact ⟨
      by exact mul_proper_of_proper_proper Λ₁_proper Λ₂_proper,
      by exact mul_othchron_of_othchron_othchron Λ₁_ortho Λ₂_ortho⟩
  inv_mem' := by
    rintro Λ ⟨Λ_proper, Λ_ortho⟩

    have h_η₀₀ : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by rfl
    have h_dual : (dual Λ.1) (Sum.inl 0) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
      rw [dual_apply, h_η₀₀, one_mul, mul_one]

    exact ⟨
      by rw [IsProper, inv_eq_dual, det_dual, Λ_proper],
      by rw [IsOrthochronous, inv_eq_dual, h_dual]; exact Λ_ortho⟩

/- The restricted Lorentz group is a group. -/
instance {d : ℕ} : Group (Restricted d) := Subgroup.toGroup (restrictedLorentzGroupIsSubgroup)

end LorentzGroup
