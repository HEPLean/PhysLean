/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.Group.Orthochronous
import PhysLean.Relativity.Lorentz.Group.Proper
import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Meta.Informal.Basic
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/
TODO "6VZNK" "Add definition of the restricted Lorentz group."
TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
  combiniation of a boost and a rotation."
TODO "6VZNU" "Prove restricted Lorentz group equivalent to connected component of identity
  of the Lorentz group."

namespace LorentzGroup

/-- The subgroup of the Lorentz group consisting of elements which are proper and orthochronous. -/
-- informal_definition Restricted where
--   deps := [``LorentzGroup, ``IsProper, ``IsOrthochronous]
--   tag := "6VZN7"

/- The restricted Lorentz group is the subset of the Lorentz group which is proper
and orthochronous. -/
def Restricted (d : ℕ) : Set (LorentzGroup d) :=
  { Λ : LorentzGroup d | IsProper Λ ∧ IsOrthochronous Λ }

open Matrix
open minkowskiMatrix

/- The restricted Lorentz group is a subgroup of the Lorentz group. -/
instance restrictedLorentzGroupIsSubgroup {d : ℕ} : Subgroup (LorentzGroup d) where
  carrier := Restricted d
  one_mem' := ⟨
    by rw [IsProper]; exact det_one,
    by rw [IsOrthochronous]; exact zero_le_one
  ⟩
  mul_mem' := by
    rintro Λ₁ Λ₂ ⟨Λ₁_proper, Λ₁_ortho⟩ ⟨Λ₂_proper, Λ₂_ortho⟩
    exact ⟨
      by exact mul_proper_of_proper_proper Λ₁_proper Λ₂_proper,
      by exact mul_othchron_of_othchron_othchron Λ₁_ortho Λ₂_ortho
    ⟩
  inv_mem' := by
    rintro Λ ⟨Λ_proper, Λ_ortho⟩
    change Λ⁻¹ ∈ Restricted d

    have h_eta : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by rfl

    have h_dual : (dual Λ.1) (Sum.inl 0) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
      rw [dual_apply, h_eta, one_mul, mul_one]

    exact ⟨
      by rw [IsProper, inv_eq_dual, det_dual, Λ_proper],
      by rw [IsOrthochronous, inv_eq_dual, h_dual]; exact Λ_ortho
    ⟩

/- The restricted Lorentz group is a group. -/
instance {d : ℕ} : Group (Restricted d) := Subgroup.toGroup (restrictedLorentzGroupIsSubgroup)

end LorentzGroup
