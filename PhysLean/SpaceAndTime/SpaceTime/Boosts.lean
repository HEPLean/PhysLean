/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
import PhysLean.Relativity.LorentzGroup.Boosts.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Mathematics.FDerivCurry
/-!
# Boosts of space time
-/

noncomputable section

namespace SpaceTime

open Time
open Space
open LorentzGroup

lemma boost_x_smul  (β : ℝ) (hβ : |β| < 1) (x : SpaceTime ) :
    LorentzGroup.boost (d := 3) 0 β hβ • x =
      fun | Sum.inl 0 => γ β * (x (Sum.inl 0) - β * x (Sum.inr 0))
          | Sum.inr 0 => γ β * (x (Sum.inr 0) - β * x (Sum.inl 0))
          | Sum.inr 1=> x (Sum.inr 1)
          | Sum.inr 2=> x (Sum.inr 2) := by
  dsimp
  funext i
  rw [Lorentz.Vector.smul_eq_sum]
  simp [Fin.sum_univ_three]
  fin_cases i
  · simp
    rw [LorentzGroup.boost_inl_0_inr_other _ (by decide),
      LorentzGroup.boost_inl_0_inr_other _ (by decide)]
    simp
    ring
  · simp
    rw [LorentzGroup.boost_inr_inr_other _ (by decide),
      LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    ring
  · simp
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide)]
    simp
  · simp
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide)]
    simp





end SpaceTime

end
