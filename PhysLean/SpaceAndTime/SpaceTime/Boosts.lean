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

## i. Overview

In this module we consider boosts acting on points in space time,and recover simple
formulae for such applications.

Note that the material here currently assumes that the speed of light `c = 1`.

## ii. Key results

- `boost_x_smul` : The action of a boost in the x-direction on a point in space time.

## iii. Table of contents

- A. The action of a boost in the x-direction

## iv. References

See e.g.
- https://en.wikipedia.org/wiki/Lorentz_transformation

-/

noncomputable section

namespace SpaceTime

open Time
open Space
open LorentzGroup
/-!

## A. The action of a boost in the x-direction

We show that boosting in the `x`-direction takes `(t, x, y, z)` to
`(γ (t - β x), γ (x - β t), y, z)`.

-/

lemma boost_x_smul (β : ℝ) (hβ : |β| < 1) (x : SpaceTime) :
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
  · simp only [Fin.isValue, Fin.zero_eta, boost_inl_0_inl_0, boost_inl_0_inr_self, neg_mul]
    rw [LorentzGroup.boost_inl_0_inr_other _ (by decide),
      LorentzGroup.boost_inl_0_inr_other _ (by decide)]
    simp only [Fin.isValue, zero_mul, add_zero]
    ring
  · simp only [Fin.isValue, Fin.zero_eta, boost_inr_self_inl_0, neg_mul, boost_inr_self_inr_self]
    rw [LorentzGroup.boost_inr_inr_other _ (by decide),
      LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp only [Fin.isValue, _root_.one_ne_zero, ↓reduceIte, zero_mul, add_zero, Fin.reduceEq]
    ring
  · simp only [Fin.isValue, Fin.mk_one]
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide)]
    simp
  · simp only [Fin.isValue, Fin.reduceFinMk]
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide)]
    simp

lemma boost_zero_apply_time_space {d : ℕ} {β : ℝ} (hβ : |β| < 1) (c : SpeedOfLight)
    (t : Time) (x : Space d.succ) :
   ((boost (0 : Fin d.succ) β hβ)⁻¹ • (SpaceTime.toTimeAndSpace c).symm (t, x)) =
   (SpaceTime.toTimeAndSpace c).symm
   (γ β * (t.val + β /c * x 0),
    fun | (0 : Fin d.succ) => γ β * (x 0 + c * β * t.val)
        | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩) := by
  funext μ
  rw [boost_inverse, Lorentz.Vector.smul_eq_sum]
  simp
  rw [Fin.sum_univ_succ]
  match μ with
  | Sum.inl 0 =>
    simp
    field_simp
  | Sum.inr ⟨0, h⟩ =>
    simp only [Nat.succ_eq_add_one, Fin.isValue, toTimeAndSpace_symm_apply_inr]
    simp
    field_simp
    ring
  | Sum.inr ⟨Nat.succ n, h⟩ =>
    simp
    rw [Finset.sum_eq_single ⟨n, by omega⟩]
    simp [boost_inr_inr_other]
    simp
    simp [boost_inr_inr_other]
    intro b hb
    left
    simpa [Fin.ext_iff] using hb
    simp


end SpaceTime

end
