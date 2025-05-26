/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import PhysLean.StringTheory.FTheory.SU5U1.Fluxes.Basic
/-!

## Constraints on chiral indices from the condition of no chiral exotics

On the types `FluxesFive` and `FluxesTen`, we have the conditions `NoExotics`,
corresponding to the non-existence of chiral exotics in the spectrum.

These conditions lead to constraints of the chiral indices of the SM representations.
For example:
- They must be non-negative.
- They must be less than or equal to `3`.

This module proves thes constraints.

-/
namespace FTheory

namespace SU5U1

namespace FluxesFive

/-- The chiral indices of the representations `D = (bar 3,1)_{1/3}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma chiralIndicesOfD_noneg_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) : 0 ≤ ci := by
  have hF1 := hF.2.2.2
  simp [numAntiChiralD] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      rw [Multiset.eq_zero_iff_forall_not_mem]
      simp only [Multiset.mem_filter, not_and, not_lt, not_forall, Classical.not_imp, not_le, s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

/-- The sum of the chiral indices of the representations `D = (bar 3,1)_{1/3}` is equal
  to `3` in the presences of no exotics. -/
lemma chiralIndicesOfD_sum_eq_three_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.chiralIndicesOfD.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfD +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfD)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfD)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralD + F.numAntiChiralD = 3
  rw [hF.2.2.2, hF.2.2.1]
  simp

/-- The chiral indices of the representation `D = (bar 3,1)_{1/3}` are less then
  or equal to `3`. -/
lemma chiralIndicesOfD_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfD)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfD)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    intro i hi h3
    exact chiralIndicesOfD_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfD.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfD]
    simp [s, s']
  rw [F.chiralIndicesOfD_sum_eq_three_of_noExotics hF] at hsum'
  omega

end FluxesFive

namespace FluxesTen

end FluxesTen

end SU5U1

end FTheory
