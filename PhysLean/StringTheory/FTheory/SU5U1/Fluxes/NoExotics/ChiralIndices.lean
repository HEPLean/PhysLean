/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Fluxes.Basic
import Mathlib.Tactic.FinCases
/-!

## Constraints on chiral indices from the condition of no chiral exotics

On the types `FluxesFive` and `FluxesTen`, we have the conditions `NoExotics`,
corresponding to the non-existence of chiral exotics in the spectrum.

These conditions lead to constraints of the chiral indices of the SM representations.
For example:
- They must be non-negative.
- They must be less than or equal to `3`.
- The non-zero chiral indices must be one of the following multisets `{1, 1, 1}`, `{1, 2}`, `{3}`.

This module proves these constraints.

-/
namespace FTheory

namespace SU5U1

namespace FluxesFive

/-!

## Constraints on the chiral indices of `D = (bar 3,1)_{1/3}`

-/

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
    exact fun i hi _ => chiralIndicesOfD_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfD.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfD]
    simp [s, s']
  rw [F.chiralIndicesOfD_sum_eq_three_of_noExotics hF] at hsum'
  omega

lemma mem_chiralIndicesOfD_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfD_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfD_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma chiralIndicesOfD_subset_sum_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (S : Multiset (ℤ × ℤ))
    (hSle : S ≤ F) : (S.map (fun x => x.1)).sum ≤ 3 := by
  rw [← F.chiralIndicesOfD_sum_eq_three_of_noExotics hF]
  have h1 : F = S + (F - S) := Eq.symm (add_tsub_cancel_of_le hSle)
  have hpos : 0 ≤ ((F - S).map (fun x => x.1)).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp at hx
    obtain ⟨N, h⟩ := hx
    have hl : (x, N) ∈ F := by
      apply Multiset.mem_of_subset (t := F) at h
      exact h
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    have hx : x ∈ F.chiralIndicesOfD := by
      simp [chiralIndicesOfD]
      use N
    exact chiralIndicesOfD_noneg_of_noExotics F hF x hx
  rw [chiralIndicesOfD]
  rw [h1]
  rw [Multiset.map_add, Multiset.sum_add]
  omega

/-!

## Constraints on the chiral indices of `L = (1,2)_{-1/2}`

-/

/-- The chiral indices of the representations `L = (1,2)_{-1/2}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma chiralIndicesOfL_noneg_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : 0 ≤ ci := by
  have hF1 := hF.2.1
  simp [numAntiChiralL] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL)
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

/-- The sum of the chiral indices of the representations `L = (1,2)_{-1/2}` is equal
  to `3` in the presences of no exotics. -/
lemma chiralIndicesOfL_sum_eq_three_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.chiralIndicesOfL.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfL +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfL)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfL)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralL + F.numAntiChiralL = 3
  rw [hF.2.1, hF.1]
  simp

/-- The chiral indices of the representation `L = (1,2)_{-1/2}` are less then
  or equal to `3`. -/
lemma chiralIndicesOfL_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfL)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfL)
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
    exact fun i hi _ => chiralIndicesOfL_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfL.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfL]
    simp [s, s']
  rw [F.chiralIndicesOfL_sum_eq_three_of_noExotics hF] at hsum'
  omega

lemma mem_chiralIndicesOfL_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfL_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfL_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma chiralIndicesOfL_subset_sum_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (S : Multiset (ℤ × ℤ))
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  rw [← F.chiralIndicesOfL_sum_eq_three_of_noExotics hF]
  have h1 : F = S + (F - S) := Eq.symm (add_tsub_cancel_of_le hSle)
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 + x.2))).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp at hx
    obtain ⟨M, N, hmem, hsum⟩ := hx
    have hl : (M, N) ∈ F := by
      apply Multiset.mem_of_subset (t := F) at hmem
      exact hmem
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    have hx : x ∈ F.chiralIndicesOfL := by
      simp [chiralIndicesOfL]
      use M, N
    exact chiralIndicesOfL_noneg_of_noExotics F hF x hx
  rw [chiralIndicesOfL]
  rw [h1]
  rw [Multiset.map_add, Multiset.sum_add]
  omega

end FluxesFive

namespace FluxesTen

/-!

## Constraints on the chiral indices of `Q = (3,2)_{1/6}`

-/

/-- The chiral indices of the representations `Q = (3,2)_{1/6}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma chiralIndicesOfQ_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : 0 ≤ ci := by
  have hF1 := hF.2.1
  simp [numAntiChiralQ] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ)
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

/-- The sum of the chiral indices of the representations `Q = (3,2)_{1/6}` is equal
  to `3` in the presences of no exotics. -/
lemma chiralIndicesOfQ_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfQ.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfQ +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfQ)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfQ)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralQ + F.numAntiChiralQ = 3
  rw [hF.2.1, hF.1]
  simp

/-- The chiral indices of the representation `Q = (3,2)_{1/6}` are less then
  or equal to `3`. -/
lemma chiralIndicesOfQ_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfQ)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfQ)
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
    exact fun i hi _ => chiralIndicesOfQ_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfQ.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfQ]
    simp [s, s']
  rw [F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF] at hsum'
  omega

lemma mem_chiralIndicesOfQ_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfQ_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfQ_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma chiralIndicesOfQ_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset (ℤ × ℤ))
    (hSle : S ≤ F) : (S.map (fun x => x.1)).sum ≤ 3 := by
  rw [← F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF]
  have h1 : F = S + (F - S) := Eq.symm (add_tsub_cancel_of_le hSle)
  have hpos : 0 ≤ ((F - S).map (fun x => x.1)).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp at hx
    obtain ⟨N, h⟩ := hx
    have hl : (x, N) ∈ F := by
      apply Multiset.mem_of_subset (t := F) at h
      exact h
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    have hx : x ∈ F.chiralIndicesOfQ := by
      simp [chiralIndicesOfQ]
      use N
    exact chiralIndicesOfQ_noneg_of_noExotics F hF x hx
  rw [chiralIndicesOfQ]
  rw [h1]
  rw [Multiset.map_add, Multiset.sum_add]
  omega

/-!

## Constraints on the chiral indices of `U = (bar 3,1)_{-2/3}`

-/

/-- The chiral indices of the representations `U = (bar 3,1)_{-2/3}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma chiralIndicesOfU_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : 0 ≤ ci := by
  have hF1 := hF.2.2.2
  simp [numAntiChiralU] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU)
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

/-- The sum of the chiral indices of the representations `U = (bar 3,1)_{-2/3}` is equal
  to `3` in the presences of no exotics. -/
lemma chiralIndicesOfU_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfU.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfU +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfU)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfU)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralU + F.numAntiChiralU = 3
  rw [hF.2.2.2.1, hF.2.2.1]
  simp

/-- The chiral indices of the representation `U = (bar 3,1)_{-2/3}` are less then
  or equal to `3`. -/
lemma chiralIndicesOfU_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfU)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfU)
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
    exact fun i hi _ => chiralIndicesOfU_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfU.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfU]
    simp [s, s']
  rw [F.chiralIndicesOfU_sum_eq_three_of_noExotics hF] at hsum'
  omega

lemma mem_chiralIndicesOfU_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfU_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfU_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma chiralIndicesOfU_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset (ℤ × ℤ))
    (hSle : S ≤ F) : (S.map (fun x => (x.1 - x.2))).sum ≤ 3 := by
  rw [← F.chiralIndicesOfU_sum_eq_three_of_noExotics hF]
  have h1 : F = S + (F - S) := Eq.symm (add_tsub_cancel_of_le hSle)
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 - x.2))).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp at hx
    obtain ⟨M, N, hmem, hsum⟩ := hx
    have hl : (M, N) ∈ F := by
      apply Multiset.mem_of_subset (t := F) at hmem
      exact hmem
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    have hx : x ∈ F.chiralIndicesOfU := by
      simp [chiralIndicesOfU]
      use M, N
    exact chiralIndicesOfU_noneg_of_noExotics F hF x hx
  rw [chiralIndicesOfU]
  rw [h1]
  rw [Multiset.map_add, Multiset.sum_add]
  omega

/-!

## Constraints on the chiral indices of `E = (1,1)_{1}`

-/

lemma chiralIndicesOfE_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : 0 ≤ ci := by
  have hF1 := hF.2.2.2.2.2
  simp [numAntiChiralE] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE)
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

/-- The sum of the chiral indices of the representations `E = (1,1)_{1}` is equal
  to `3` in the presences of no exotics. -/
lemma chiralIndicesOfE_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfE.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfE +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfE)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfE)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralE + F.numAntiChiralE = 3
  rw [hF.2.2.2.2.1, hF.2.2.2.2.2]
  simp

/-- The chiral indices of the representation `E = (1,1)_{1}` are less then
  or equal to `3`. -/
lemma chiralIndicesOfE_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfE)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfE)
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
    exact fun i hi _ => chiralIndicesOfE_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfE.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfE]
    simp [s, s']
  rw [F.chiralIndicesOfE_sum_eq_three_of_noExotics hF] at hsum'
  omega

lemma mem_chiralIndicesOfE_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfE_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfE_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma chiralIndicesOfE_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset (ℤ × ℤ))
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  rw [← F.chiralIndicesOfE_sum_eq_three_of_noExotics hF]
  have h1 : F = S + (F - S) := by exact Eq.symm (add_tsub_cancel_of_le hSle)
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 + x.2))).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp at hx
    obtain ⟨M, N, hmem, hsum⟩ := hx
    have hl : (M, N) ∈ F := by
      apply Multiset.mem_of_subset (t := F) at hmem
      exact hmem
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    have hx : x ∈ F.chiralIndicesOfE := by
      simp [chiralIndicesOfE]
      use M, N
    exact chiralIndicesOfE_noneg_of_noExotics F hF x hx
  rw [chiralIndicesOfE]
  rw [h1]
  rw [Multiset.map_add, Multiset.sum_add]
  omega

end FluxesTen

end SU5U1

end FTheory
