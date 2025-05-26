/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
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

lemma nonZeroChiralIndicesOfD_ge_one_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfD) : 1 ≤ ci := by
  have h0 := (Multiset.mem_filter.mp hci).2
  have h1 := chiralIndicesOfD_noneg_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  omega

lemma mem_nonZeroChiralIndicesOfD_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfD) :
    ci ∈ ({1, 2, 3} : Finset ℤ) := by
  have hr := mem_chiralIndicesOfD_mem_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h0 := nonZeroChiralIndicesOfD_ge_one_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma nonZeroChiralIndicesOfD_sum_eq_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfD.sum = 3 := by
  rw [← F.chiralIndicesOfD_sum_eq_nonZeroChiralIndicesOfD_sum]
  exact F.chiralIndicesOfD_sum_eq_three_of_noExotics hF

lemma nonZeroChiralIndicesOfD_card_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfD.card ≤ 3 := by
  have h1 := Multiset.card_nsmul_le_sum (nonZeroChiralIndicesOfD_ge_one_of_noExotics F hF)
  rw [F.nonZeroChiralIndicesOfD_sum_eq_three_of_noExotics hF] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_le_ofNat] at h1
  omega

lemma nonZeroChiralIndicesOfD_card_mem_range_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfD.card ∈ Finset.range 4 :=
  Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
  nonZeroChiralIndicesOfD_card_le_three_of_noExotics F hF

lemma nonZeroChiralIndicesOfD_mem_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.nonZeroChiralIndicesOfD ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ℤ)) := by
  have hsum := F.nonZeroChiralIndicesOfD_sum_eq_three_of_noExotics hF
  have hf := F.nonZeroChiralIndicesOfD_card_mem_range_of_noExotics hF
  have hmin := F.mem_nonZeroChiralIndicesOfD_mem_of_noExotics hF
  simp [Finset.range] at hf
  generalize F.nonZeroChiralIndicesOfD = S at *
  rcases hf with hr | hr | hr | hr
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨x, y, z, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    have hz := hmin z (by simp)
    clear hmin
    revert hsum; revert x; revert y; revert z
    decide
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨x, y, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    clear hmin
    revert hsum; revert x; revert y
    decide
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨x, rfl⟩ := hr
    have hx := hmin x (by simp)
    clear hmin
    revert hsum; revert x
    decide
  · subst hr
    simp at hsum

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

lemma nonZeroChiralIndicesOfL_ge_one_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfL) : 1 ≤ ci := by
  have h0 := (Multiset.mem_filter.mp hci).2
  have h1 := chiralIndicesOfL_noneg_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  omega

lemma mem_nonZeroChiralIndicesOfL_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfL) :
    ci ∈ ({1, 2, 3} : Finset ℤ) := by
  have hr := mem_chiralIndicesOfL_mem_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h0 := nonZeroChiralIndicesOfL_ge_one_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma nonZeroChiralIndicesOfL_sum_eq_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfL.sum = 3 := by
  rw [← F.chiralIndicesOfL_sum_eq_nonZeroChiralIndicesOfL_sum]
  exact F.chiralIndicesOfL_sum_eq_three_of_noExotics hF

lemma nonZeroChiralIndicesOfL_card_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfL.card ≤ 3 := by
  have h1 := Multiset.card_nsmul_le_sum (nonZeroChiralIndicesOfL_ge_one_of_noExotics F hF)
  rw [F.nonZeroChiralIndicesOfL_sum_eq_three_of_noExotics hF] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_le_ofNat] at h1
  omega

lemma nonZeroChiralIndicesOfL_card_mem_range_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfL.card ∈ Finset.range 4 :=
  Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
  nonZeroChiralIndicesOfL_card_le_three_of_noExotics F hF

lemma nonZeroChiralIndicesOfL_mem_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.nonZeroChiralIndicesOfL ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ℤ)) := by
  have hsum := F.nonZeroChiralIndicesOfL_sum_eq_three_of_noExotics hF
  have hf := F.nonZeroChiralIndicesOfL_card_mem_range_of_noExotics hF
  have hmin := F.mem_nonZeroChiralIndicesOfL_mem_of_noExotics hF
  simp [Finset.range] at hf
  generalize F.nonZeroChiralIndicesOfL = S at *
  rcases hf with hr | hr | hr | hr
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨x, y, z, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    have hz := hmin z (by simp)
    clear hmin
    revert hsum; revert x; revert y; revert z
    decide
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨x, y, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    clear hmin
    revert hsum; revert x; revert y
    decide
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨x, rfl⟩ := hr
    have hx := hmin x (by simp)
    clear hmin
    revert hsum; revert x
    decide
  · subst hr
    simp at hsum

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

lemma nonZeroChiralIndicesOfQ_ge_one_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfQ) : 1 ≤ ci := by
  have h0 := (Multiset.mem_filter.mp hci).2
  have h1 := chiralIndicesOfQ_noneg_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  omega

lemma mem_nonZeroChiralIndicesOfQ_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfQ) :
    ci ∈ ({1, 2, 3} : Finset ℤ) := by
  have hr := mem_chiralIndicesOfQ_mem_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h0 := nonZeroChiralIndicesOfQ_ge_one_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma nonZeroChiralIndicesOfQ_sum_eq_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfQ.sum = 3 := by
  rw [← F.chiralIndicesOfQ_sum_eq_nonZeroChiralIndicesOfQ_sum]
  exact F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF

lemma nonZeroChiralIndicesOfQ_card_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfQ.card ≤ 3 := by
  have h1 := Multiset.card_nsmul_le_sum (nonZeroChiralIndicesOfQ_ge_one_of_noExotics F hF)
  rw [F.nonZeroChiralIndicesOfQ_sum_eq_three_of_noExotics hF] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_le_ofNat] at h1
  omega

lemma nonZeroChiralIndicesOfQ_card_mem_range_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfQ.card ∈ Finset.range 4 :=
  Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
  nonZeroChiralIndicesOfQ_card_le_three_of_noExotics F hF

lemma nonZeroChiralIndicesOfQ_mem_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.nonZeroChiralIndicesOfQ ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ℤ)) := by
  have hsum := F.nonZeroChiralIndicesOfQ_sum_eq_three_of_noExotics hF
  have hf := F.nonZeroChiralIndicesOfQ_card_mem_range_of_noExotics hF
  have hmin := F.mem_nonZeroChiralIndicesOfQ_mem_of_noExotics hF
  simp [Finset.range] at hf
  generalize F.nonZeroChiralIndicesOfQ = S at *
  rcases hf with hr | hr | hr | hr
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨x, y, z, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    have hz := hmin z (by simp)
    clear hmin
    revert hsum; revert x; revert y; revert z
    decide
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨x, y, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    clear hmin
    revert hsum; revert x; revert y
    decide
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨x, rfl⟩ := hr
    have hx := hmin x (by simp)
    clear hmin
    revert hsum; revert x
    decide
  · subst hr
    simp at hsum

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

lemma nonZeroChiralIndicesOfU_ge_one_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfU) : 1 ≤ ci := by
  have h0 := (Multiset.mem_filter.mp hci).2
  have h1 := chiralIndicesOfU_noneg_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  omega

lemma mem_nonZeroChiralIndicesOfU_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfU) :
    ci ∈ ({1, 2, 3} : Finset ℤ) := by
  have hr := mem_chiralIndicesOfU_mem_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h0 := nonZeroChiralIndicesOfU_ge_one_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma nonZeroChiralIndicesOfU_sum_eq_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfU.sum = 3 := by
  rw [← F.chiralIndicesOfU_sum_eq_nonZeroChiralIndicesOfU_sum]
  exact F.chiralIndicesOfU_sum_eq_three_of_noExotics hF

lemma nonZeroChiralIndicesOfU_card_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfU.card ≤ 3 := by
  have h1 := Multiset.card_nsmul_le_sum (nonZeroChiralIndicesOfU_ge_one_of_noExotics F hF)
  rw [F.nonZeroChiralIndicesOfU_sum_eq_three_of_noExotics hF] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_le_ofNat] at h1
  omega

lemma nonZeroChiralIndicesOfU_card_mem_range_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfU.card ∈ Finset.range 4 :=
  Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
  nonZeroChiralIndicesOfU_card_le_three_of_noExotics F hF

lemma nonZeroChiralIndicesOfU_mem_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.nonZeroChiralIndicesOfU ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ℤ)) := by
  have hsum := F.nonZeroChiralIndicesOfU_sum_eq_three_of_noExotics hF
  have hf := F.nonZeroChiralIndicesOfU_card_mem_range_of_noExotics hF
  have hmin := F.mem_nonZeroChiralIndicesOfU_mem_of_noExotics hF
  simp [Finset.range] at hf
  generalize F.nonZeroChiralIndicesOfU = S at *
  rcases hf with hr | hr | hr | hr
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨x, y, z, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    have hz := hmin z (by simp)
    clear hmin
    revert hsum; revert x; revert y; revert z
    decide
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨x, y, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    clear hmin
    revert hsum; revert x; revert y
    decide
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨x, rfl⟩ := hr
    have hx := hmin x (by simp)
    clear hmin
    revert hsum; revert x
    decide
  · subst hr
    simp at hsum

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

lemma nonZeroChiralIndicesOfE_ge_one_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfE) : 1 ≤ ci := by
  have h0 := (Multiset.mem_filter.mp hci).2
  have h1 := chiralIndicesOfE_noneg_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  omega

lemma mem_nonZeroChiralIndicesOfE_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.nonZeroChiralIndicesOfE) :
    ci ∈ ({1, 2, 3} : Finset ℤ) := by
  have hr := mem_chiralIndicesOfE_mem_of_noExotics F hF ci (Multiset.mem_filter.mp hci).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have h0 := nonZeroChiralIndicesOfE_ge_one_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma nonZeroChiralIndicesOfE_sum_eq_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfE.sum = 3 := by
  rw [← F.chiralIndicesOfE_sum_eq_nonZeroChiralIndicesOfE_sum]
  exact F.chiralIndicesOfE_sum_eq_three_of_noExotics hF

lemma nonZeroChiralIndicesOfE_card_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfE.card ≤ 3 := by
  have h1 := Multiset.card_nsmul_le_sum (nonZeroChiralIndicesOfE_ge_one_of_noExotics F hF)
  rw [F.nonZeroChiralIndicesOfE_sum_eq_three_of_noExotics hF] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_le_ofNat] at h1
  omega

lemma nonZeroChiralIndicesOfE_card_mem_range_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) : F.nonZeroChiralIndicesOfE.card ∈ Finset.range 4 :=
  Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
  nonZeroChiralIndicesOfE_card_le_three_of_noExotics F hF

lemma nonZeroChiralIndicesOfE_mem_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.nonZeroChiralIndicesOfE ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ℤ)) := by
  have hsum := F.nonZeroChiralIndicesOfE_sum_eq_three_of_noExotics hF
  have hf := F.nonZeroChiralIndicesOfE_card_mem_range_of_noExotics hF
  have hmin := F.mem_nonZeroChiralIndicesOfE_mem_of_noExotics hF
  simp [Finset.range] at hf
  generalize F.nonZeroChiralIndicesOfE = S at *
  rcases hf with hr | hr | hr | hr
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨x, y, z, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    have hz := hmin z (by simp)
    clear hmin
    revert hsum; revert x; revert y; revert z
    decide
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨x, y, rfl⟩ := hr
    have hx := hmin x (by simp)
    have hy := hmin y (by simp)
    clear hmin
    revert hsum; revert x; revert y
    decide
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨x, rfl⟩ := hr
    have hx := hmin x (by simp)
    clear hmin
    revert hsum; revert x
    decide
  · subst hr
    simp at hsum

end FluxesTen

end SU5U1

end FTheory
