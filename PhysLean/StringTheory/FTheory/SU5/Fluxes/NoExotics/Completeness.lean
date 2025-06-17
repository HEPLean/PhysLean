/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.ChiralIndices
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Elems
/-!

# Completeness of `Elems` with regard to the `NoExotics` condition

In the module:

- `PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Elems`

we define finite sets of elements of `FluxesFive` and `FluxesTen` which satisfy the
`NoExotics` condition.

In this module we prove that these sets are complete, in the sense that every
element of `FluxesFive` or `FluxesTen` which satisfies the `NoExotics` condition
is contained in them. This statement corresponds to the following lemmas:

- `FluxesFive.noExotics_iff_mem_elemsNoExotics`
- `FluxesTen.noExotics_iff_mem_elemsNoExotics`

Our proof follows by building allowed subsets of fluxes by their cardinality, and heavily relies
on the `decide` tactic.

Note that the `10d` fluxes are much more constrained than the 5-bar fluxes. This is because
they are constrained by `3` SM representations `Q`, `U`, and `E`, whereas the 5-bar fluxes
are only constrained by `2` SM representations `D` and `L`.

-/
namespace FTheory

namespace SU5

/-!

## Completeness for `FluxesFive`

-/
namespace FluxesFive

lemma mem_mem_finset_of_noExotics (F : FluxesFive) (hF : F.NoExotics)
    (hnZ : F.HasNoZero)
    (x : ℤ × ℤ) (hx : x ∈ F) :
    x ∈ ({(0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2),
      (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0)} : Finset (ℤ × ℤ)) := by
  rcases x with ⟨M, N⟩
  have hM : M ∈ F.chiralIndicesOfD := by
    simp [chiralIndicesOfD]
    use N
  have hN : M + N ∈ F.chiralIndicesOfL := by
    simp [chiralIndicesOfL]
    use M, N
  simp only [Int.reduceNeg, Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton]
  have hL1 := F.mem_chiralIndicesOfL_mem_of_noExotics hF (M + N) hN
  have hD1 := F.mem_chiralIndicesOfD_mem_of_noExotics hF M hM
  have h0 : ¬ (M = 0 ∧ N = 0) := by
    by_contra hn
    rcases hn with ⟨hn1, hn2⟩
    subst hn1 hn2
    exact hnZ hx
  let D := M + N
  have hd : N = D - M := by omega
  generalize D = D' at *
  subst hd
  simp only [add_sub_cancel] at hL1
  clear D hN hx hM
  revert h0
  revert D' M
  decide

/-!

### Allowed subsets of `FluxesFive` obeying `NoExotics`

-/

lemma subset_le_mem_of_card_eq_one {F : FluxesFive} (hF : F.NoExotics)
    (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 1) (hS : S ≤ F) :
    S ∈ ({{(0, 1)}, {(0, 2)}, {(0, 3)}, {(1, -1)}, {(1, 0)}, {(1, 1)}, {(1, 2)},
      {(2, -2)}, {(2, -1)}, {(2, 0)}, {(2, 1)}, {(3, -3)}, {(3, -2)}, {(3, -1)}, {(3, 0)}} :
      Finset (Multiset (ℤ × ℤ))) := by
  rw [Multiset.card_eq_one] at hcard
  obtain ⟨x, rfl⟩ := hcard
  have hx := mem_mem_finset_of_noExotics F hF hnZ x (by simpa using hS)
  fin_cases hx
  all_goals decide

lemma subset_le_mem_of_card_eq_two {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 2) (hS : S ≤ F) :
    S ∈ ({{(0, 1), (0, 1)}, {(0, 1), (1, -1)}, {(0, 1), (1, 0)}, {(0, 1), (0, 2)},
      {(0, 1), (1, 1)}, {(0, 1), (2, -2)}, {(0, 1), (2, -1)}, {(0, 1), (2, 0)},
      {(0, 1), (3, -3)}, {(0, 1), (3, -2)}, {(0, 1), (3, -1)},
      {(0, 2), (1, -1)}, {(0, 2), (1, 0)}, {(0, 2), (2, -2)}, {(0, 2), (2, -1)},
      {(0, 2), (3, -3)}, {(0, 2), (3, -2)}, {(0, 3), (1, -1)}, {(0, 3), (2, -2)},
      {(0, 3), (3, -3)}, {(1, -1), (1, -1)}, {(1, -1), (1, 0)}, {(1, -1), (1, 1)},
      {(1, -1), (1, 2)}, {(1, -1), (2, -2)}, {(1, -1), (2, -1)}, {(1, -1), (2, 0)},
      {(1, 0), (1, 0)}, {(1, -1), (2, 1)}, {(1, 0), (1, 1)}, {(1, 0), (2, -2)},
      {(1, 0), (2, -1)}, {(1, 0), (2, 0)}, {(1, 1), (2, -2)}, {(1, 1), (2, -1)},
      {(1, 2), (2, -2)}} : Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    simp only [not_false_eq_true]
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_one hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_three {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 3) (hS : S ≤ F) :
    S ∈ ({{(0, 1), (0, 1), (0, 1)}, {(0, 1), (0, 1), (1, -1)},
    {(0, 1), (0, 1), (1, 0)}, {(0, 1), (0, 1), (2, -2)},
    {(0, 1), (0, 1), (2, -1)}, {(0, 1), (0, 1), (3, -3)}, {(0, 1), (0, 1), (3, -2)},
    {(0, 1), (0, 2), (1, -1)}, {(0, 1), (0, 2), (2, -2)}, {(0, 1), (0, 2), (3, -3)},
    {(0, 1), (1, -1), (1, -1)}, {(0, 1), (1, -1), (1, 0)}, {(0, 1), (1, -1), (1, 1)},
    {(0, 1), (1, -1), (2, -2)}, {(0, 1), (1, -1), (2, -1)}, {(0, 1), (1, -1), (2, 0)},
    {(0, 1), (1, 0), (1, 0)}, {(0, 1), (1, 0), (2, -2)}, {(0, 1), (1, 0), (2, -1)},
    {(0, 1), (1, 1), (2, -2)}, {(0, 2), (1, -1), (1, -1)}, {(0, 2), (1, -1), (1, 0)},
    {(0, 2), (1, -1), (2, -2)}, {(0, 2), (1, -1), (2, -1)}, {(0, 2), (1, 0), (2, -2)},
    {(0, 3), (1, -1), (1, -1)}, {(0, 3), (1, -1), (2, -2)}, {(1, -1), (1, -1), (1, -1)},
    {(1, -1), (1, -1), (1, 0)}, {(1, -1), (1, -1), (1, 1)}, {(1, -1), (1, -1), (1, 2)},
    {(1, -1), (1, 0), (1, 0)}, {(1, -1), (1, 0), (1, 1)}, {(1, 0), (1, 0), (1, 0)} } :
    Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    decide
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_two hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_four {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 4) (hS : S ≤ F) :
    S ∈ ({{(0, 1), (0, 1), (0, 1), (1, -1)},
    {(0, 1), (0, 1), (0, 1), (2, -2)}, {(0, 1), (0, 1), (0, 1), (3, -3)},
    {(0, 1), (0, 1), (1, -1), (1, -1)}, {(0, 1), (0, 1), (1, -1), (1, 0)},
    {(0, 1), (0, 1), (1, -1), (2, -2)}, {(0, 1), (0, 1), (1, -1), (2, -1)},
    {(0, 1), (0, 1), (1, 0), (2, -2)}, {(0, 1), (0, 2), (1, -1), (1, -1)},
    {(0, 1), (0, 2), (1, -1), (2, -2)}, {(0, 1), (1, -1), (1, -1), (1, -1)},
    {(0, 1), (1, -1), (1, -1), (1, 0)}, {(0, 1), (1, -1), (1, -1), (1, 1)},
    {(0, 1), (1, -1), (1, 0), (1, 0)}, {(0, 2), (1, -1), (1, -1), (1, -1)},
    {(0, 2), (1, -1), (1, -1), (1, 0)}, {(0, 3), (1, -1), (1, -1), (1, -1)}} :
    Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    decide
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_three hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_five {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 5) (hS : S ≤ F) :
    S ∈ ({{(0, 1), (0, 1), (0, 1), (1, -1), (1, -1)},
    {(0, 1), (0, 1), (0, 1), (1, -1), (2, -2)},
    {(0, 1), (0, 1), (1, -1), (1, -1), (1, -1)},
    {(0, 1), (0, 1), (1, -1), (1, -1), (1, 0)},
    {(0, 1), (0, 2), (1, -1), (1, -1), (1, -1)}} :
    Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons,
    Int.reduceNeg, Finset.mem_insert, Multiset.zero_ne_cons,
    Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    decide
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_four hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_six {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 6) (hS : S ≤ F) :
    S ∈ ({{(0, 1), (0, 1), (0, 1), (1, -1), (1, -1), (1, -1)}} :
    Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg,
    Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons,
    Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    decide
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_five hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_seven {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 7) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg,
    Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons,
    Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    decide
  intro a S ih hcard hle hSum1 hSum2
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_six hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_seven_add {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) {n : ℕ} (hcard : S.card = 7 + n) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) := by
  match n with
  | 0 =>
    exact subset_le_mem_of_card_eq_seven hF hnZ S hcard hS
  | .succ n =>
    revert S
    apply Multiset.induction
    · simp
      omega
    intro a S ih hle hcard
    have hsub : S ≤ F := by
      refine Multiset.le_iff_count.mpr ?_
      intro b
      rw [Multiset.le_iff_count] at hle
      trans Multiset.count b (a ::ₘ S)
      · exact Multiset.count_le_count_cons b a S
      · exact hle b
    have hSCard : S.card = 7 + n := by
      rw [Multiset.card_cons] at hcard
      simp at hcard
      omega
    have ih' := subset_le_mem_of_card_eq_seven_add hF hnZ S hSCard hsub
    simp at ih'

lemma subset_le_mem_of_card_ge_seven {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : 7 ≤ S.card) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) :=
  subset_le_mem_of_card_eq_seven_add (n := S.card - 7) hF hnZ S (by omega) hS

/-!

### Resulting properties on `FluxesFive` with `NoExotics`

-/

lemma card_le_six_of_noExotics {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ≤ 6 := by
  by_contra hn
  simp at hn
  have hn := subset_le_mem_of_card_ge_seven hF hnZ F hn (by simp)
  simp at hn

lemma card_mem_range_seven_of_noExotics {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ∈ Finset.range 7 := by
  rw [Finset.mem_range_succ_iff]
  exact card_le_six_of_noExotics hF hnZ

lemma mem_elemsNoExotics_of_noExotics (F : FluxesFive) (hNE : F.NoExotics) (hnZ : F.HasNoZero) :
    F ∈ elemsNoExotics := by
  have h1 := card_mem_range_seven_of_noExotics hNE hnZ
  simp [Finset.range] at h1
  rcases h1 with hr | hr | hr | hr | hr | hr | hr
  · have hF := subset_le_mem_of_card_eq_six hNE hnZ F hr (by rfl)
    clear hr hnZ hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_five hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_four hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_three hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_two hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_one hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · subst hr
    revert hNE
    decide

/-- Completness of `elemsNoExotics`, that is, every element of `FluxesFive`
  which obeys `NoExotics` is an element of `elemsNoExotics`, and every
  element of `elemsNoExotics` obeys `NoExotics`. -/
lemma noExotics_iff_mem_elemsNoExotics (F : FluxesFive) :
    F.NoExotics ∧ F.HasNoZero ↔ F ∈ elemsNoExotics := by
  constructor
  · exact fun ⟨h1, h2⟩ => mem_elemsNoExotics_of_noExotics F h1 h2
  · exact fun h => ⟨noExotics_of_mem_elemsNoExotics F h, hasNoZero_of_mem_elemsNoExotics F h⟩

end FluxesFive

/-!

## Completeness for `FluxesTen`

-/

namespace FluxesTen

lemma mem_mem_finset_of_noExotics (F : FluxesTen) (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (x : ℤ × ℤ) (hx : x ∈ F) :
    x ∈ ({(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 0)} : Finset (ℤ × ℤ)) := by
  rcases x with ⟨M, N⟩
  have hQ : M ∈ F.chiralIndicesOfQ := by
    simp [chiralIndicesOfQ]
    use N
  have hU : M - N ∈ F.chiralIndicesOfU := by
    simp [chiralIndicesOfU]
    use M, N
  have hE : M + N ∈ F.chiralIndicesOfE := by
    simp [chiralIndicesOfE]
    use M, N
  simp only [Int.reduceNeg, Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton]
  have hQ1 := F.mem_chiralIndicesOfQ_mem_of_noExotics hF M hQ
  have hU1 := F.mem_chiralIndicesOfU_mem_of_noExotics hF (M - N) hU
  have hE1 := F.mem_chiralIndicesOfE_mem_of_noExotics hF (M + N) hE
  have h0 : ¬ (M = 0 ∧ N = 0) := by
    by_contra hn
    rcases hn with ⟨hn1, hn2⟩
    subst hn1 hn2
    exact hnZ hx
  let D := M + N
  have hd : N = D - M := by omega
  generalize D = D' at *
  subst hd
  simp only [add_sub_cancel] at hE1
  clear hU hE hQ hx D
  revert h0 hU1
  revert D'
  revert M
  decide

/-!

### Allowed subsets of `FluxesTen` obeying `NoExotics`

-/

lemma subset_le_mem_of_card_eq_one {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 1) (hS : S ≤ F) :
    S ∈ ({{(1, -1)}, {(1, 0)}, {(1, 1)}, {(2, -1)}, {(2, 0)}, {(2, 1)}, {(3, 0)}} :
    Finset (Multiset (ℤ × ℤ))) := by
  rw [Multiset.card_eq_one] at hcard
  obtain ⟨x, rfl⟩ := hcard
  have hx := mem_mem_finset_of_noExotics F hF hnZ x (by simpa using hS)
  fin_cases hx
  all_goals decide

lemma subset_le_mem_of_card_eq_two {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 2) (hS : S ≤ F) :
    S ∈ ({{(1, -1), (1, 0)}, {(1, -1), (1, 1)}, {(1, -1), (2, 1)},
      {(1, 0), (1, 0)}, {(1, 0), (1, 1)}, {(1, 0), (2, 0)}, {(1, 1), (2, -1)}} :
      Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfQ_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfU_subset_sum_le_three_of_noExotics F hF S hS
  have hsum3 := chiralIndicesOfE_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    simp only [not_false_eq_true]
  intro a S ih hcard hle hSum1 hSum2 hsum3
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_one hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2 hsum3
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_three {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 3) (hS : S ≤ F) :
    S ∈ ({{(1, -1), (1, 0), (1, 1)}, {(1, 0), (1, 0), (1, 0)}} : Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfQ_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfU_subset_sum_le_three_of_noExotics F hF S hS
  have hsum3 := chiralIndicesOfE_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    simp only [not_false_eq_true]
  intro a S ih hcard hle hSum1 hSum2 hsum3
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_two hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2 hsum3
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_four {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : S.card = 4) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) := by
  have hSum1 := chiralIndicesOfQ_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfU_subset_sum_le_three_of_noExotics F hF S hS
  have hsum3 := chiralIndicesOfE_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp only [Multiset.card_zero, OfNat.zero_ne_ofNat, Set.mem_setOf_eq, zero_le,
    Multiset.map_zero, Multiset.sum_zero, Nat.ofNat_nonneg, Multiset.insert_eq_cons, Int.reduceNeg,
    Finset.mem_insert, Multiset.zero_ne_cons, Finset.mem_singleton, or_self, imp_false,
    not_true_eq_false]
    simp [not_false_eq_true]
  intro a S ih hcard hle hSum1 hSum2 hsum3
  have hsub : S ≤ F := by
    refine Multiset.le_iff_count.mpr ?_
    intro b
    rw [Multiset.le_iff_count] at hle
    trans Multiset.count b (a ::ₘ S)
    · exact Multiset.count_le_count_cons b a S
    · exact hle b
  have hmem : a ∈ F := by
    apply Multiset.subset_of_le hle
    simp
  rw [Multiset.card_cons] at hcard
  simp at hcard
  have ha := mem_mem_finset_of_noExotics F hF hnZ a hmem
  have hS := subset_le_mem_of_card_eq_three hF hnZ S hcard hsub
  clear hle ih hmem hcard hsub
  revert hSum1 hSum2 hsum3
  revert a
  revert S
  decide

lemma subset_le_mem_of_card_eq_four_add {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) {n : ℕ} (hcard : S.card = 4 + n) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) := by
  match n with
  | 0 =>
    exact subset_le_mem_of_card_eq_four hF hnZ S hcard hS
  | .succ n =>
    revert S
    apply Multiset.induction
    · simp
      omega
    intro a S ih hle hcard
    have hsub : S ≤ F := by
      refine Multiset.le_iff_count.mpr ?_
      intro b
      rw [Multiset.le_iff_count] at hle
      trans Multiset.count b (a ::ₘ S)
      · exact Multiset.count_le_count_cons b a S
      · exact hle b
    have hSCard : S.card = 4 + n := by
      rw [Multiset.card_cons] at hcard
      simp at hcard
      omega
    have ih' := subset_le_mem_of_card_eq_four_add hF hnZ S hSCard hsub
    simp at ih'

lemma subset_le_mem_of_card_ge_four {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset (ℤ × ℤ)) (hcard : 4 ≤ S.card) (hS : S ≤ F) :
    S ∈ ({} : Finset (Multiset (ℤ × ℤ))) :=
  subset_le_mem_of_card_eq_four_add (n := S.card - 4) hF hnZ S (by omega) hS

/-!

### Resulting properties on `FluxesTen` with `NoExotics`

-/

lemma card_le_three_of_noExotics {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ≤ 3 := by
  by_contra hn
  simp at hn
  have hn := subset_le_mem_of_card_ge_four hF hnZ F hn (by simp)
  simp at hn

lemma card_mem_range_four_of_noExotics {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ∈ Finset.range 4 := by
  rw [Finset.mem_range_succ_iff]
  exact card_le_three_of_noExotics hF hnZ

lemma mem_elemsNoExotics_of_noExotics (F : FluxesTen) (hNE : F.NoExotics) (hnZ : F.HasNoZero) :
    F ∈ elemsNoExotics := by
  have h1 := card_mem_range_four_of_noExotics hNE hnZ
  simp [Finset.range] at h1
  rcases h1 with hr | hr | hr | hr
  · have hF := subset_le_mem_of_card_eq_three hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_two hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · have hF := subset_le_mem_of_card_eq_one hNE hnZ F hr (by rfl)
    clear hr hnZ
    revert hNE
    revert F
    decide
  · subst hr
    revert hNE
    decide

/-- Completness of `elemsNoExotics`, that is, every element of `FluxesTen`
  which obeys `NoExotics` is an element of `elemsNoExotics`, and every
  element of `elemsNoExotics` obeys `NoExotics`. -/
lemma noExotics_iff_mem_elemsNoExotics (F : FluxesTen) :
    F.NoExotics ∧ F.HasNoZero ↔ F ∈ elemsNoExotics := by
  constructor
  · exact fun h => mem_elemsNoExotics_of_noExotics F h.1 h.2
  · exact fun h => ⟨noExotics_of_mem_elemsNoExotics F h, hasNoZero_of_mem_elemsNoExotics F h⟩

end FluxesTen
end SU5

end FTheory
