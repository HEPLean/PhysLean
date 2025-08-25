/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Completions
/-!
# Minimal super set

Given a a colleciton of charges `x`, and two sets of charges `S5` and `S10`,
a minimal super set of `x` is the collection of charge `y` which is a
super sets of `x`, for which the the additional charges in `y` are
corresponding in `S5` and `S10`, and which is minimal in this regard.

-/

namespace SuperSymmetry

namespace SU5

namespace Charges

variable {𝓩 : Type} [DecidableEq 𝓩]

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimimal charges `y` in `ofFinset S5 S10` which are a super sets of `x`. -/
def minimalSuperSet (S5 S10 : Finset 𝓩) (x : Charges 𝓩) : Finset (Charges 𝓩) :=
  let SqHd := if x.1.isSome then ∅ else S5.image fun y => (some y, x.2)
  let SqHu := if x.2.1.isSome then ∅ else S5.image fun y => (x.1, some y, x.2.2)
  let SQ5 := (S5 \ x.2.2.1).image (fun y => (x.1, x.2.1, insert y x.2.2.1, x.2.2.2))
  let SQ10 := (S10 \ x.2.2.2).image (fun y => (x.1, x.2.1, x.2.2.1, insert y x.2.2.2))
  (SqHd ∪ SqHu ∪ SQ5 ∪ SQ10).erase x

lemma self_subset_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x y : Charges 𝓩)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ⊆ y := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | (none, _, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | (some x1, _, _, _) =>
      simp at hr
  · match x with
    | (_, none, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | (_, some x2, _, _) =>
      simp at hr
  · match x with
    | (_, _, Q5, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
  · match x with
    | (_, _, _, Q10) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]

@[simp]
lemma self_not_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x : Charges 𝓩) :
    x ∉ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]

lemma self_neq_mem_minimalSuperSet (S5 S10 : Finset 𝓩) (x y : Charges 𝓩)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ≠ y := by
  by_contra h
  subst h
  simp at hy

lemma card_of_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : Charges 𝓩}
    (y : Charges 𝓩) (hy : y ∈ minimalSuperSet S5 S10 x) :
    card y = card x + 1 := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | (none, _, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | (some x1, _, _, _) =>
      simp at hr
  · match x with
    | (_, none, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | (_, some x2, _, _) =>
      simp at hr
  · match x with
    | (_, _, Q5, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1
  · match x with
    | (_, _, _, Q10) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1

lemma insert_Q5_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : Charges 𝓩}
    (z : 𝓩) (hz : z ∈ S5) (hznot : z ∉ x.2.2.1) :
    (x.1, x.2.1, insert z x.2.2.1, x.2.2.2) ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | (qHd, qHu, Q5, Q10) =>
  apply And.intro
  · simpa using hznot
  · right
    right
    left
    use z

lemma insert_Q10_mem_minimalSuperSet {S5 S10 : Finset 𝓩} {x : Charges 𝓩}
    (z : 𝓩) (hz : z ∈ S10) (hznot : z ∉ x.2.2.2) :
    (x.1, x.2.1, x.2.2.1, insert z x.2.2.2) ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | (qHd, qHu, Q5, Q10) =>
  apply And.intro
  · simpa using hznot
  · right
    right
    right
    use z

lemma some_qHd_mem_minimalSuperSet_of_none {S5 S10 : Finset 𝓩}
    {x2 : Option 𝓩 × Finset 𝓩 × Finset 𝓩} (z : 𝓩) (hz : z ∈ S5) :
    (some z, x2) ∈ minimalSuperSet S5 S10 (none, x2) := by
  simp_all [minimalSuperSet]

lemma some_qHu_mem_minimalSuperSet_of_none {S5 S10 : Finset 𝓩}
    {x1 : Option 𝓩} {x2 : Finset 𝓩 × Finset 𝓩} (z : 𝓩) (hz : z ∈ S5) :
    (x1, some z, x2) ∈ minimalSuperSet S5 S10 (x1, none, x2) := by
  simp_all [minimalSuperSet]

lemma exists_minimalSuperSet (S5 S10 : Finset 𝓩) {x y : Charges 𝓩}
    (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y)
    (hxneqy : x ≠ y) : ∃ z ∈ minimalSuperSet S5 S10 x, z ⊆ y := by
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  simp at hxneqy
  repeat rw [Prod.ext_iff] at hxneqy
  by_cases h3 : x3 ≠ y3
  · have h3Strict : x3 ⊂ y3 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h3Strict
    obtain ⟨z3, hz3, h3⟩ := h3Strict
    use (x1, x2, insert z3 x3, x4)
    constructor
    · apply insert_Q5_mem_minimalSuperSet
      · apply mem_ofFinset_Q5_subset S5 S10 hy
        simp only
        exact hz3
      · exact h3
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h3
  subst h3
  by_cases h4 : x4 ≠ y4
  · have h4Strict : x4 ⊂ y4 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h4Strict
    obtain ⟨z4, hz4, h4⟩ := h4Strict
    use (x1, x2, x3, insert z4 x4)
    constructor
    · apply insert_Q10_mem_minimalSuperSet
      · apply mem_ofFinset_Q10_subset S5 S10 hy
        simp only
        exact hz4
      · exact h4
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h4
  subst h4
  simp_all
  match x1, y1, x2, y2 with
  | some x1, none, x2, y2 =>
    simp at hsubset
  | none, some y1, x2, y2 =>
    simp at hsubset
    use (some y1, x2, x3, x4)
    constructor
    · apply some_qHd_mem_minimalSuperSet_of_none
      exact qHd_mem_ofFinset S5 S10 _ _ hy
    · simp_all [hasSubset]
  | x1, y1, some x2, none =>
    simp at hsubset
  | x1, y1, none, some y2 =>
    simp at hsubset
    use (x1, some y2, x3, x4)
    constructor
    · apply some_qHu_mem_minimalSuperSet_of_none
      exact qHu_mem_ofFinset S5 S10 _ _ _ hy
    · simp_all [hasSubset]
  | none, none, none, none =>
    simp_all
  | some x1, some y1, none, none =>
    simp_all
  | none, none, some x2, some y2 =>
    simp_all
  | some x1, some y1, some x2, some y2 =>
    simp_all

lemma minimalSuperSet_induction_on_inductive {S5 S10 : Finset 𝓩}
    (p : Charges 𝓩 → Prop) (hp : (x : Charges 𝓩) → p x → ∀ y ∈ minimalSuperSet S5 S10 x, p y)
    (x : Charges 𝓩) (hbase : p x)
    (y : Charges 𝓩) (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y) :
    (n : ℕ) → (hn : n = y.card - x.card) → p y
  | 0, hn => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : card x ≤ card y := card_mono hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    refine minimalSuperSet_induction_on_inductive p hp z ?_ y hy ?_ n ?_
    · exact hp x hbase z hz
    · exact hsubsetz
    · rw [card_of_mem_minimalSuperSet z hz]
      omega

/-!

## Inserting charges and minimal super sets

-/

variable {𝓩 : Type} [DecidableEq 𝓩]

lemma insert_filter_card_zero
    (T : Multiset (Charges 𝓩)) (S5 S10 : Finset 𝓩)
    (p : Charges 𝓩 → Prop) [DecidablePred p]
    (hComplet : ∀ x ∈ T, IsComplete x)
    (h10 : ∀ q10 : S10, ((T.map fun x => (x.1, x.2.1, x.2.2.1, insert q10.1 x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => (x.1, x.2.1, insert q5.1 x.2.2.1, x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
    ∀ x ∈ T, ∀ y ∈ minimalSuperSet S5 S10 x, y ∉ T → ¬ p y := by
  intro (xqHd, xqHu, xQ5, xQ10) x_mem_T y y_mem_minimalSuperSet y_not_in_T
  have x_isComplete : IsComplete (xqHd, xqHu, xQ5, xQ10) := hComplet _ x_mem_T
  have xqHd_isSome : xqHd.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHd_isSome
  obtain ⟨xqHd, rfl⟩ := xqHd_isSome
  have xqHu_isSome : xqHu.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHu_isSome
  obtain ⟨xqHu, rfl⟩ := xqHu_isSome
  simp [minimalSuperSet] at y_mem_minimalSuperSet
  simp_all
  rcases y_mem_minimalSuperSet with ⟨q5, q5_mem_S5, rfl⟩ | ⟨q10, q10_mem_S10, rfl⟩
  · have h5' := h5 q5 q5_mem_S5.1
    rw [Multiset.filter_eq_nil] at h5'
    simp_all
    exact h5' (some xqHd, some xqHu, xQ5, xQ10) x_mem_T y_not_in_T
  · have h10' := h10 q10 q10_mem_S10.1
    rw [Multiset.filter_eq_nil] at h10'
    simp_all
    exact h10' (some xqHd, some xqHu, xQ5, xQ10) x_mem_T y_not_in_T

lemma subset_insert_filter_card_zero_inductive
    (T : Multiset (Charges 𝓩))
    (S5 S10 : Finset 𝓩)
    (p : Charges 𝓩 → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges 𝓩), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges 𝓩)
    (hx : x ∈ T) (y : Charges 𝓩) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, ((T.map fun x => (x.1, x.2.1, x.2.2.1, insert q10.1 x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => (x.1, x.2.1, insert q5.1 x.2.2.1, x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
    (n : ℕ) → (hn : n = y.card - x.card) → y ∉ T → ¬ p y
  | 0, hn, hnot_in_T => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : x.card ≤ y.card := card_mono hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn, hnot_in_T => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    have hz' := insert_filter_card_zero T S5 S10 p hComplet h10 h5 x hx z hz
    by_cases hz_not_in_T : z ∉ T
    · apply hnotSubset
      · exact hsubsetz
      · exact hz' hz_not_in_T
    apply subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet z (n := n)
    · simpa using hz_not_in_T
    · exact hsubsetz
    · exact hy
    · exact fun q10 => h10 q10
    · exact fun q5 => h5 q5
    · rw [card_of_mem_minimalSuperSet z hz]
      omega
    · exact hnot_in_T

/-- For a proposition `p` if `(T.uniqueMap4 (insert q10.1)).toMultiset.filter p`
  and `(T.uniqueMap3 (insert q5.1)).toMultiset.filter p` for all `q5 ∈ S5` and `q10 ∈ S10` then
  if `x ∈ T` and `x ⊆ y` if `y ∉ T` then `¬ p y`.
  This assumes that all charges in `T` are complete, and that `p` satisfies
  `x ⊆ y → ¬ p x → ¬ p y`. -/
lemma subset_insert_filter_card_zero
    (T : Multiset (Charges 𝓩))
    (S5 S10 : Finset 𝓩)
    (p : Charges 𝓩 → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges 𝓩), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges 𝓩)
    (hx : x ∈ T) (y : Charges 𝓩) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, ((T.map fun x => (x.1, x.2.1, x.2.2.1, insert q10.1 x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅)
    (h5 : ∀ q5 : S5, ((T.map fun x => (x.1, x.2.1, insert q5.1 x.2.2.1, x.2.2.2)).filter
      fun y => (y ∉ T ∧ p y)) = ∅) :
      y ∉ T → ¬ p y :=
  subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet x hx y hsubset hy h10 h5
    (y.card - x.card) rfl

end Charges

end SU5

end SuperSymmetry
