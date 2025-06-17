/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Basic
/-!

# Completions of charges

We say a set of charges is complete if it has all types of fields.

Given a collection of charges `x` in `ofFinset S5 S10`,
  the completions of `x` are the, minimimal charges `y` in `ofFinset S5 S10` which are a super sets
  of `x` and are complete.

This module defines the `IsComplete` proposition and completions of charges and provides
lemmas about them.

-/

namespace SuperSymmetry

namespace SU5

namespace Charges

/-!

## Completions

-/

/-- A collection of charges is complete if it has all types of fields. -/
def IsComplete (x : Charges) : Prop :=
  x.1.isSome ∧ x.2.1.isSome ∧ x.2.2.1 ≠ ∅ ∧ x.2.2.2 ≠ ∅

instance (x : Charges) : Decidable (IsComplete x) :=
  inferInstanceAs (Decidable (x.1.isSome ∧ x.2.1.isSome ∧ x.2.2.1 ≠ ∅ ∧ x.2.2.2 ≠ ∅))

lemma isComplete_mono {x y : Charges} (h : x ⊆ y) (hx : IsComplete x) :
    IsComplete y := by
  simp [IsComplete] at *
  rw [subset_def] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hn
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hn
    have h1 := h.1
    have hx1 := hx.1
    rw [Option.isSome_iff_exists] at hx1
    obtain ⟨a, ha⟩ := hx1
    rw [hn, ha] at h1
    simp at h1
  · by_contra hn
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hn
    have h1 := h.2.1
    have hx1 := hx.2.1
    rw [Option.isSome_iff_exists] at hx1
    obtain ⟨a, ha⟩ := hx1
    rw [hn, ha] at h1
    simp at h1
  · by_contra hn
    simp_all
  · by_contra hn
    simp_all

/-!

## Completions

Note the completions are not monotonic with respect to the subset relation.

-/

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimimal charges `y` in `ofFinset S5 S10` which are a super sets of `x` and are
  complete. -/
def completions (S5 S10 : Finset ℤ) (x : Charges) : Multiset Charges :=
  let SqHd := if x.1.isSome then {x.1} else S5.val.map fun y => some y
  let SqHu := if x.2.1.isSome then {x.2.1} else S5.val.map fun y => some y
  let SQ5 := if x.2.2.1 ≠ ∅ then {x.2.2.1} else S5.val.map fun y => {y}
  let SQ10 := if x.2.2.2 ≠ ∅ then {x.2.2.2} else S10.val.map fun y => {y}
  (SqHd.product (SqHu.product (SQ5.product SQ10)))

lemma completions_eq_singleton_of_complete {S5 S10 : Finset ℤ} (x : Charges)
    (hcomplete : IsComplete x) :
    completions S5 S10 x = {x} := by
  simp [completions]
  simp [IsComplete] at hcomplete
  by_cases h1 : x.1.isSome
  case' neg => simp_all
  by_cases h2 : x.2.1.isSome
  case' neg => simp_all
  by_cases h3 : x.2.2.1 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.2.2.2 ≠ ∅
  case' neg => simp_all
  simp_all
  rfl

@[simp]
lemma self_mem_completions_iff_isComplete {S5 S10 : Finset ℤ} (x : Charges) :
    x ∈ completions S5 S10 x ↔ IsComplete x := by
  simp [completions, IsComplete]
  repeat rw [Multiset.mem_product]
  by_cases h1 : x.1.isSome
  case' neg => simp_all
  by_cases h2 : x.2.1.isSome
  case' neg => simp_all
  by_cases h3 : x.2.2.1 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.2.2.2 ≠ ∅
  case' neg => simp_all
  simp_all

lemma mem_completions_isComplete {S5 S10 : Finset ℤ} {x y : Charges}
    (hx : y ∈ completions S5 S10 x) : IsComplete y := by
  match y with
  | (qHd, qHu, Q5, Q10) =>
  simp [completions] at hx
  repeat rw [Multiset.mem_product] at hx
  simp at hx
  match x with
  | (x1, x2, x3, x4) =>
  simp_all
  rw [IsComplete]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
    by_cases hs : x1.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.1
      simp
  · simp
    by_cases hs : x2.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.1
      simp
  · simp
    by_cases hs : x3 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.1
      simp
  · simp
    by_cases hs : x4 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.2
      simp

lemma self_subset_mem_completions (S5 S10 : Finset ℤ) (x y : Charges)
    (hy : y ∈ completions S5 S10 x) : x ⊆ y := by
  simp [completions] at hy
  repeat rw [Multiset.mem_product] at hy
  rw [Subset]
  dsimp [hasSubset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : x.1.isSome
    · simp_all
    · simp_all
  · by_cases h : x.2.1.isSome
    · simp_all
    · simp_all
  · by_cases h : x.2.2.1 ≠ ∅
    · simp_all
    · simp_all
  · by_cases h : x.2.2.2 ≠ ∅
    · simp_all
    · simp_all

lemma exist_completions_subset_of_complete (S5 S10 : Finset ℤ) (x y : Charges)
    (hsubset : x ⊆ y) (hy : y ∈ ofFinset S5 S10) (hycomplete : IsComplete y) :
    ∃ z ∈ completions S5 S10 x, z ⊆ y := by
  by_cases hx : IsComplete x
  · use x
    simp_all
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  simp [IsComplete] at hycomplete
  rw [Option.isSome_iff_exists, Option.isSome_iff_exists] at hycomplete
  obtain ⟨y1, rfl⟩ := hycomplete.1
  obtain ⟨y2, rfl⟩ := hycomplete.2.1
  rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem] at hycomplete
  simp at hycomplete
  obtain ⟨z3, hz3⟩ := hycomplete.1
  obtain ⟨z4, hz4⟩ := hycomplete.2
  have hz3Mem : z3 ∈ S5 := by
    apply mem_ofFinset_Q5_subset S5 S10 hy
    simp_all
  have hz4Mem : z4 ∈ S10 := by
    apply mem_ofFinset_Q10_subset S5 S10 hy
    simp_all
  have hy1' : some y1 ∈ if x1.isSome = true then {x1} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h1 : x1.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h1
      obtain ⟨a, rfl⟩ := h1
      simp_all
    · simp_all
      exact qHd_mem_ofFinset S5 S10 y1 (some y2, y3, y4) hy
  have hy2' : some y2 ∈ if x2.isSome = true then {x2} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h2 : x2.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h2
      obtain ⟨a, rfl⟩ := h2
      simp_all
    · simp_all
      exact qHu_mem_ofFinset S5 S10 y2 (some y1) (y3, y4) hy
  simp_all
  by_cases h3 : x3 ≠ ∅
  · by_cases h4 : x4 ≠ ∅
    · use (y1, y2, x3, x4)
      constructor
      · simp_all [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use (y1, y2, x3, {z4})
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
  · simp at h3
    subst h3
    by_cases h4 : x4 ≠ ∅
    · use (y1, y2, {z3}, x4)
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use (y1, y2, {z3}, {z4})
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all

end Charges

end SU5

end SuperSymmetry
