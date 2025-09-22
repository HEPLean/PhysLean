/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
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

namespace ChargeSpectrum

variable {𝓩 : Type}
/-!

## Completions

-/

/-- A charge spectrum is complete if it has all types of fields. -/
def IsComplete (x : ChargeSpectrum 𝓩) : Prop :=
  x.qHd.isSome ∧ x.qHu.isSome ∧ x.Q5 ≠ ∅ ∧ x.Q10 ≠ ∅

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) : Decidable (IsComplete x) :=
  inferInstanceAs (Decidable (x.qHd.isSome ∧ x.qHu.isSome ∧ x.Q5 ≠ ∅ ∧ x.Q10 ≠ ∅))

@[simp]
lemma not_isComplete_empty : ¬ IsComplete (∅ : ChargeSpectrum 𝓩) := by
  simp [IsComplete]

lemma isComplete_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (hx : IsComplete x) :
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

variable [DecidableEq 𝓩]

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimimal charges `y` in `ofFinset S5 S10` which are a super sets of `x` and are
  complete. -/
def completions (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) : Multiset (ChargeSpectrum 𝓩) :=
  let SqHd := if x.qHd.isSome then {x.qHd} else S5.val.map fun y => some y
  let SqHu := if x.qHu.isSome then {x.qHu} else S5.val.map fun y => some y
  let SQ5 := if x.Q5 ≠ ∅ then {x.Q5} else S5.val.map fun y => {y}
  let SQ10 := if x.Q10 ≠ ∅ then {x.Q10} else S10.val.map fun y => {y}
  (SqHd.product (SqHu.product (SQ5.product SQ10))).map (toProd).symm


lemma mem_completions_iff {S5 S10 : Finset 𝓩} {x y : ChargeSpectrum 𝓩} :
    y ∈ completions S5 S10 x ↔
    y.qHd ∈ (if x.qHd.isSome then {x.qHd} else S5.val.map fun y => some y) ∧
    y.qHu ∈ (if x.qHu.isSome then {x.qHu} else S5.val.map fun y => some y) ∧
    y.Q5 ∈ (if x.Q5 ≠ ∅ then {x.Q5} else S5.val.map fun y => {y}) ∧
    y.Q10 ∈ (if x.Q10 ≠ ∅ then {x.Q10} else S10.val.map fun y => {y}) := by
  rw [completions]
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨a, h, hy⟩
    have ha : a = toProd y := by subst hy; simp
    subst ha
    simpa [toProd] using h
  · intro h
    use toProd y
    simpa [toProd] using h

lemma completions_nodup (S5 S10 : Finset 𝓩) (x : ChargeSpectrum 𝓩) :
    (completions S5 S10 x).Nodup := by
  simp [completions]
  split_ifs
  all_goals
    refine Multiset.Nodup.map toProd.symm.injective ?_
    refine Multiset.Nodup.product ?_ (Multiset.Nodup.product ?_ (Multiset.Nodup.product ?_ ?_))
  any_goals exact Multiset.nodup_singleton _
  any_goals exact Finset.nodup_map_iff_injOn.mpr (by simp)

lemma completions_eq_singleton_of_complete {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩)
    (hcomplete : IsComplete x) :
    completions S5 S10 x = {x} := by
  simp [completions]
  simp [IsComplete] at hcomplete
  by_cases h1 : x.qHd.isSome
  case' neg => simp_all
  by_cases h2 : x.qHu.isSome
  case' neg => simp_all
  by_cases h3 : x.Q5 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.Q10 ≠ ∅
  case' neg => simp_all
  simp_all
  rfl

@[simp]
lemma self_mem_completions_iff_isComplete {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩) :
    x ∈ completions S5 S10 x ↔ IsComplete x := by
  simp [mem_completions_iff, IsComplete]
  by_cases h1 : x.qHd.isSome
  case neg => simp_all
  by_cases h2 : x.qHu.isSome
  case' neg => simp_all
  by_cases h3 : x.Q5 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.Q10 ≠ ∅
  case' neg => simp_all

  simp_all

lemma mem_completions_isComplete {S5 S10 : Finset 𝓩} {x y : ChargeSpectrum 𝓩}
    (hx : y ∈ completions S5 S10 x) : IsComplete y := by
  match y with
  | ⟨qHd, qHu, Q5, Q10⟩ =>
  simp [mem_completions_iff] at hx
  match x with
  | ⟨x1, x2, x3, x4⟩ =>
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

lemma self_subset_mem_completions (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hy : y ∈ completions S5 S10 x) : x ⊆ y := by
  simp [mem_completions_iff] at hy
  rw [Subset]
  dsimp [hasSubset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : x.qHd.isSome
    · simp_all
    · simp_all
  · by_cases h : x.qHu.isSome
    · simp_all
    · simp_all
  · by_cases h : x.Q5 ≠ ∅
    · simp_all
    · simp_all
  · by_cases h : x.Q10 ≠ ∅
    · simp_all
    · simp_all

lemma exist_completions_subset_of_complete (S5 S10 : Finset 𝓩) (x y : ChargeSpectrum 𝓩)
    (hsubset : x ⊆ y) (hy : y ∈ ofFinset S5 S10) (hycomplete : IsComplete y) :
    ∃ z ∈ completions S5 S10 x, z ⊆ y := by
  by_cases hx : IsComplete x
  · use x
    simp_all
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  simp [IsComplete] at hycomplete
  rw [Option.isSome_iff_exists, Option.isSome_iff_exists] at hycomplete
  obtain ⟨y1, rfl⟩ := hycomplete.1
  obtain ⟨y2, rfl⟩ := hycomplete.2.1
  rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem] at hycomplete
  simp at hycomplete
  obtain ⟨z3, hz3⟩ := hycomplete.1
  obtain ⟨z4, hz4⟩ := hycomplete.2
  simp [mem_ofFinset_iff] at hy
  have hz3Mem : z3 ∈ S5 := by
    apply hy.2.2.1
    simp_all
  have hz4Mem : z4 ∈ S10 := by
    apply hy.2.2.2
    simp_all
  have hy1' : some y1 ∈ if x1.isSome = true then {x1} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h1 : x1.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h1
      obtain ⟨a, rfl⟩ := h1
      simp_all
    · simp_all
  have hy2' : some y2 ∈ if x2.isSome = true then {x2} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h2 : x2.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h2
      obtain ⟨a, rfl⟩ := h2
      simp_all
    · simp_all
  simp_all
  by_cases h3 : x3 ≠ ∅
  · by_cases h4 : x4 ≠ ∅
    · use ⟨y1, y2, x3, x4⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use ⟨y1, y2, x3, {z4}⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
  · simp at h3
    subst h3
    by_cases h4 : x4 ≠ ∅
    · use ⟨y1, y2, {z3}, x4⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use ⟨y1, y2, {z3}, {z4}⟩
      constructor
      · simp_all [mem_completions_iff]
      · rw [Subset]
        dsimp [hasSubset]
        simp_all

/-!

## Completions of minimal top yukawa

-/

/-- A fast version of `completions` for an `x` which is in
  `minimallyAllowsTermsOfFinset S5 S10 .topYukawa`. -/
def completionsTopYukawa (S5 : Finset 𝓩) (x : ChargeSpectrum 𝓩) :
    Multiset (ChargeSpectrum 𝓩) :=
  (S5.val.product S5.val).map fun (qHd, q5) => ⟨qHd, x.qHu, {q5}, x.Q10⟩

omit [DecidableEq 𝓩] in
lemma completionsTopYukawa_nodup {S5 : Finset 𝓩} (x : ChargeSpectrum 𝓩) :
    (completionsTopYukawa S5 x).Nodup := by
  simp [completionsTopYukawa]
  refine Multiset.Nodup.map_on ?_ ?_
  intro (z1, z2) hz (y1, y2) hy h
  simp [eq_iff] at h
  simp_all
  exact (S5.product S5).nodup

lemma completions_eq_completionsTopYukawa_of_mem_minimallyAllowsTermsOfFinset [AddCommGroup 𝓩]
    {S5 S10 : Finset 𝓩} (x : ChargeSpectrum 𝓩)
    (hx : x ∈ minimallyAllowsTermsOfFinset S5 S10 .topYukawa) :
    completions S5 S10 x = completionsTopYukawa S5 x := by
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact completions_nodup S5 S10 x
  · exact completionsTopYukawa_nodup x
  intro a
  simp [minimallyAllowsTermsOfFinset] at hx
  obtain ⟨qHu, Q10, ⟨⟨h1, ⟨h2, hcard⟩⟩, h3⟩, rfl⟩ := hx
  simp [completions, completionsTopYukawa]
  have Q10_neq_zero : Q10 ≠ 0 := by
    by_contra hn
    subst hn
    simp at hcard
  simp [Q10_neq_zero]
  match a with
  | ⟨xqHd, xqHu, xQ5, xQ10⟩ =>
  simp [eq_iff]
  aesop

end ChargeSpectrum

end SU5

end SuperSymmetry
