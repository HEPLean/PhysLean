/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimalSuperSet
import PhysLean.Meta.TODO.Basic
/-!

# Phenomenologically closed sets of charge spectra

## i. Overview

The main goal of this file is to prove the lemma
`completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`, which
allows us to prove that a multiset of charge spectra contains all
phenomenologically viable charge spectra, given a finite set of allowed
`5`-bar and `10`-dimensional.

This lemma relies on the multiset of charge spectra satisfying a number of conditions,
which include three which are defined in this file: `IsPhenoClosedQ5`, `IsPhenoClosedQ10` and
`ContainsPhenoCompletionsOfMinimallyAllows`.


## ii. Key results

- `IsPhenoClosedQ5` : The proposition that a multiset of charges is phenomologically closed
  under addition of `5`-bar charges from a finite set `S5`.
- `IsPhenoClosedQ10` : The proposition that a multiset of charges is phenomologically closed
  under addition of `10`-dimensional charges from a finite set `S10`.
- `ContainsPhenoCompletionsOfMinimallyAllows` : The proposition that a multiset of charges
  contains all phenomenologically viable completions of charge spectra which permit the
  top Yukukwa.
- `completeMinSubset` : For a given `S5 S10 : Finset 𝓩`,
  the minimal multiset of charges which satifies the condition
  `ContainsPhenoCompletionsOfMinimallyAllows`.
- `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10` : A lemma for simplifying the proof
  that a multiset contains all phenomenologically viable charge spectra.
- `viableChargesMultiset` : A computable multiset containing all phenomenologically viable
  charge spectra for a given `S5 S10 : Finset 𝓩`.

## iii. Table of contents

- A. Phenomenologically closed under additions of 5-bar charges
  - A.1. Simplification using pheno-constrained due to additionial of 5-bar charge
- B. Phenomenologically closed under additions of 10d charges
  - B.1. Simplification using pheno-constrained due to additionial of 10d charge
- C. Prop for multiset containing all pheno-viable completions of charges permitting top Yukawa
  - C.1. Simplification using fast version of completions of charges permitting top Yukawa
  - C.2. Decidability of proposition
  - C.3. Monoticity of proposition
  - C.4. `completeMinSubset`: Minimial multiset with viable completions of top-permitting charges
    - C.4.1. The multiset `completeMinSubset` has no duplicates
    - C.4.2. The multiset `completeMinSubset` is minimal
    - C.4.3. The multiset `completeMinSubset` contains all completions
- D. Multisets containing all pheno-viable charge spectra
  - D.1. Lemma for simplifying proof that a multiset contains all pheno-viable charge spectra
  - D.2. Computable multiset containing all pheno-viable charge spectra

## iv. References

There are no known references for the material in this module.

-/
namespace SuperSymmetry

namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [DecidableEq 𝓩] [AddCommGroup 𝓩]

/-!

## A. Phenomenologically closed under additions of 5-bar charges

-/

/-- The proposition that for multiset set of charges `charges`,
  adding individual elements of `S5` to the `Q5` charges of elements of `charges` again
  leads to an element in `charges` or a charge which is phenomenologically constrained,
  or regenerates dangerous couplings with one singlet insertion. -/
def IsPhenoClosedQ5 (S5 : Finset 𝓩) (charges : Multiset (ChargeSpectrum 𝓩)) : Prop :=
  ∀ q5 ∈ S5, ∀ x ∈ charges,
    let y : ChargeSpectrum 𝓩 := ⟨x.qHd, x.qHu, insert q5 x.Q5, x.Q10⟩
    IsPhenoConstrained y ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1

/-!

### A.1. Simplification using pheno-constrained due to additionial of 5-bar charge

-/

lemma isPhenClosedQ5_of_isPhenoConstrainedQ5 {S5 : Finset 𝓩} {charges : Multiset (ChargeSpectrum 𝓩)}
    (h : ∀ q5 ∈ S5, ∀ x ∈ charges,
      let y : ChargeSpectrum 𝓩 := ⟨x.qHd, x.qHu, insert q5 x.Q5, x.Q10⟩
      IsPhenoConstrainedQ5 x q5 ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1) :
    IsPhenoClosedQ5 S5 charges := by
  intro q5 hq5 x hx
  rcases h q5 hq5 x hx with h'| h' | h'
  · left
    rw [isPhenoConstrained_insertQ5_iff_isPhenoConstrainedQ5]
    left
    exact h'
  · simp_all
  · simp_all

/-!

## B. Phenomenologically closed under additions of 10d charges

-/


/-- The proposition that for multiset set of charges `charges`,
  adding individual elements of `S10` to the `Q10` charges of elements of `charges` again
  leads to an element in `charges` or a charge which is phenomenologically constrained,
  or regenerates dangerous couplings with one singlet insertion. -/
def IsPhenoClosedQ10 (S10 : Finset 𝓩) (charges : Multiset (ChargeSpectrum 𝓩)) : Prop :=
  ∀ q10 ∈ S10, ∀ x ∈ charges,
    let y : ChargeSpectrum 𝓩 := ⟨x.qHd, x.qHu, x.Q5, insert q10 x.Q10⟩
    IsPhenoConstrained y ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1

/-!

### B.1. Simplification using pheno-constrained due to additionial of 10d charge

-/


lemma isPhenClosedQ10_of_isPhenoConstrainedQ10 {S10 : Finset 𝓩}
    {charges : Multiset (ChargeSpectrum 𝓩)}
    (h : ∀ q10 ∈ S10, ∀ x ∈ charges,
      let y : ChargeSpectrum 𝓩 := ⟨x.qHd, x.qHu, x.Q5, insert q10 x.Q10⟩
      IsPhenoConstrainedQ10 x q10 ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1) :
    IsPhenoClosedQ10 S10 charges := by
  intro q10 hq10 x hx
  have h' := h q10 hq10 x hx
  rcases h' with h'| h' | h'
  · left
    rw [isPhenoConstrained_insertQ10_iff_isPhenoConstrainedQ10]
    left
    exact h'
  · simp_all
  · simp_all

/-!

## C. Prop for multiset containing all pheno-viable completions of charges permitting top Yukawa

-/

open PotentialTerm
/-- The proposition that for multiset set of charges `charges` contains all
  viable completions of charges which allow the top Yukawa, given allowed values
  of `5`d and `10`d charges `S5` and `S10`. -/
def ContainsPhenoCompletionsOfMinimallyAllows (S5 S10 : Finset 𝓩)
    (charges : Multiset (ChargeSpectrum 𝓩)) : Prop :=
  ∀ x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa),
      ¬ x.IsPhenoConstrained → ∀ y ∈ completions S5 S10 x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1 → y ∈ charges

/-!

### C.1. Simplification using fast version of completions of charges permitting top Yukawa

-/

lemma containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa {S5 S10 : Finset 𝓩}
    {charges : Multiset (ChargeSpectrum 𝓩)} :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges ↔
    ∀ x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa),
    ∀ y ∈ completionsTopYukawa S5 x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1 → y ∈ charges := by
  rw [ContainsPhenoCompletionsOfMinimallyAllows]
  have h1 (x : ChargeSpectrum 𝓩) (hx : x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa)) :
    ¬ x.IsPhenoConstrained ↔ True := by
    simp only [iff_true]
    exact not_isPhenoConstrained_of_minimallyAllowsTermsOfFinset_topYukawa hx
  conv_lhs =>
    enter [x, hx]
    rw [completions_eq_completionsTopYukawa_of_mem_minimallyAllowsTermsOfFinset x hx]
    rw [h1 x hx]
  simp

/-!

### C.2. Decidability of proposition

-/

instance [DecidableEq 𝓩] {S5 S10 : Finset 𝓩} {charges : Multiset (ChargeSpectrum 𝓩)} :
    Decidable (ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges) :=
  decidable_of_iff _ (containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa).symm

/-!

### C.3. Monoticity of proposition

-/

lemma containsPhenoCompletionsOfMinimallyAllows_of_subset {S5 S10 : Finset 𝓩}
    {charges charges' : Multiset (ChargeSpectrum 𝓩)}
    (h' : ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges)
    (h : ∀ x ∈ charges, x ∈ charges') :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges' :=
  fun x hx hnot y h3 h4 => h y <| h' x hx hnot y h3 h4


/-!

### C.4. `completeMinSubset`: Minimial multiset with viable completions of top-permitting charges

-/
/-- For a given `S5 S10 : Finset 𝓩`, the minimal multiset of charges which satifies
  the condition `ContainsPhenoCompletionsOfMinimallyAllows`.
  That is to say, every multiset of charges which satifies
  `ContainsPhenoCompletionsOfMinimallyAllows` has `completeMinSubset` as a subset. -/
def completeMinSubset (S5 S10 : Finset 𝓩) : Multiset (ChargeSpectrum 𝓩) :=
  ((minimallyAllowsTermsOfFinset S5 S10 topYukawa).bind <|
      completionsTopYukawa S5).dedup.filter
    fun x => ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1

/-!

#### C.4.1. The multiset `completeMinSubset` has no duplicates

-/

lemma completeMinSubset_nodup {S5 S10 : Finset 𝓩} :
    (completeMinSubset S5 S10).Nodup := by
  simp [completeMinSubset]
  apply Multiset.Nodup.filter
  exact Multiset.nodup_dedup
      ((minimallyAllowsTermsOfFinset S5 S10 topYukawa).bind (completionsTopYukawa S5))

/-!

#### C.4.2. The multiset `completeMinSubset` is minimal

-/

lemma completeMinSubset_subset_iff_containsPhenoCompletionsOfMinimallyAllows
    (S5 S10 : Finset 𝓩) (charges : Multiset (ChargeSpectrum 𝓩)) :
    completeMinSubset S5 S10 ⊆ charges ↔
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges := by
  constructor
  · intro h
    rw [containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa]
    rw [Multiset.subset_iff] at h
    intro x hx y hy1 hy2
    apply h
    simp [completeMinSubset]
    simp_all
    use x
  · intro h y hy
    simp [completeMinSubset] at hy
    obtain ⟨⟨x, hx, hyx⟩, hy2⟩ := hy
    rw [containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa] at h
    exact h x hx y hyx hy2

/-!

#### C.4.3. The multiset `completeMinSubset` contains all completions

-/

lemma completeMinSubset_containsPhenoCompletionsOfMinimallyAllows (S5 S10 : Finset 𝓩) :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 (completeMinSubset S5 S10) := by
  rw [← completeMinSubset_subset_iff_containsPhenoCompletionsOfMinimallyAllows]
  simp

/-!

## D. Multisets containing all pheno-viable charge spectra

-/

/-!

### D.1. Lemma for simplifying proof that a multiset contains all pheno-viable charge spectra

-/

/-!
The multiset of charges `charges` contains precisely those charges (given a finite set
of allowed charges) which
- allow the top Yukawa term,
- are not phenomenologically constrained,
- do not generate dangerous couplings with one singlet insertion,
- and are complete,
if the following conditions hold:
- every element of `charges` allows the top Yukawa term,
- every element of `charges` is not phenomenologically constrained,
- every element of `charges` does not generate dangerous couplings with one singlet insertion,
- every element of `charges` is complete,
- `charges` is `IsPhenoClosedQ5` with respect to `S5`,
- `charges` is `IsPhenoClosedQ10` with respect to `S10`
- and satisfies `ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges`.
The importance of this lemma is that it is only regarding properties of finite-set `charges`
not of the whole space of possible charges.
-/
lemma completeness_of_isPhenoClosedQ5_isPhenoClosedQ10
    {S5 S10 : Finset 𝓩} {charges : Multiset (ChargeSpectrum 𝓩)}
    (charges_topYukawa : ∀ x ∈ charges, x.AllowsTerm .topYukawa)
    (charges_not_isPhenoConstrained : ∀ x ∈ charges, ¬ x.IsPhenoConstrained)
    (charges_yukawa : ∀ x ∈ charges, ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (charges_complete : ∀ x ∈ charges, x.IsComplete)
    (charges_isPhenoClosedQ5 : IsPhenoClosedQ5 S5 charges)
    (charges_isPhenoClosedQ10 : IsPhenoClosedQ10 S10 charges)
    (charges_exist : ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges)
    {x : ChargeSpectrum 𝓩} (hsub : x ∈ ofFinset S5 S10) :
    x ∈ charges ↔ AllowsTerm x .topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x := by
  constructor
  · /- Showing that if `x ∈ Charges` it satifies the conditions. -/
    intro h
    exact ⟨charges_topYukawa x h, charges_not_isPhenoConstrained x h, charges_yukawa x h,
      charges_complete x h⟩
  · intro ⟨hTop, hPheno, hY, hComplete⟩
    /- Showing that if `x ∉ charges` and `AllowsTerm x .topYukawa`,
      `¬ IsPhenoConstrained x`, ``¬ YukawaGeneratesDangerousAtLevel x 1`, `IsComplete x`,
      then `False`. -/
    by_contra hn
    suffices hnot : ¬ ((¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1) ∧
        AllowsTerm x topYukawa) by
      simp_all
    revert hn
    rw [not_and]
    simp only [hTop, not_true_eq_false, imp_false]
    suffices hmem : ∃ y ∈ charges, y ⊆ x by
      obtain ⟨y, y_mem, hyx⟩ := hmem
      refine subset_insert_filter_card_zero charges S5 S10 (fun x =>
        (¬x.IsPhenoConstrained ∧ ¬x.YukawaGeneratesDangerousAtLevel 1))
        ?_ ?_ y ?_ x hyx hsub ?_ ?_
      · simpa using fun x y hxy h1 h2 => yukawaGeneratesDangerousAtLevel_of_subset hxy <| h1
          fun hn => h2 <| isPhenoConstrained_mono hxy hn
      · intro x
        exact fun a => charges_complete x a
      · exact y_mem
      · intro q10
        rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
        simp only [Multiset.mem_filter, Multiset.mem_map, not_and, Decidable.not_not,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro z hz hzP h2
        have h1 := charges_isPhenoClosedQ10 q10 q10.2 z hz
        simp_all
      · intro q5
        rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
        simp only [Multiset.mem_filter, Multiset.mem_map, not_and, Decidable.not_not,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro z hz hzP h2
        have h1 := charges_isPhenoClosedQ5 q5 q5.2 z hz
        simp_all
    /- Getting the subset of `x` which minimally allows the top Yukawa. -/
    obtain ⟨y, hyMem, hysubsetx⟩ : ∃ y ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa),
        y ⊆ x := by
      rw [allowsTerm_iff_subset_minimallyAllowsTerm] at hTop
      obtain ⟨y, hPower, hIrre⟩ := hTop
      use y
      constructor
      · rw [← minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset]
        · exact hIrre
        · exact mem_ofFinset_antitone S5 S10 (by simpa using hPower) hsub
      · simpa using hPower
    obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete S5 S10 y x hysubsetx hsub hComplete
    use z
    constructor
    · refine charges_exist y hyMem ?_ z hz1 ?_
      · by_contra hn
        have := isPhenoConstrained_mono hysubsetx hn
        simp_all
      · apply And.intro
        · by_contra hn
          have := isPhenoConstrained_mono hz2 hn
          simp_all
        · by_contra hn
          have := yukawaGeneratesDangerousAtLevel_of_subset hz2 hn
          simp_all
    · simp_all

/-!

### D.2. Computable multiset containing all pheno-viable charge spectra

-/

TODO "JGVOQ" "Make the result `viableChargesMultiset` a safe definition, that is to
  say proof that the recursion terminates."

/-- All charges, for a given `S5 S10 : Finset 𝓩`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  This is the unique multiset without duplicates which satifies:
  `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`.

  Note this is fast for evaluation, but to slow with `decide`. -/
unsafe def viableChargesMultiset (S5 S10 : Finset 𝓩) :
    Multiset (ChargeSpectrum 𝓩) := (aux (completeMinSubset S5 S10) (completeMinSubset S5 S10)).dedup
where
  /-- Auxillary recursive function to define `viableChargesMultiset`. -/
  aux : Multiset (ChargeSpectrum 𝓩) → Multiset (ChargeSpectrum 𝓩) → Multiset (ChargeSpectrum 𝓩) :=
    fun all add =>
      /- Note that aux terminates since that every iteration the size of `all` increases,
        unless it terminates that round, but `all` is bounded in size by the number
        of allowed charges given `S5` and `S10`. -/
      if add = ∅ then all else
      let s := add.bind fun x => (minimalSuperSet S5 S10 x).val
      let s2 := s.filter fun y => y ∉ all ∧
        ¬ IsPhenoConstrained y ∧ ¬ YukawaGeneratesDangerousAtLevel y 1
      aux (all + s2) s2

end ChargeSpectrum

end SU5

end SuperSymmetry
