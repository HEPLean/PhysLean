/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Yukawa
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimalSuperSet
import PhysLean.Meta.TODO.Basic
/-!

# Phenomenologically closed sets of charges

In this module we define a number of propositions related to the phenomenological closure of
sets of charges.

One of the key results within this module is the lemma
`completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`, which gives a quick way to
check whether a set of charges contains precisely those charges which
- allow the top Yukawa term,
- are not phenomenologically constrained,
- do not generate dangerous couplings with one singlet insertion,
- and are complete,
given allowed values of `5`d and `10`d charges `S5` and `S10`.
This result can be used for specific sets of charges `S5` and `S10`, along with
some results proved by `decide`.

-/
namespace SuperSymmetry

namespace SU5

namespace Charges

variable {𝓩 : Type} [DecidableEq 𝓩] [AddCommGroup 𝓩]

/-!

## IsPhenoClosedQ5

-/

/-- The proposition that for multiset set of charges `charges`,
  adding individual elements of `S5` to the `Q5` charges of elements of `charges` again
  leads to an element in `charges` or a charge which is phenomenologically constrained,
  or regenerates dangerous couplings with one singlet insertion. -/
def IsPhenoClosedQ5 (S5 : Finset 𝓩) (charges : Multiset (Charges 𝓩)) : Prop :=
  ∀ q5 ∈ S5, ∀ x ∈ charges,
    let y : Charges 𝓩 := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1

lemma isPhenClosedQ5_of_isPhenoConstrainedQ5 {S5 : Finset 𝓩} {charges : Multiset (Charges 𝓩)}
    (h : ∀ q5 ∈ S5, ∀ x ∈ charges,
      let y : Charges 𝓩 := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
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

## IsPhenoClosedQ10

-/

/-- The proposition that for multiset set of charges `charges`,
  adding individual elements of `S10` to the `Q10` charges of elements of `charges` again
  leads to an element in `charges` or a charge which is phenomenologically constrained,
  or regenerates dangerous couplings with one singlet insertion. -/
def IsPhenoClosedQ10 (S10 : Finset 𝓩) (charges : Multiset (Charges 𝓩)) : Prop :=
  ∀ q10 ∈ S10, ∀ x ∈ charges,
    let y : Charges 𝓩 := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ charges ∨ YukawaGeneratesDangerousAtLevel y 1

lemma isPhenClosedQ10_of_isPhenoConstrainedQ10 {S10 : Finset 𝓩} {charges : Multiset (Charges 𝓩)}
    (h : ∀ q10 ∈ S10, ∀ x ∈ charges,
      let y : Charges 𝓩 := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
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

open PotentialTerm

/-- The proposition that for multiset set of charges `charges` contains all
  viable completions of charges which allow the top Yukawa, given allowed values
  of `5`d and `10`d charges `S5` and `S10`. -/
def ContainsPhenoCompletionsOfMinimallyAllows (S5 S10 : Finset 𝓩) (charges : Multiset (Charges 𝓩)) :
    Prop := ∀ x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa),
      ¬ x.IsPhenoConstrained → ∀ y ∈ completions S5 S10 x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1 → y ∈ charges

lemma containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa {S5 S10 : Finset 𝓩}
    {charges : Multiset (Charges 𝓩)} :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges ↔
    ∀ x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa),
    ∀ y ∈ completionsTopYukawa S5 x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1 → y ∈ charges := by
  rw [ContainsPhenoCompletionsOfMinimallyAllows]
  have h1 (x : Charges 𝓩) (hx : x ∈ (minimallyAllowsTermsOfFinset S5 S10 topYukawa)) :
    ¬ x.IsPhenoConstrained ↔ True := by
    simp only [iff_true]
    exact not_isPhenoConstrained_of_minimallyAllowsTermsOfFinset_topYukawa hx
  conv_lhs =>
    enter [x, hx]
    rw [completions_eq_completionsTopYukawa_of_mem_minimallyAllowsTermsOfFinset x hx]
    rw [h1 x hx]
  simp

instance [DecidableEq 𝓩] {S5 S10 : Finset 𝓩} {charges : Multiset (Charges 𝓩)} :
    Decidable (ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges) :=
  decidable_of_iff _ (containsPhenoCompletionsOfMinimallyAllows_iff_completionsTopYukawa).symm

lemma containsPhenoCompletionsOfMinimallyAllows_of_subset {S5 S10 : Finset 𝓩}
    {charges charges' : Multiset (Charges 𝓩)}
    (h' : ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges)
    (h : ∀ x ∈ charges, x ∈ charges') :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges' :=
  fun x hx hnot y h3 h4 => h y <| h' x hx hnot y h3 h4

/-!

## Completeness of isPhenoClosedQ5 and isPhenoClosedQ10

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
    {S5 S10 : Finset 𝓩} {charges : Multiset (Charges 𝓩)}
    (charges_topYukawa : ∀ x ∈ charges, x.AllowsTerm .topYukawa)
    (charges_not_isPhenoConstrained : ∀ x ∈ charges, ¬ x.IsPhenoConstrained)
    (charges_yukawa : ∀ x ∈ charges, ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (charges_complete : ∀ x ∈ charges, x.IsComplete)
    (charges_isPhenoClosedQ5 : IsPhenoClosedQ5 S5 charges)
    (charges_isPhenoClosedQ10 : IsPhenoClosedQ10 S10 charges)
    (charges_exist : ContainsPhenoCompletionsOfMinimallyAllows S5 S10 charges)
    {x : Charges 𝓩} (hsub : x ∈ ofFinset S5 S10) :
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

## Definitions of multisets which are phenomenologically closed

-/

/-- For a given `S5 S10 : Finset 𝓩`, the minimal multiset of charges which satifies
  the condition `ContainsPhenoCompletionsOfMinimallyAllows`.
  That is to say, every multiset of charges which satifies
  `ContainsPhenoCompletionsOfMinimallyAllows` has `completeMinSubset` as a subset. -/
def completeMinSubset (S5 S10 : Finset 𝓩) : Multiset (Charges 𝓩) :=
  ((minimallyAllowsTermsOfFinset S5 S10 topYukawa).bind <|
      completionsTopYukawa S5).dedup.filter
    fun x => ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1

lemma completeMinSubset_nodup {S5 S10 : Finset 𝓩} :
    (completeMinSubset S5 S10).Nodup := by
  simp [completeMinSubset]
  apply Multiset.Nodup.filter
  exact Multiset.nodup_dedup
      ((minimallyAllowsTermsOfFinset S5 S10 topYukawa).bind (completionsTopYukawa S5))

lemma completeMinSubset_subset_iff_containsPhenoCompletionsOfMinimallyAllows
    (S5 S10 : Finset 𝓩) (charges : Multiset (Charges 𝓩)) :
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

lemma completeMinSubset_containsPhenoCompletionsOfMinimallyAllows (S5 S10 : Finset 𝓩) :
    ContainsPhenoCompletionsOfMinimallyAllows S5 S10 (completeMinSubset S5 S10) := by
  rw [← completeMinSubset_subset_iff_containsPhenoCompletionsOfMinimallyAllows]
  simp

TODO "JGVOQ" "Make the result `viableChargesMultiset` a safe definition, that is to
  say proof that the recursion terminates."

/-- All charges, for a given `S5 S10 : Finset 𝓩`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  This is the unique multiset without duplicates which satifies:
  `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`.

  Note this is fast for evaluation, but to slow with `decide`. -/
unsafe def viableChargesMultiset (S5 S10 : Finset 𝓩) :
    Multiset (Charges 𝓩) := (aux (completeMinSubset S5 S10) (completeMinSubset S5 S10)).dedup
where
  /-- Auxillary recursive function to define `viableChargesMultiset`. -/
  aux : Multiset (Charges 𝓩) → Multiset (Charges 𝓩) → Multiset (Charges 𝓩) :=
    fun all add =>
      /- Note that aux terminates since that every iteration the size of `all` increases,
        unless it terminates that round, but `all` is bounded in size by the number
        of allowed charges given `S5` and `S10`. -/
      if add = ∅ then all else
      let s := add.bind fun x => (minimalSuperSet S5 S10 x).val
      let s2 := s.filter fun y => y ∉ all ∧
        ¬ IsPhenoConstrained y ∧ ¬ YukawaGeneratesDangerousAtLevel y 1
      aux (all + s2) s2

end Charges

end SU5

end SuperSymmetry
