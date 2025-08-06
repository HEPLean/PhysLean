/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Yukawa.Elems
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Yukawa
/-!

# Complete of `nonPhenoConstrainedCharges I`

We show that the `nonPhenoConstrainedCharges I` is complete, that is,
it contains every charge in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`
which is not pheno-constrained, permits a top yukawa and is complete.

## Method

The method of our proof is the following.

1. We define `completionTopYukawa` which contains all `completions` of elements
  which minimally allow the top Yukawa, which are not pheno-constrained. We show
  that every charge in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`
  which is not pheno-constrained and complete must contain an element
  of `completionTopYukawaSame` as a subset.
2. We show that `completionTopYukawa I` is a subset of `nonPhenoConstrainedCharges I`.
3. We then use the fact that one can not add to any charge in `nonPhenoConstrainedCharges`
  another `Q5` or `Q10` without remaining in `nonPhenoConstrainedCharges` or allowing
  a pheno-constraining term to be present.

This proof of completeness is more like a certification of completeness, rather
than a constructive proof.

## Key results

- `not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge` which specifies
  the completeness of the tree of charges `nonPhenoConstrainedCharges I`.
-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig

open PhysLean Tree

#eval
    (((minimallyAllowsTermsOfFinset nextToNearestNeighbor.allowedBarFiveCharges
        nextToNearestNeighbor.allowedTenCharges topYukawa).bind <|
      completions nextToNearestNeighbor.allowedBarFiveCharges nextToNearestNeighbor.allowedTenCharges).dedup.filter
    fun x => ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1)


/--
The tree of charges which contains all `completions` of
charges which minimally allow the top Yukawa,
which are not pheno-constrained.

This can be constructed via

#eval FourTree.fromMultiset <|
    ((minimallyAllowsTermsOfFinset same.allowedBarFiveCharges
        same.allowedTenCharges topYukawa).bind <|
      completions same.allowedBarFiveCharges same.allowedTenCharges).dedup.filter
    fun x => ¬ IsPhenoConstrained x
-/
private def completionTopYukawa (I : CodimensionOneConfig) : Multiset (Charges ℤ) :=
  match I with
  | same => {(some (-2), some (-3), {2}, {-3, 0}), (some (-1), some (-3), {1}, {-3, 0}),
    (some 1, some (-3), {-1}, {-3, 0}), (some 1, some (-3), {2}, {-3, 0}),
    (some 2, some (-3), {-2}, {-3, 0}), (some 2, some (-3), {1}, {-3, 0}),
    (some (-3), some (-2), {0}, {-1}), (some (-3), some (-2), {1}, {-1}),
    (some (-3), some (-2), {2}, {-1}), (some (-1), some (-2), {0}, {-1}),
    (some (-1), some (-2), {1}, {-1}), (some (-1), some (-2), {2}, {-1}),
    (some 0, some (-2), {-3}, {-1}), (some 0, some (-2), {-1}, {-1}),
    (some 0, some (-2), {1}, {-1}), (some 0, some (-2), {2}, {-1}),
    (some 1, some (-2), {-3}, {-1}), (some 1, some (-2), {-1}, {-1}),
    (some 1, some (-2), {0}, {-1}), (some 1, some (-2), {2}, {-1}),
    (some 2, some (-2), {-3}, {-1}), (some 2, some (-2), {-1}, {-1}),
    (some 2, some (-2), {0}, {-1}), (some 2, some (-2), {1}, {-1}),
    (some (-3), some (-2), {3}, {-2, 0}), (some (-1), some (-2), {3}, {-2, 0}),
    (some 3, some (-2), {-3}, {-2, 0}), (some (-1), some (-2), {0}, {-3, 1}),
    (some 0, some (-2), {-1}, {-3, 1}), (some 0, some (-2), {3}, {-3, 1}),
    (some 3, some (-2), {0}, {-3, 1}), (some (-2), some 0, {-1}, {-3, 3}),
    (some (-2), some 0, {1}, {-3, 3}), (some (-1), some 0, {-2}, {-3, 3}),
    (some (-1), some 0, {2}, {-3, 3}), (some 1, some 0, {-2}, {-3, 3}),
    (some 1, some 0, {2}, {-3, 3}), (some 2, some 0, {-1}, {-3, 3}),
    (some 2, some 0, {1}, {-3, 3}), (some (-2), some 2, {-1}, {1}),
    (some (-2), some 2, {0}, {1}), (some (-2), some 2, {1}, {1}),
    (some (-2), some 2, {3}, {1}), (some (-1), some 2, {-2}, {1}),
    (some (-1), some 2, {0}, {1}), (some (-1), some 2, {1}, {1}),
    (some (-1), some 2, {3}, {1}), (some 0, some 2, {-2}, {1}),
    (some 0, some 2, {-1}, {1}), (some 0, some 2, {1}, {1}),
    (some 0, some 2, {3}, {1}), (some 1, some 2, {-2}, {1}),
    (some 1, some 2, {-1}, {1}), (some 1, some 2, {0}, {1}),
    (some 3, some 2, {-2}, {1}), (some 3, some 2, {-1}, {1}),
    (some 3, some 2, {0}, {1}), (some (-3), some 2, {3}, {0, 2}),
    (some 1, some 2, {-3}, {0, 2}), (some 3, some 2, {-3}, {0, 2}),
    (some (-3), some 2, {0}, {-1, 3}), (some 0, some 2, {-3}, {-1, 3}),
    (some 0, some 2, {1}, {-1, 3}), (some 1, some 2, {0}, {-1, 3}),
    (some (-2), some 3, {-1}, {0, 3}), (some (-2), some 3, {2}, {0, 3}),
    (some (-1), some 3, {-2}, {0, 3}), (some (-1), some 3, {1}, {0, 3}),
    (some 1, some 3, {-1}, {0, 3}), (some 2, some 3, {-2}, {0, 3})}
  | nearestNeighbor => {(some (-9), some (-14), {-4}, {-7}), (some (-9), some (-14), {1}, {-7}),
    (some (-9), some (-14), {6}, {-7}), (some (-9), some (-14), {11}, {-7}),
    (some (-4), some (-14), {-9}, {-7}), (some (-4), some (-14), {1}, {-7}),
    (some (-4), some (-14), {6}, {-7}), (some (-4), some (-14), {11}, {-7}),
    (some 1, some (-14), {-9}, {-7}), (some 1, some (-14), {-4}, {-7}),
    (some 1, some (-14), {6}, {-7}), (some 1, some (-14), {11}, {-7}),
    (some 6, some (-14), {-9}, {-7}), (some 6, some (-14), {-4}, {-7}),
    (some 6, some (-14), {1}, {-7}), (some 6, some (-14), {11}, {-7}),
    (some 11, some (-14), {-9}, {-7}), (some 11, some (-14), {-4}, {-7}),
    (some 11, some (-14), {1}, {-7}), (some 11, some (-14), {6}, {-7}),
    (some 11, some (-14), {-9}, {-12, -2}), (some 1, some (-9), {11}, {-12, 3}),
    (some 11, some (-9), {1}, {-12, 3}), (some (-14), some (-4), {-9}, {-2}),
    (some (-14), some (-4), {11}, {-2}), (some (-9), some (-4), {-14}, {-2}),
    (some (-9), some (-4), {11}, {-2}), (some 1, some (-4), {-14}, {-2}),
    (some 1, some (-4), {11}, {-2}), (some 11, some (-4), {-14}, {-2}),
    (some 11, some (-4), {-9}, {-2}), (some (-9), some 1, {-4}, {-12, 13}),
    (some (-4), some 1, {-9}, {-12, 13}), (some 6, some 1, {-9}, {-12, 13}),
    (some (-14), some 6, {-4}, {3}), (some (-14), some 6, {1}, {3}),
    (some (-14), some 6, {11}, {3}), (some (-4), some 6, {-14}, {3}),
    (some (-4), some 6, {1}, {3}), (some (-4), some 6, {11}, {3}),
    (some 1, some 6, {-14}, {3}), (some 1, some 6, {-4}, {3}),
    (some 11, some 6, {-14}, {3}), (some 11, some 6, {-4}, {3}),
    (some (-9), some 6, {-4}, {-7, 13}), (some (-4), some 6, {-9}, {-7, 13}),
    (some (-4), some 6, {11}, {-7, 13}), (some 11, some 6, {-4}, {-7, 13})}
  | nextToNearestNeighbor => {(some (-13), some (-8), {7}, {-4}),
    (some (-3), some (-8), {7}, {-4}), (some 2, some (-8), {-13}, {-4}),
    (some 2, some (-8), {-3}, {-4}), (some 2, some (-8), {7}, {-4}),
    (some 7, some (-8), {-13}, {-4}), (some 7, some (-8), {-3}, {-4}),
    (some (-13), some 2, {-8}, {1}), (some (-13), some 2, {7}, {1}),
    (some (-13), some 2, {12}, {1}), (some (-8), some 2, {-13}, {1}),
    (some (-8), some 2, {7}, {1}), (some 7, some 2, {-13}, {1}),
    (some 7, some 2, {-8}, {1}), (some 7, some 2, {12}, {1}),
    (some 12, some 2, {-13}, {1}), (some 12, some 2, {7}, {1}),
    (some (-8), some 2, {-3}, {-9, 11}), (some (-3), some 2, {-8}, {-9, 11}),
    (some (-3), some 2, {12}, {-9, 11}), (some 12, some 2, {-3}, {-9, 11}),
    (some (-13), some 12, {-8}, {6}), (some (-13), some 12, {2}, {6}),
    (some (-13), some 12, {7}, {6}), (some (-8), some 12, {-13}, {6}),
    (some (-8), some 12, {2}, {6}), (some (-8), some 12, {7}, {6}),
    (some (-3), some 12, {-13}, {6}), (some (-3), some 12, {-8}, {6}),
    (some (-3), some 12, {2}, {6}), (some (-3), some 12, {7}, {6}),
    (some 2, some 12, {-13}, {6}), (some 2, some 12, {-8}, {6}),
    (some 2, some 12, {7}, {6}), (some 7, some 12, {-13}, {6}),
    (some 7, some 12, {-8}, {6}), (some 7, some 12, {2}, {6})}

lemma completionTopYukawa_complete_of_same :
    ∀ x ∈ (minimallyAllowsTermsOfFinset CodimensionOneConfig.same.allowedBarFiveCharges
      CodimensionOneConfig.same.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions same.allowedBarFiveCharges same.allowedTenCharges x, ¬ y.IsPhenoConstrained
    ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ completionTopYukawa .same := by
  decide

lemma completionTopYukawa_complete_of_nearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nearestNeighbor.allowedBarFiveCharges
      nearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ completionTopYukawa .nearestNeighbor := by
  decide

lemma completionTopYukawa_complete_of_nextToNearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nextToNearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nextToNearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nextToNearestNeighbor.allowedBarFiveCharges
      nextToNearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ completionTopYukawa .nextToNearestNeighbor := by
  decide

lemma completionTopYukawa_complete {I : CodimensionOneConfig} (x : Charges)
    (hx : x ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
      I.allowedTenCharges topYukawa))
    (hPheno : ¬ x.IsPhenoConstrained) :
    ∀ y ∈ completions I.allowedBarFiveCharges I.allowedTenCharges x, ¬ y.IsPhenoConstrained
    ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ completionTopYukawa I := by
  cases I
  case same => exact completionTopYukawa_complete_of_same x hx hPheno
  case nearestNeighbor => exact completionTopYukawa_complete_of_nearestNeighbor x hx hPheno
  case nextToNearestNeighbor => exact
    completionTopYukawa_complete_of_nextToNearestNeighbor x hx hPheno

set_option maxRecDepth 2000 in
lemma exists_subset_completionTopYukawa_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (htopYukawa : AllowsTerm x topYukawa)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) : ∃ (y : Charges), y ∈ completionTopYukawa I ∧ y ⊆ x := by
  have hIrreducible :
        ∃ y ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
        I.allowedTenCharges topYukawa), y ⊆ x := by
      rw [allowsTerm_iff_subset_minimallyAllowsTerm] at htopYukawa
      obtain ⟨y, hPower, hIrre⟩ := htopYukawa
      use y
      constructor
      · rw [← minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset]
        · exact hIrre
        · simp at hPower
          exact mem_ofFinset_antitone I.allowedBarFiveCharges I.allowedTenCharges hPower hsub
      · simpa using hPower
  obtain ⟨y, hyMem, hysubsetx⟩ := hIrreducible
  obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete
    I.allowedBarFiveCharges I.allowedTenCharges y x hysubsetx hsub hcomplete
  use z
  constructor
  · refine completionTopYukawa_complete y hyMem ?_ z hz1 ?_
    · by_contra hn
      have h' := isPhenoConstrained_mono hysubsetx hn
      simp_all
    · apply And.intro
      · by_contra hn

        have h' := isPhenoConstrained_mono hz2 hn
        simp_all
      · by_contra hn
        have h' := yukawaGeneratesDangerousAtLevel_of_subset hz2 hn
        simp_all
  · simp_all

set_option maxRecDepth 2000 in
lemma completionTopYukawa_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ (completionTopYukawa I), x ∈ nonPhenoConstrainedCharges I := by
  decide +revert

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_mem_nonPhenoConstrainedCharges {x : Charges}
    (hx : ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) :
    x ∉ nonPhenoConstrainedCharges I → ¬ ((¬ IsPhenoConstrained x ∧
    ¬ YukawaGeneratesDangerousAtLevel x 1) ∧
      AllowsTerm x topYukawa) := by
  by_cases hn : ¬ (AllowsTerm x topYukawa)
  · simp [hn]
  rw [not_and]
  simp only [hn, imp_false]
  simp at hn
  obtain ⟨y, y_mem, hyx⟩ :=
    exists_subset_completionTopYukawa_of_not_isPhenoConstrained hx hn hsub hcomplete

  refine subset_insert_filter_card_zero (nonPhenoConstrainedCharges I)
    I.allowedBarFiveCharges I.allowedTenCharges (fun x =>
      (¬x.IsPhenoConstrained ∧ ¬x.YukawaGeneratesDangerousAtLevel 1))
    ?_ ?_ y ?_ x hyx hsub ?_ ?_
  · intro x y hxy
    simp only [Decidable.not_not]
    simp
    intro h1 h2
    apply yukawaGeneratesDangerousAtLevel_of_subset hxy
    apply h1
    intro hn
    apply h2
    exact isPhenoConstrained_mono hxy hn
  · intro x
    exact fun a => isComplete_of_mem_nonPhenoConstrainedCharge I x a
  · apply completionTopYukawa_subset_nonPhenoConstrainedCharges
    exact y_mem
  · intro q10
    rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
    simp
    intro z hz hzP h2
    have h1 := phenoInsert_Q10 I q10 q10.2 z hz
    simp_all
  · intro q5
    rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
    simp
    intro z hz hzP h2
    have h1 := phenoInsert_Q5 I q5 q5.2 z hz
    simp_all

lemma not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge {x : Charges}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x ↔
    x ∈ nonPhenoConstrainedCharges I := by
  constructor
  · intro ⟨hTop, hPheno, hY, hComplete⟩
    by_contra hn
    apply not_isPhenoConstrained_mem_nonPhenoConstrainedCharges ⟨hPheno, hY⟩ hsub hComplete hn
    simp_all
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharge I x h
    · exact not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges I x h
    · exact not_yukawaGeneratesDangerousAtLevel_one_of_mem_nonPhenoConstrainedCharges I x h
    · exact isComplete_of_mem_nonPhenoConstrainedCharge I x h

end Charges

end SU5U1

end FTheory
