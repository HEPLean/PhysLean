/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Basic
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Completeness
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Basic
/-!

# Complete of `nonPhenoConstrainedCharges .same`

We show that the `nonPhenoConstrainedCharges .same` is complete, that is,
it contains every charge in `ofFinset same.allowedBarFiveCharges same.allowedTenCharges`
which is not pheno-constrained and complete.

## Method

The method of our proof is the following.

1. We define `completionTopYukawaSame` which contains all `completions` of elements
  `irreducibleElems .same topYukawa` which are not pheno-constrained. We show
  that every charge  in `ofFinset same.allowedBarFiveCharges same.allowedTenCharges`
  which is not pheno-constrained and complete must contain an element
  of `completionTopYukawaSame` as a subset.
2. We then define `addOneTopYukawaSame` which contains all `minimalSuperSet` of elements
  `completionTopYukawaSame` which are not pheno-constrained.
  We show that every charge in `ofFinset same.allowedBarFiveCharges same.allowedTenCharges`
  which is not pheno-constrained and complete must contain an element of `addOneTopYukawaSame`
  or be in `completionTopYukawaSame`.
3. We repeat process above for `addTwoTopYukawaSame` and `addThreeTopYukawaSame`, repeating
  the process once more would lead to the empty set.
4. We then show that every charge of `ofFinset same.allowedBarFiveCharges same.allowedTenCharges`
  which is not pheno-constrained and complete must be in
  `completionTopYukawaSame`, `addOneTopYukawaSame`, `addTwoTopYukawaSame` or
  `addThreeTopYukawaSame`.
5. We show that every element of `completionTopYukawaSame`, `addOneTopYukawaSame`,
  `addTwoTopYukawaSame` and `addThreeTopYukawaSame` is in
  `nonPhenoConstrainedCharges .same`.

## Key results

- `not_isPhenoConstrained_mem_nonPhenoConstrainedCharges_of_same` which specifies
  the completeness of the tree of charges `nonPhenoConstrainedCharges .same`.
-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges
open PotentialTerm ChargeProfile
open CodimensionOneConfig

open Tree Leaf Twig Branch Trunk

set_option maxRecDepth 2000


lemma nonPhenoConstrainedCharges_insertQ10_filter (I : CodimensionOneConfig) :  ∀ (q10 : { x // x ∈ I.allowedTenCharges }),
    Multiset.filter (fun x => ¬x.IsPhenoConstrained)
    ((nonPhenoConstrainedCharges I).insertQ10 ↑q10).toMultiset = ∅ := by
  intro ⟨q10, hq10⟩
  simp
  rw [Multiset.filter_eq_nil]
  intro C hC
  intro hn
  have hmemP : C ∈ (phenoInsertQ10 (nonPhenoConstrainedCharges I) q10) := by
    rw [← mem_iff_mem_toMultiset] at hC
    obtain ⟨qHd, qHu, Q5, Q10, rfl, h1⟩ := exists_of_mem_insertQ10 C q10 hC
    apply mem_phenoInsertQ10_of_mem_isPresent
    · exact hC
    simp [IsPhenoConstrained, toChargeProfile] at hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hc
      have hc' : IsPresent K2 (qHd, qHu, insert q10 Q10)  := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent Λ (Q5, insert q10 Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent W1 (Q5, insert q10 Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent K1 (Q5, insert q10 Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' :  IsPresent W2 (qHd, insert q10 Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
  have hemp : ((nonPhenoConstrainedCharges I).phenoInsertQ10 q10).toMultiset = ∅ := by
    rw [Multiset.empty_eq_zero, ← Multiset.card_eq_zero]
    have hx := nonPhenoConstrainedCharges_phenoInsertQ10_card_zero I q10 hq10
    rw [← hx]
    rw [Tree.card_eq_toMultiset_card]
  rw [mem_iff_mem_toMultiset] at hmemP
  simp_all

lemma nonPhenoConstrainedCharges_insertQ5_filter (I : CodimensionOneConfig)  : ∀ (q5 : { x // x ∈ I.allowedBarFiveCharges }),
    Multiset.filter (fun x => ¬x.IsPhenoConstrained)
    ((nonPhenoConstrainedCharges I).insertQ5 ↑q5).toMultiset = ∅ := by
  intro ⟨q5, hq5⟩
  simp
  rw [Multiset.filter_eq_nil]
  intro C hC
  intro hn
  have hmemP : C ∈ (phenoInsertQ5 (nonPhenoConstrainedCharges I) q5) := by
    rw [← mem_iff_mem_toMultiset] at hC
    obtain ⟨qHd, qHu, Q5, Q10, rfl, h1⟩ := exists_of_mem_insertQ5 C q5 hC
    apply mem_phenoInsertQ5_of_mem_isPresent
    · exact hC
    simp [IsPhenoConstrained, toChargeProfile] at hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hc
      have hc' : IsPresent β (qHu, insert q5 Q5) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent W4 (qHd, qHu, insert q5 Q5) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent W1 (insert q5 Q5, Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : IsPresent K1 (insert q5 Q5, Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' :  IsPresent Λ (insert q5 Q5, Q10) := by
        apply isPresent_of_subset _ hc
        simp [Subset]
      simp_all
  have hemp : ((nonPhenoConstrainedCharges I).phenoInsertQ5 q5).toMultiset = ∅ := by
    rw [Multiset.empty_eq_zero, ← Multiset.card_eq_zero]
    have hx := nonPhenoConstrainedCharges_phenoInsertQ5_card_zero I q5 hq5
    rw [← hx]
    rw [Tree.card_eq_toMultiset_card]
  rw [mem_iff_mem_toMultiset] at hmemP
  simp_all
/-!

## The tree of charges `completionTopYukawaSame`

-/


/--
The tree of charges which contains all `completions` of elements `irreducibleElems .same topYukawa`
which are not pheno-constrained.

This can be constructed via

Tree.fromMultiset ((((irreducibleElems same topYukawa).map (fromChargeProfile topYukawa)).bind
    (completions same.allowedBarFiveCharges same.allowedTenCharges)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
-/
def completionTopYukawa (I : CodimensionOneConfig) : Tree :=
  match I with
  | same => root {trunk (some (-3)) {branch (some 3) {twig {-1} {leaf {-2, -1}}, twig {0} {leaf {-2, -1}}, twig {2} {leaf {-2, -1}}},
  branch (some (-2)) {twig {0} {leaf {-2, -1}}, twig {1} {leaf {-3, 0}}, twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
  branch (some (-1)) {twig {0} {leaf {-2, -1}}, twig {-2} {leaf {-3, 0}}, twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
  branch (some 0) {twig {-2} {leaf {-3, 0}},
   twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
   twig {1} {leaf {-3, 0}},
   twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
  branch (some 1) {twig {0} {leaf {-2, -1}},
   twig {-2} {leaf {-3, 0}},
   twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
   twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
  branch (some 2) {twig {0} {leaf {-2, -1}}, twig {-2} {leaf {-3, 0}}, twig {-1} {leaf {-2, -1}, leaf {-3, 0}}, twig {1} {leaf {-3, 0}}}},
 trunk (some (-2)) {branch (some 1) {twig {0} {leaf {-1}},
   twig {2} {leaf {-1}},
   twig {-3} {leaf {-1}, leaf {-2, 0}},
   twig {-1} {leaf {-1}, leaf {-2, 0}},
   twig {3} {leaf {-2, 0}}},
  branch (some (-3)) {twig {1} {leaf {-1}},
   twig {2} {leaf {-1}},
   twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}},
   twig {0} {leaf {-1}, leaf {-3, 1}},
   twig {3} {leaf {-2, 0}, leaf {-3, 1}}},
  branch (some (-1)) {twig {1} {leaf {-1}}, twig {2} {leaf {-1}}, twig {-3} {leaf {-1}, leaf {-2, 0}}, twig {3} {leaf {-2, 0}, leaf {-3, 1}}},
  branch (some 0) {twig {1} {leaf {-1}},
   twig {-3} {leaf {-1}, leaf {-2, 0}},
   twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}},
   twig {3} {leaf {-2, 0}, leaf {-3, 1}}},
  branch (some 2) {twig {-3} {leaf {-1}},
   twig {1} {leaf {-1}},
   twig {-1} {leaf {-1}, leaf {-3, 1}},
   twig {0} {leaf {-1}, leaf {-3, 1}},
   twig {3} {leaf {-3, 1}}},
  branch (some 3) {twig {-3} {leaf {-2, 0}}, twig {-1} {leaf {-2, 0}, leaf {-3, 1}}, twig {0} {leaf {-3, 1}}}},
 trunk (some (-1)) {branch (some 0) {twig {-3} {leaf {-1, 0}}},
  branch (some 3) {twig {-3} {leaf {-1, 0}}},
  branch (some (-3)) {twig {-2} {leaf {-2, 1}}},
  branch (some 1) {twig {-2} {leaf {-2, 1}}},
  branch (some 2) {twig {-2} {leaf {-2, 1}}}},
 trunk (some 0) {branch (some (-3)) {twig {3} {leaf {-2, 2}}},
  branch (some 3) {twig {-3} {leaf {-2, 2}}},
  branch (some (-2)) {twig {-1} {leaf {-3, 3}}, twig {1} {leaf {-3, 3}}, twig {2} {leaf {-3, 3}}},
  branch (some (-1)) {twig {-3} {leaf {-2, 2}}, twig {3} {leaf {-2, 2}}, twig {1} {leaf {-3, 3}}, twig {2} {leaf {-3, 3}}},
  branch (some 1) {twig {-3} {leaf {-2, 2}}, twig {3} {leaf {-2, 2}}, twig {-2} {leaf {-3, 3}}, twig {-1} {leaf {-3, 3}}},
  branch (some 2) {twig {-2} {leaf {-3, 3}}, twig {-1} {leaf {-3, 3}}, twig {1} {leaf {-3, 3}}}},
 trunk (some 1) {branch (some (-3)) {twig {3} {leaf {0, 1}}},
  branch (some 0) {twig {3} {leaf {0, 1}}},
  branch (some (-2)) {twig {2} {leaf {-1, 2}}},
  branch (some (-1)) {twig {2} {leaf {-1, 2}}},
  branch (some 3) {twig {2} {leaf {-1, 2}}}},
 trunk (some 2) {branch (some (-1)) {twig {-2} {leaf {1}},
   twig {0} {leaf {1}},
   twig {-3} {leaf {0, 2}},
   twig {1} {leaf {1}, leaf {0, 2}},
   twig {3} {leaf {1}, leaf {0, 2}}},
  branch (some (-3)) {twig {3} {leaf {0, 2}}, twig {0} {leaf {-1, 3}}, twig {1} {leaf {0, 2}, leaf {-1, 3}}},
  branch (some (-2)) {twig {-1} {leaf {1}},
   twig {3} {leaf {1}},
   twig {-3} {leaf {-1, 3}},
   twig {0} {leaf {1}, leaf {-1, 3}},
   twig {1} {leaf {1}, leaf {-1, 3}}},
  branch (some 0) {twig {-1} {leaf {1}},
   twig {3} {leaf {1}, leaf {0, 2}},
   twig {-3} {leaf {0, 2}, leaf {-1, 3}},
   twig {1} {leaf {1}, leaf {0, 2}, leaf {-1, 3}}},
  branch (some 1) {twig {-2} {leaf {1}}, twig {-1} {leaf {1}}, twig {3} {leaf {1}, leaf {0, 2}}, twig {-3} {leaf {0, 2}, leaf {-1, 3}}},
  branch (some 3) {twig {-2} {leaf {1}},
   twig {-1} {leaf {1}},
   twig {-3} {leaf {0, 2}, leaf {-1, 3}},
   twig {0} {leaf {1}, leaf {-1, 3}},
   twig {1} {leaf {1}, leaf {0, 2}, leaf {-1, 3}}}},
 trunk (some 3) {branch (some (-3)) {twig {-2} {leaf {1, 2}}, twig {0} {leaf {1, 2}}, twig {1} {leaf {1, 2}}},
  branch (some (-2)) {twig {0} {leaf {1, 2}}, twig {-1} {leaf {0, 3}}, twig {1} {leaf {1, 2}, leaf {0, 3}}, twig {2} {leaf {0, 3}}},
  branch (some (-1)) {twig {0} {leaf {1, 2}},
   twig {-2} {leaf {1, 2}, leaf {0, 3}},
   twig {1} {leaf {1, 2}, leaf {0, 3}},
   twig {2} {leaf {0, 3}}},
  branch (some 0) {twig {-2} {leaf {1, 2}, leaf {0, 3}},
   twig {-1} {leaf {0, 3}},
   twig {1} {leaf {1, 2}, leaf {0, 3}},
   twig {2} {leaf {0, 3}}},
  branch (some 1) {twig {0} {leaf {1, 2}}, twig {-2} {leaf {1, 2}, leaf {0, 3}}, twig {2} {leaf {0, 3}}},
  branch (some 2) {twig {0} {leaf {1, 2}}, twig {-2} {leaf {1, 2}, leaf {0, 3}}, twig {-1} {leaf {0, 3}}}}}
  -- nearestNeighbor
  | nearestNeighbor => root {trunk (some (-14)) {branch (some (-9)) {twig {1} {leaf {-7}}, twig {6} {leaf {-7}}, twig {11} {leaf {-7}, leaf {-12, -2}}},
  branch (some (-4)) {twig {1} {leaf {-7}}, twig {-9} {leaf {-7}, leaf {-12, -2}}, twig {11} {leaf {-7}, leaf {-12, -2}}},
  branch (some 1) {twig {-4} {leaf {-7}},
   twig {6} {leaf {-7}},
   twig {-9} {leaf {-7}, leaf {-12, -2}},
   twig {11} {leaf {-7}, leaf {-12, -2}}},
  branch (some 6) {twig {-4} {leaf {-7}},
   twig {1} {leaf {-7}},
   twig {-9} {leaf {-7}, leaf {-12, -2}},
   twig {11} {leaf {-7}, leaf {-12, -2}}},
  branch (some 11) {twig {-4} {leaf {-7}}, twig {1} {leaf {-7}}, twig {6} {leaf {-7}}, twig {-9} {leaf {-7}, leaf {-12, -2}}}},
 trunk (some (-4)) {branch (some (-14)) {twig {-9} {leaf {-2}}, twig {11} {leaf {-2}}},
  branch (some (-9)) {twig {11} {leaf {-2}}},
  branch (some 1) {twig {-14} {leaf {-2}}, twig {-9} {leaf {-2}}, twig {11} {leaf {-2}}},
  branch (some 11) {twig {-14} {leaf {-2}}, twig {-9} {leaf {-2}}}},
 trunk (some 1) {branch (some (-14)) {twig {11} {leaf {-7, 8}}},
  branch (some (-4)) {twig {11} {leaf {-7, 8}}},
  branch (some (-9)) {twig {-4} {leaf {-12, 13}}},
  branch (some 6) {twig {-9} {leaf {-12, 13}}, twig {-4} {leaf {-12, 13}}}},
 trunk (some 6) {branch (some 1) {twig {-14} {leaf {3}}, twig {11} {leaf {3}}},
  branch (some (-14)) {twig {1} {leaf {3}},
   twig {-9} {leaf {-7, 13}},
   twig {-4} {leaf {3}, leaf {-7, 13}},
   twig {11} {leaf {3}, leaf {-7, 13}}},
  branch (some (-9)) {twig {-4} {leaf {-7, 13}}, twig {11} {leaf {-7, 13}}},
  branch (some (-4)) {twig {1} {leaf {3}}, twig {-9} {leaf {-7, 13}}, twig {11} {leaf {3}, leaf {-7, 13}}},
  branch (some 11) {twig {-14} {leaf {3}}, twig {1} {leaf {3}}, twig {-9} {leaf {-7, 13}}, twig {-4} {leaf {3}, leaf {-7, 13}}}},
 trunk (some 11) {branch (some (-9)) {twig {1} {leaf {3, 8}}},
  branch (some (-4)) {twig {1} {leaf {3, 8}}, twig {-14} {leaf {-2, 13}}},
  branch (some 1) {twig {-14} {leaf {-2, 13}}},
  branch (some 6) {twig {-14} {leaf {-2, 13}}}}}
  | nextToNearestNeighbor => root {trunk (some (-13)) {branch (some (-8)) {twig {7} {leaf {-9, -4}}},
  branch (some 2) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some 7) {twig {-3} {leaf {-9, -4}}},
  branch (some 12) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}}},
 trunk (some (-8)) {branch (some 7) {twig {-13} {leaf {-4}}, twig {-3} {leaf {-4}}},
  branch (some (-13)) {twig {-3} {leaf {-4}}, twig {7} {leaf {-4}}, twig {12} {leaf {-9, 1}}},
  branch (some (-3)) {twig {7} {leaf {-4}}, twig {-13} {leaf {-4}, leaf {-9, 1}}, twig {12} {leaf {-9, 1}}},
  branch (some 2) {twig {-3} {leaf {-4}}, twig {7} {leaf {-4}}, twig {-13} {leaf {-4}, leaf {-9, 1}}},
  branch (some 12) {twig {-13} {leaf {-9, 1}}}},
 trunk (some 2) {branch (some (-13)) {twig {-8} {leaf {1}}, twig {7} {leaf {1}}, twig {12} {leaf {1}}},
  branch (some 7) {twig {-13} {leaf {1}}, twig {-8} {leaf {1}}},
  branch (some (-8)) {twig {-13} {leaf {1}}, twig {7} {leaf {1}}, twig {-3} {leaf {-9, 11}}, twig {12} {leaf {1}, leaf {-9, 11}}},
  branch (some (-3)) {twig {12} {leaf {-9, 11}}},
  branch (some 12) {twig {-13} {leaf {1}}, twig {7} {leaf {1}}, twig {-8} {leaf {1}, leaf {-9, 11}}, twig {-3} {leaf {-9, 11}}}},
 trunk (some 7) {branch (some (-8)) {twig {-13} {leaf {-4, 11}}},
  branch (some 2) {twig {-13} {leaf {-4, 11}}},
  branch (some 12) {twig {-13} {leaf {-4, 11}}}},
 trunk (some 12) {branch (some (-13)) {twig {-8} {leaf {6}}, twig {2} {leaf {6}}, twig {7} {leaf {6}}},
  branch (some (-8)) {twig {-13} {leaf {6}}, twig {2} {leaf {6}}, twig {7} {leaf {6}, leaf {1, 11}}},
  branch (some (-3)) {twig {-13} {leaf {6}}, twig {2} {leaf {6}}, twig {-8} {leaf {6}, leaf {1, 11}}, twig {7} {leaf {6}, leaf {1, 11}}},
  branch (some 2) {twig {-13} {leaf {6}}, twig {7} {leaf {6}, leaf {1, 11}}},
  branch (some 7) {twig {-13} {leaf {6}}, twig {-8} {leaf {6}, leaf {1, 11}}}}}


lemma completionTopYukawa_complete_of_same : ∀ x ∈ (irreducibleElems .same topYukawa).map (fromChargeProfile topYukawa),
  ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions same.allowedBarFiveCharges same.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .same := by
  decide

lemma completionTopYukawa_complete_of_nearestNeighbor : ∀ x ∈ (irreducibleElems .nearestNeighbor topYukawa).map (fromChargeProfile topYukawa),
  ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nearestNeighbor.allowedBarFiveCharges nearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .nearestNeighbor := by
  decide

lemma completionTopYukawa_complete_of_nextToNearestNeighbor : ∀ x ∈ (irreducibleElems .nextToNearestNeighbor topYukawa).map (fromChargeProfile topYukawa),
  ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nextToNearestNeighbor.allowedBarFiveCharges nextToNearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .nextToNearestNeighbor := by
  decide

lemma completionTopYukawa_complete {I : CodimensionOneConfig} (x : Charges)
    (hx : x ∈ (irreducibleElems I topYukawa).map (fromChargeProfile topYukawa))
    (hPheno : ¬ x.IsPhenoConstrained) :
    ∀ y ∈ completions I.allowedBarFiveCharges I.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa I := by
  cases I
  case same => exact completionTopYukawa_complete_of_same x hx hPheno
  case nearestNeighbor => exact completionTopYukawa_complete_of_nearestNeighbor x hx hPheno
  case nextToNearestNeighbor => exact completionTopYukawa_complete_of_nextToNearestNeighbor x hx hPheno

set_option maxRecDepth 2000 in
lemma exists_subset_completionTopYukawa_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) : ∃ y ∈ completionTopYukawa I, y ⊆ x := by
  have hIrreducible :
        ∃ y ∈ (irreducibleElems I topYukawa).map (fromChargeProfile topYukawa), y ⊆ x := by
      rw [isPresent_iff_subest_isIrreducible] at htopYukawa
      obtain ⟨y, hPower, hIrre⟩ := htopYukawa
      use fromChargeProfile topYukawa y
      constructor
      · simp
        use y
        simp
        rw [← isIrreducible_iff_mem_irreducibleElems]
        · exact hIrre
        · rw [finsetOfCodimensionOneConfig]
          simp at hPower
          apply ChargeProfile.mem_ofFinset_of_subset _ _ hPower
          apply toChargeProfile_mem_ofFinset_of_mem_ofFinset topYukawa I.allowedBarFiveCharges
            I.allowedTenCharges
          exact hsub
      · simp at hPower
        have hx : fromChargeProfile topYukawa y ⊆ fromChargeProfile topYukawa (toChargeProfile topYukawa x) := by
          simpa using hPower
        apply subset_trans hx
        exact toChargeProfile_fromChargeProfile_subset
  obtain ⟨y, hyMem, hysubsetx⟩ := hIrreducible
  obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete
    I.allowedBarFiveCharges I.allowedTenCharges y x hysubsetx hsub hcomplete
  use z
  constructor
  · refine completionTopYukawa_complete y hyMem ?_ z hz1 ?_
    · by_contra hn
      have h' := isPhenoConstrained_of_subset hysubsetx hn
      simp_all
    · by_contra hn
      have h' := isPhenoConstrained_of_subset hz2 hn
      simp_all
  · simp_all


set_option maxRecDepth 2000 in
lemma completionTopYukawa_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ (completionTopYukawa I).toMultiset, x ∈ nonPhenoConstrainedCharges I := by
  decide +revert

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_mem_nonPhenoConstrainedCharges {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) :
    x ∉ nonPhenoConstrainedCharges I → ¬ (¬ IsPhenoConstrained x ∧
      IsPresent topYukawa (toChargeProfile topYukawa x)) := by
  by_cases hn : ¬ (IsPresent topYukawa (toChargeProfile topYukawa x))
  · simp [hn]
  simp only [not_and, hn, imp_false]
  simp at hn
  obtain ⟨y, y_mem, hyx⟩ := exists_subset_completionTopYukawa_of_not_isPhenoConstrained hx hn hsub hcomplete
  refine subset_insert_filter_card_zero (nonPhenoConstrainedCharges I)
    I.allowedBarFiveCharges I.allowedTenCharges (fun x => ¬x.IsPhenoConstrained)
    ?_ ?_ y ?_ x hyx hsub ?_ ?_
  · intro x y hxy
    simp
    exact fun a => isPhenoConstrained_of_subset hxy a
  · intro x
    rw [mem_iff_mem_toMultiset]
    exact fun a => isComplete_of_mem_nonPhenoConstrainedCharge I x a
  · apply completionTopYukawa_subset_nonPhenoConstrainedCharges
    rw [mem_iff_mem_toMultiset] at y_mem
    exact y_mem
  · exact nonPhenoConstrainedCharges_insertQ10_filter I
  · exact nonPhenoConstrainedCharges_insertQ5_filter I


lemma not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge {x : Charges}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    IsPresent topYukawa (toChargeProfile topYukawa x) ∧
    ¬ IsPhenoConstrained x ∧ IsComplete x ↔
    x ∈ nonPhenoConstrainedCharges I  := by
  constructor
  · intro ⟨hTop, hPheno, hComplete⟩
    by_contra hn
    apply not_isPhenoConstrained_mem_nonPhenoConstrainedCharges hPheno hsub hComplete  hn
    simp_all
  · intro h
    rw [mem_iff_mem_toMultiset] at h
    refine ⟨?_, ?_, ?_⟩
    · exact isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges I x h
    · exact not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges I x h
    · exact isComplete_of_mem_nonPhenoConstrainedCharge I x h

end Charges

end SU5U1

end FTheory
