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

set_option profiler true
set_option maxRecDepth 2000
/- lemma nonPhenoConstrainedCharges_complete_ten' :
    ∀ x ∈ (insertQ10 (nonPhenoConstrainedCharges same) (-3)).toMultiset,
      IsPhenoConstrained x := by
  decide -/

lemma test :  ∀ q10 ∈ same.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges same) q10).card = 0 := by
  decide

lemma test' : ∀ q5 ∈ same.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges same) (q5)).card = 0 := by
  decide


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
def completionTopYukawaSame : Tree := root {trunk (some (-3)) {branch (some 3) {twig {-1} {leaf {-2, -1}}, twig {0} {leaf {-2, -1}}, twig {2} {leaf {-2, -1}}},
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

set_option maxRecDepth 2000 in
lemma completionTopYukawaSame_qHd_isSome : ∀ x ∈ completionTopYukawaSame.toMultiset, x.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma completionTopYukawaSame_qHu_isSome : ∀ x ∈ completionTopYukawaSame.toMultiset, x.2.1.isSome := by
  decide

lemma completionTopYukawaSame_card : completionTopYukawaSame.card = 164 := by
  simp only [completionTopYukawaSame, Int.reduceNeg, Multiset.insert_eq_cons]
  rfl

lemma completionTopYukawaSame_complete : ∀ x ∈ (irreducibleElems .same topYukawa).map (fromChargeProfile topYukawa),
  ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions same.allowedBarFiveCharges same.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawaSame := by
  decide

set_option maxRecDepth 2000 in
lemma exists_subset_completionTopYukawaSame_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) : ∃ y ∈ completionTopYukawaSame, y ⊆ x := by
  have hIrreducible :
        ∃ y ∈ (irreducibleElems .same topYukawa).map (fromChargeProfile topYukawa), y ⊆ x := by
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
          apply toChargeProfile_mem_ofFinset_of_mem_ofFinset topYukawa same.allowedBarFiveCharges
            same.allowedTenCharges
          exact hsub
      · simp at hPower
        have hx : fromChargeProfile topYukawa y ⊆ fromChargeProfile topYukawa (toChargeProfile topYukawa x) := by
          simpa using hPower
        apply subset_trans hx
        exact toChargeProfile_fromChargeProfile_subset
  obtain ⟨y, hyMem, hysubsetx⟩ := hIrreducible
  obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete
    same.allowedBarFiveCharges same.allowedTenCharges y x hysubsetx hsub hcomplete
  use z
  constructor
  · refine completionTopYukawaSame_complete y hyMem ?_ z hz1 ?_
    · by_contra hn
      have h' := isPhenoConstrained_of_subset hysubsetx hn
      simp_all
    · by_contra hn
      have h' := isPhenoConstrained_of_subset hz2 hn
      simp_all
  · simp_all


/-!

## The tree of charges `addOneTopYukawaSame`
-/

/--
All `minimalSuperSet` of elements `completionTopYukawaSame` which are not pheno-constrained.

This can be constructed via

Tree.fromMultiset (((completionTopYukawaSame.toMultiset).bind (fun x =>
    (minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
-/
def addOneTopYukawaSame : Tree := root {trunk (some (-3)) {branch (some 3) {twig {-1} {leaf {-3, -2, -1}},
   twig {-1, 0} {leaf {-2, -1}},
   twig {0} {leaf {-3, -2, -1}},
   twig {2} {leaf {-3, -2, -1}}},
  branch (some (-2)) {twig {0} {leaf {-3, -2, -1}}, twig {2} {leaf {-3, -2, -1}}},
  branch (some (-1)) {twig {0} {leaf {-3, -2, -1}}, twig {2} {leaf {-3, -2, -1}}},
  branch (some 0) {twig {-2, -1} {leaf {-3, 0}},
   twig {-1} {leaf {-3, -2, -1}, leaf {-2, -3, 0}},
   twig {-2, 1} {leaf {-3, 0}},
   twig {2} {leaf {-3, -2, -1}},
   twig {-1, 2} {leaf {-3, 0}}},
  branch (some 1) {twig {0} {leaf {-3, -2, -1}},
   twig {0, -1} {leaf {-2, -1}},
   twig {-2, -1} {leaf {-3, 0}},
   twig {-1} {leaf {-3, -2, -1}, leaf {-2, -3, 0}},
   twig {2} {leaf {-3, -2, -1}},
   twig {-1, 2} {leaf {-3, 0}}},
  branch (some 2) {twig {0} {leaf {-3, -2, -1}},
   twig {0, -1} {leaf {-2, -1}},
   twig {-2, -1} {leaf {-3, 0}},
   twig {-1} {leaf {-3, -2, -1}, leaf {-2, -3, 0}},
   twig {-2, 1} {leaf {-3, 0}}}},
 trunk (some (-2)) {branch (some 1) {twig {0} {leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1}},
   twig {0, 2} {leaf {-1}},
   twig {2} {leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}},
   twig {0, -3} {leaf {-1}},
   twig {2, -3} {leaf {-1}},
   twig {-3} {leaf {-3, -1}, leaf {0, -1}, leaf {3, -1}},
   twig {0, -1} {leaf {-1}},
   twig {-3, -1} {leaf {-1}, leaf {-2, 0}},
   twig {-1} {leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, 0}}},
  branch (some (-3)) {twig {1} {leaf {-3, -1}, leaf {3, -1}},
   twig {1, 2} {leaf {-1}},
   twig {2} {leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}},
   twig {1, -1} {leaf {-1}},
   twig {-1} {leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, 0}},
   twig {-1, 0} {leaf {-1}},
   twig {2, 0} {leaf {-1}},
   twig {0} {leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1}},
   twig {-1, 3} {leaf {-3, 1}}},
  branch (some (-1)) {twig {1} {leaf {-3, -1}},
   twig {1, 2} {leaf {-1}},
   twig {2} {leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}},
   twig {1, -3} {leaf {-1}},
   twig {2, -3} {leaf {-1}},
   twig {-3} {leaf {-3, -1}, leaf {0, -1}}},
  branch (some 0) {twig {1} {leaf {-3, -1}, leaf {3, -1}},
   twig {1, -3} {leaf {-1}},
   twig {-3} {leaf {-3, -1}, leaf {0, -1}, leaf {3, -1}},
   twig {1, -1} {leaf {-1}},
   twig {-3, -1} {leaf {-1}, leaf {-2, 0}},
   twig {-1} {leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, 0}},
   twig {-1, 3} {leaf {-3, 1}}},
  branch (some 2) {twig {-3} {leaf {-3, -1}, leaf {3, -1}},
   twig {-3, 1} {leaf {-1}},
   twig {1} {leaf {-3, -1}, leaf {3, -1}},
   twig {-3, -1} {leaf {-1}},
   twig {1, -1} {leaf {-1}},
   twig {-1} {leaf {-3, -1}, leaf {-2, -1}},
   twig {-3, 0} {leaf {-1}},
   twig {-1, 0} {leaf {-1}},
   twig {0} {leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1}},
   twig {-1, 3} {leaf {-3, 1}}}, branch (some 3) {twig {-3, -1} {leaf {-2, 0}}, twig {-1} {leaf {-3, -2, 0}}}},
 trunk (some 0) {branch (some (-2)) {twig {-1} {leaf {-2, -3, 3}}, twig {-1, 1} {leaf {-3, 3}}, twig {-1, 2} {leaf {-3, 3}}},
  branch (some (-1)) {twig {-3} {leaf {-3, -2, 2}},
   twig {-3, 3} {leaf {-2, 2}},
   twig {3} {leaf {3, -2, 2}},
   twig {1} {leaf {2, -3, 3}},
   twig {2} {leaf {2, -3, 3}}},
  branch (some 1) {twig {-3} {leaf {-3, -2, 2}},
   twig {-3, 3} {leaf {-2, 2}},
   twig {3} {leaf {3, -2, 2}},
   twig {-2} {leaf {-2, -3, 3}},
   twig {-1} {leaf {-2, -3, 3}}},
  branch (some 2) {twig {-2, 1} {leaf {-3, 3}}, twig {-1, 1} {leaf {-3, 3}}, twig {1} {leaf {2, -3, 3}}}},
 trunk (some 2) {branch (some (-1)) {twig {-2} {leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {-2, 0} {leaf {1}},
   twig {0} {leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {0, 1} {leaf {1}},
   twig {1} {leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2}},
   twig {-2, 3} {leaf {1}},
   twig {0, 3} {leaf {1}},
   twig {3} {leaf {-3, 1}, leaf {0, 1}, leaf {3, 1}},
   twig {1, 3} {leaf {1}, leaf {0, 2}}},
  branch (some (-3)) {twig {3, 1} {leaf {0, 2}}, twig {1} {leaf {3, 0, 2}}},
  branch (some (-2)) {twig {-1} {leaf {-3, 1}, leaf {3, 1}},
   twig {-1, 3} {leaf {1}},
   twig {3} {leaf {-3, 1}, leaf {3, 1}},
   twig {3, 0} {leaf {1}},
   twig {0} {leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {-1, 1} {leaf {1}},
   twig {0, 1} {leaf {1}},
   twig {3, 1} {leaf {1}},
   twig {1} {leaf {2, 1}, leaf {3, 1}},
   twig {-3, 1} {leaf {-1, 3}}},
  branch (some 0) {twig {-1} {leaf {-3, 1}, leaf {3, 1}},
   twig {-1, 3} {leaf {1}},
   twig {3} {leaf {-3, 1}, leaf {0, 1}, leaf {3, 1}},
   twig {-1, 1} {leaf {1}},
   twig {3, 1} {leaf {1}, leaf {0, 2}},
   twig {1} {leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2}},
   twig {-3, 1} {leaf {-1, 3}}},
  branch (some 1) {twig {-2} {leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {-2, -1} {leaf {1}},
   twig {-1} {leaf {3, 1}},
   twig {-2, 3} {leaf {1}},
   twig {-1, 3} {leaf {1}},
   twig {3} {leaf {0, 1}, leaf {3, 1}}},
  branch (some 3) {twig {-2} {leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {-2, -1} {leaf {1}},
   twig {-1} {leaf {-3, 1}, leaf {3, 1}},
   twig {-2, 0} {leaf {1}},
   twig {0} {leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}},
   twig {-1, 1} {leaf {1}},
   twig {0, 1} {leaf {1}},
   twig {1} {leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2}},
   twig {-3, 1} {leaf {-1, 3}}}},
 trunk (some 3) {branch (some (-3)) {twig {-2} {leaf {3, 1, 2}}, twig {0} {leaf {3, 1, 2}}, twig {0, 1} {leaf {1, 2}}, twig {1} {leaf {3, 1, 2}}},
  branch (some (-2)) {twig {0} {leaf {3, 1, 2}},
   twig {0, 1} {leaf {1, 2}},
   twig {1} {leaf {3, 1, 2}, leaf {2, 0, 3}},
   twig {-1, 2} {leaf {0, 3}},
   twig {1, 2} {leaf {0, 3}}},
  branch (some (-1)) {twig {0} {leaf {3, 1, 2}},
   twig {-2} {leaf {3, 1, 2}},
   twig {0, 1} {leaf {1, 2}},
   twig {-2, 1} {leaf {0, 3}},
   twig {1} {leaf {3, 1, 2}, leaf {2, 0, 3}},
   twig {1, 2} {leaf {0, 3}}},
  branch (some 0) {twig {-2} {leaf {3, 1, 2}},
   twig {-2, 1} {leaf {0, 3}},
   twig {1} {leaf {3, 1, 2}, leaf {2, 0, 3}},
   twig {-1, 2} {leaf {0, 3}},
   twig {1, 2} {leaf {0, 3}}},
  branch (some 1) {twig {0} {leaf {3, 1, 2}}, twig {-2} {leaf {3, 1, 2}}},
  branch (some 2) {twig {0} {leaf {3, 1, 2}}, twig {-2} {leaf {3, 1, 2}}}}}


lemma addOneTopYukawaSame_card : addOneTopYukawaSame.card = 216 := by
  simp [addOneTopYukawaSame]
  rfl

set_option maxRecDepth 2000 in
lemma addOneTopYukawaSame_qHd_isSome : ∀ x ∈ addOneTopYukawaSame.toMultiset, x.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma addOneTopYukawaSame_qHu_isSome : ∀ x ∈ addOneTopYukawaSame.toMultiset, x.2.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_addOneTopYukawaSame_mem :
    ∀ x ∈ addOneTopYukawaSame.toMultiset, ¬ x.IsPhenoConstrained := by
  decide

set_option maxRecDepth 2000 in
lemma addOneTopYukawaSame_complete_ten :
  ∀ x ∈ completionTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedTenCharges,
      ¬ y ∈ x.2.2.2 →
     ¬ IsPhenoConstrained (x.1, x.2.1, x.2.2.1, insert y x.2.2.2)
    →  addOneTopYukawaSame.mem ((x.1, x.2.1, x.2.2.1, insert y x.2.2.2) : Charges)  := by
  decide

set_option maxRecDepth 2000 in
lemma addOneTopYukawaSame_complete_five :
  ∀ x ∈ completionTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedBarFiveCharges,
      ¬ y ∈ x.2.2.1 → ¬ IsPhenoConstrained (x.1, x.2.1, insert y  x.2.2.1, x.2.2.2)
    → addOneTopYukawaSame.mem ((x.1, x.2.1, insert y  x.2.2.1, x.2.2.2) : Charges)  := by
  decide

lemma addOneTopYukawaSame_complete :
  ∀ x ∈ completionTopYukawaSame.toMultiset,
  ∀ y ∈ minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x,
    ¬ IsPhenoConstrained y → addOneTopYukawaSame.mem y := by
  intro x hx y hy hp
  simp [minimalSuperSet] at hy
  have h1 := completionTopYukawaSame_qHd_isSome x hx
  have h2 := completionTopYukawaSame_qHu_isSome x hx
  simp_all
  have hy2 := hy.2
  rcases hy2 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · apply addOneTopYukawaSame_complete_five x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h
  · apply addOneTopYukawaSame_complete_ten x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h

set_option maxRecDepth 2000 in
lemma exists_subset_addOneTopYukawaSame_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) : x ∈ completionTopYukawaSame ∨
    ∃ y ∈ addOneTopYukawaSame, y ⊆ x := by
  obtain ⟨y, hyMem, hysubsetx⟩ := exists_subset_completionTopYukawaSame_of_not_isPhenoConstrained
    hx htopYukawa hsub hcomplete
  by_cases hyx : y = x
  · subst hyx
    left
    exact hyMem
  right
  obtain ⟨z, hz1, hz2⟩ := exists_minimalSuperSet
    same.allowedBarFiveCharges same.allowedTenCharges hsub hysubsetx hyx
  use z
  constructor
  · apply addOneTopYukawaSame_complete y ((mem_iff_mem_toMultiset completionTopYukawaSame y).mp hyMem) _ hz1
    by_contra hn
    have h' := isPhenoConstrained_of_subset hz2 hn
    simp_all
  · exact hz2

/-!

## The tree of charges `addTwoTopYukawaSame`

-/

/--
All `minimalSuperSet` of elements `addOneTopYukawaSame` which are not pheno-constrained.

This can be constructed via

Tree.fromMultiset (((addOneTopYukawaSame.toMultiset).bind (fun x =>
    (minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
-/
def addTwoTopYukawaSame : Tree := root {trunk (some (-3)) {branch (some 3) {twig {-1, 0} {leaf {-3, -2, -1}}},
  branch (some 1) {twig {0, -1} {leaf {-3, -2, -1}}},
  branch (some 2) {twig {0, -1} {leaf {-3, -2, -1}}}},
 trunk (some (-2)) {branch (some 1) {twig {0} {leaf {-3, -2, -1}},
   twig {0, 2} {leaf {-3, -1}},
   twig {2} {leaf {-3, -2, -1}},
   twig {0, 2, -3} {leaf {-1}},
   twig {0, -3} {leaf {-3, -1}},
   twig {2, -3} {leaf {-3, -1}},
   twig {0, -3, -1} {leaf {-1}},
   twig {-3, -1} {leaf {-3, -1}},
   twig {0, -1} {leaf {-3, -1}, leaf {-2, -1}},
   twig {-1} {leaf {-3, -2, -1}}},
  branch (some (-3)) {twig {2} {leaf {-3, -2, -1}},
   twig {1, -1} {leaf {-3, -1}},
   twig {-1} {leaf {-3, -2, -1}},
   twig {2, 0} {leaf {-3, -1}},
   twig {-1, 0} {leaf {-3, -1}, leaf {-2, -1}},
   twig {0} {leaf {-3, -2, -1}}},
  branch (some (-1)) {twig {2} {leaf {-3, -2, -1}}, twig {1, 2, -3} {leaf {-1}}, twig {1, -3} {leaf {-3, -1}}, twig {2, -3} {leaf {-3, -1}}},
  branch (some 0) {twig {1, -3} {leaf {-3, -1}, leaf {3, -1}},
   twig {1, -3, -1} {leaf {-1}},
   twig {-3, -1} {leaf {-3, -1}},
   twig {1, -1} {leaf {-3, -1}},
   twig {-1} {leaf {-3, -2, -1}}},
  branch (some 2) {twig {-3, 1} {leaf {-3, -1}, leaf {3, -1}},
   twig {-3, 1, -1} {leaf {-1}},
   twig {-3, -1} {leaf {-3, -1}},
   twig {1, -1} {leaf {-3, -1}},
   twig {-1} {leaf {-3, -2, -1}},
   twig {-3, -1, 0} {leaf {-1}},
   twig {-3, 0} {leaf {-3, -1}},
   twig {-1, 0} {leaf {-3, -1}, leaf {-2, -1}},
   twig {0} {leaf {-3, -2, -1}}}},
 trunk (some 2) {branch (some (-1)) {twig {-2} {leaf {2, 3, 1}},
   twig {-2, 0} {leaf {3, 1}},
   twig {0} {leaf {2, 3, 1}},
   twig {0, 1} {leaf {2, 1}, leaf {3, 1}},
   twig {1} {leaf {2, 3, 1}},
   twig {-2, 0, 3} {leaf {1}},
   twig {-2, 3} {leaf {3, 1}},
   twig {0, 3} {leaf {3, 1}},
   twig {0, 1, 3} {leaf {1}},
   twig {1, 3} {leaf {3, 1}}},
  branch (some (-2)) {twig {-1, 3} {leaf {-3, 1}, leaf {3, 1}},
   twig {3, 0} {leaf {3, 1}},
   twig {0} {leaf {2, 3, 1}},
   twig {-1, 3, 1} {leaf {1}},
   twig {0, 3, 1} {leaf {1}},
   twig {-1, 1} {leaf {3, 1}},
   twig {0, 1} {leaf {2, 1}, leaf {3, 1}},
   twig {3, 1} {leaf {3, 1}},
   twig {1} {leaf {2, 3, 1}}},
  branch (some 0) {twig {-1, 3} {leaf {-3, 1}, leaf {3, 1}},
   twig {-1, 3, 1} {leaf {1}},
   twig {-1, 1} {leaf {3, 1}},
   twig {3, 1} {leaf {3, 1}},
   twig {1} {leaf {2, 3, 1}}},
  branch (some 1) {twig {-2} {leaf {2, 3, 1}}, twig {-2, -1, 3} {leaf {1}}, twig {-2, 3} {leaf {3, 1}}, twig {-1, 3} {leaf {3, 1}}},
  branch (some 3) {twig {-2} {leaf {2, 3, 1}},
   twig {-2, 0} {leaf {3, 1}},
   twig {0} {leaf {2, 3, 1}},
   twig {-1, 1} {leaf {3, 1}},
   twig {0, 1} {leaf {2, 1}, leaf {3, 1}},
   twig {1} {leaf {2, 3, 1}}}},
 trunk (some 3) {branch (some (-3)) {twig {0, 1} {leaf {3, 1, 2}}},
  branch (some (-2)) {twig {0, 1} {leaf {3, 1, 2}}},
  branch (some (-1)) {twig {0, 1} {leaf {3, 1, 2}}}}}

set_option maxRecDepth 2000 in
lemma addTwoTopYukawaSame_qHd_isSome : ∀ x ∈ addTwoTopYukawaSame.toMultiset, x.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma addTwoTopYukawaSame_qHu_isSome : ∀ x ∈ addTwoTopYukawaSame.toMultiset, x.2.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma addTwoTopYukawaSame_complete_ten :
  ∀ x ∈ addOneTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedTenCharges,
      ¬ y ∈ x.2.2.2 →
     ¬ IsPhenoConstrained (x.1, x.2.1, x.2.2.1, insert y x.2.2.2)
    →  addTwoTopYukawaSame.mem ((x.1, x.2.1, x.2.2.1, insert y x.2.2.2) : Charges)  := by
  decide

set_option maxRecDepth 2000 in
lemma addTwoTopYukawaSame_complete_five :
  ∀ x ∈ addOneTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedBarFiveCharges,
      ¬ y ∈ x.2.2.1 →
     ¬ IsPhenoConstrained (x.1, x.2.1, insert y  x.2.2.1, x.2.2.2)
    →  addTwoTopYukawaSame.mem ((x.1, x.2.1, insert y  x.2.2.1, x.2.2.2) : Charges)  := by
  decide

lemma addTwoTopYukawaSame_complete :
  ∀ x ∈ addOneTopYukawaSame.toMultiset,
  ∀ y ∈ minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x,
    ¬ IsPhenoConstrained y → addTwoTopYukawaSame.mem y := by
  intro x hx y hy hp
  simp [minimalSuperSet] at hy
  have h1 := addOneTopYukawaSame_qHd_isSome x hx
  have h2 := addOneTopYukawaSame_qHu_isSome x hx
  simp_all
  have hy2 := hy.2
  rcases hy2 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · apply addTwoTopYukawaSame_complete_five x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h
  · apply addTwoTopYukawaSame_complete_ten x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h

set_option maxRecDepth 2000 in
lemma exists_subset_addTwoTopYukawaSame_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) : x ∈ completionTopYukawaSame ∨
    x ∈ addOneTopYukawaSame ∨ ∃ y ∈ addTwoTopYukawaSame, y ⊆ x := by
  have hr := exists_subset_addOneTopYukawaSame_of_not_isPhenoConstrained
    hx htopYukawa hsub hcomplete
  rcases hr with hr | hr
  · simp_all
  right
  obtain ⟨y, hyMem, hysubsetx⟩ := hr
  by_cases hyx : y = x
  · subst hyx
    left
    exact hyMem
  right
  obtain ⟨z, hz1, hz2⟩ := exists_minimalSuperSet
    same.allowedBarFiveCharges same.allowedTenCharges hsub hysubsetx hyx
  use z
  constructor
  · apply addTwoTopYukawaSame_complete y ((mem_iff_mem_toMultiset _ y).mp hyMem) _ hz1
    by_contra hn
    have h' := isPhenoConstrained_of_subset hz2 hn
    simp_all
  · exact hz2

/-!

## The tree of charges `addThreeTopYukawaSame`

-/

/--
All `minimalSuperSet` of elements `addTwoTopYukawaSame` which are not pheno-constrained.

This can be constructed via

Tree.fromMultiset (((addTwoTopYukawaSame.toMultiset).bind (fun x =>
    (minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
-/
def addThreeTopYukawaSame : Tree := root {trunk (some (-2)) {branch (some 1) {twig {0, 2, -3} {leaf {-3, -1}}, twig {-3, 0, -1} {leaf {-3, -1}}, twig {0, -1} {leaf {-3, -2, -1}}},
  branch (some (-3)) {twig {-1, 0} {leaf {-3, -2, -1}}},
  branch (some 0) {twig {-3, 1, -1} {leaf {-3, -1}}},
  branch (some 2) {twig {-3, 1, -1} {leaf {-3, -1}}, twig {-3, -1, 0} {leaf {-3, -1}}, twig {-1, 0} {leaf {-3, -2, -1}}}},
 trunk (some 2) {branch (some (-1)) {twig {0, 1} {leaf {2, 3, 1}}, twig {-2, 0, 3} {leaf {3, 1}}, twig {0, 1, 3} {leaf {3, 1}}},
  branch (some (-2)) {twig {-1, 3, 1} {leaf {3, 1}}, twig {0, 3, 1} {leaf {3, 1}}, twig {0, 1} {leaf {2, 3, 1}}},
  branch (some 0) {twig {-1, 3, 1} {leaf {3, 1}}},
  branch (some 3) {twig {0, 1} {leaf {2, 3, 1}}}}}

set_option maxRecDepth 2000 in
lemma addThreeTopYukawaSame_qHd_isSome : ∀ x ∈ addThreeTopYukawaSame.toMultiset, x.1.isSome := by
  decide

set_option maxRecDepth 2000 in
lemma addThreeTopYukawaSame_qHu_isSome : ∀ x ∈ addThreeTopYukawaSame.toMultiset, x.2.1.isSome := by
  decide

lemma addThreeTopYukawaSame_card : addThreeTopYukawaSame.card = 16 := by
  simp [addThreeTopYukawaSame]
  rfl

set_option maxRecDepth 2000 in
lemma addThreeTopYukawaSame_complete_ten :
  ∀ x ∈ addTwoTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedTenCharges,
      ¬ y ∈ x.2.2.2 →
     ¬ IsPhenoConstrained (x.1, x.2.1, x.2.2.1, insert y x.2.2.2)
    →  addThreeTopYukawaSame.mem ((x.1, x.2.1, x.2.2.1, insert y x.2.2.2) : Charges)  := by
  decide

set_option maxRecDepth 2000 in
lemma addThreeTopYukawaSame_complete_five :
  ∀ x ∈ addTwoTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedBarFiveCharges,
      ¬ y ∈ x.2.2.1 →
     ¬ IsPhenoConstrained (x.1, x.2.1, insert y  x.2.2.1, x.2.2.2)
    →  addThreeTopYukawaSame.mem ((x.1, x.2.1, insert y  x.2.2.1, x.2.2.2) : Charges)  := by
  decide

lemma addThreeTopYukawaSame_complete :
  ∀ x ∈ addTwoTopYukawaSame.toMultiset,
  ∀ y ∈ minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x,
    ¬ IsPhenoConstrained y → addThreeTopYukawaSame.mem y := by
  intro x hx y hy hp
  simp [minimalSuperSet] at hy
  have h1 := addTwoTopYukawaSame_qHd_isSome x hx
  have h2 := addTwoTopYukawaSame_qHu_isSome x hx
  simp_all
  have hy2 := hy.2
  rcases hy2 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · apply addThreeTopYukawaSame_complete_five x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h
  · apply addThreeTopYukawaSame_complete_ten x hx a ha _ hp
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h

set_option maxRecDepth 2000 in
lemma exists_subset_addThreeTopYukawaSame_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) : x ∈ completionTopYukawaSame ∨
    x ∈ addOneTopYukawaSame ∨ x ∈ addTwoTopYukawaSame ∨
    ∃ y ∈ addThreeTopYukawaSame, y ⊆ x := by
  have hr := exists_subset_addTwoTopYukawaSame_of_not_isPhenoConstrained
    hx htopYukawa hsub hcomplete
  rcases hr with hr | hr | hr
  · simp_all
  right
  · simp_all
  right
  right
  obtain ⟨y, hyMem, hysubsetx⟩ := hr
  by_cases hyx : y = x
  · subst hyx
    left
    exact hyMem
  right
  obtain ⟨z, hz1, hz2⟩ := exists_minimalSuperSet
    same.allowedBarFiveCharges same.allowedTenCharges hsub hysubsetx hyx
  use z
  constructor
  · apply addThreeTopYukawaSame_complete y ((mem_iff_mem_toMultiset _ y).mp hyMem) _ hz1
    by_contra hn
    have h' := isPhenoConstrained_of_subset hz2 hn
    simp_all
  · exact hz2


set_option maxRecDepth 2000 in
lemma false_of_addThreeTopYukawaSame_add_ten :
  ∀ x ∈ addThreeTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedTenCharges,
      ¬ y ∈ x.2.2.2 →
     ¬ IsPhenoConstrained (x.1, x.2.1, x.2.2.1, insert y x.2.2.2)
    →  False  := by
  decide

set_option maxRecDepth 2000 in
lemma false_of_addThreeTopYukawaSame_add_five :
  ∀ x ∈ addThreeTopYukawaSame.toMultiset,
    ∀ y ∈ same.allowedBarFiveCharges,
      ¬ y ∈ x.2.2.1 →
     ¬ IsPhenoConstrained (x.1, x.2.1, insert y  x.2.2.1, x.2.2.2)
    →  False := by
  decide

lemma false_of_addThreeTopYukawaSame_minimalSuperSet :
  ∀ x ∈ addThreeTopYukawaSame.toMultiset,
  ∀ y ∈ minimalSuperSet same.allowedBarFiveCharges same.allowedTenCharges x,
    ¬ IsPhenoConstrained y → False := by
  intro x hx y hy hp
  simp [minimalSuperSet] at hy
  have h1 := addThreeTopYukawaSame_qHd_isSome x hx
  have h2 := addThreeTopYukawaSame_qHu_isSome x hx
  simp_all
  have hy2 := hy.2
  rcases hy2 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · refine False.elim (false_of_addThreeTopYukawaSame_add_five x hx a ha ?_ hp)
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h
  · refine False.elim (false_of_addThreeTopYukawaSame_add_ten x hx a ha ?_ hp)
    by_contra h
    apply hy.1
    rw [Finset.insert_eq_of_mem]
    · rfl
    · exact h

set_option maxRecDepth 2000 in
lemma completeness_of_completionTopYukawaSame_addTopYukawaSame {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) : x ∈ completionTopYukawaSame ∨
    x ∈ addOneTopYukawaSame ∨ x ∈ addTwoTopYukawaSame ∨ x ∈ addThreeTopYukawaSame := by
  have hr := exists_subset_addThreeTopYukawaSame_of_not_isPhenoConstrained
    hx htopYukawa hsub hcomplete
  rcases hr with hr | hr | hr | hr
  · simp_all
  · simp_all
  · simp_all
  right
  right
  right
  obtain ⟨y, hyMem, hysubsetx⟩ := hr
  by_cases hyx : y = x
  · subst hyx
    exact hyMem
  obtain ⟨z, hz1, hz2⟩ := exists_minimalSuperSet
    same.allowedBarFiveCharges same.allowedTenCharges hsub hysubsetx hyx
  apply False.elim
  apply false_of_addThreeTopYukawaSame_minimalSuperSet y ((mem_iff_mem_toMultiset _ y).mp hyMem) _ hz1
  by_contra hn
  have h' := isPhenoConstrained_of_subset hz2 hn
  simp_all

/-!

## Completeness

-/

set_option maxRecDepth 2000 in
lemma completionTopYukawaSame_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ completionTopYukawaSame.toMultiset, x ∈ nonPhenoConstrainedCharges .same := by
  decide

set_option maxRecDepth 2000 in
lemma addOneTopYukawaSame_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ addOneTopYukawaSame.toMultiset, x ∈ nonPhenoConstrainedCharges .same := by
  decide

set_option maxRecDepth 2000 in
lemma addTwoTopYukawaSame_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ addTwoTopYukawaSame.toMultiset, x ∈ nonPhenoConstrainedCharges .same := by
  decide

set_option maxRecDepth 2000 in
lemma addThreeTopYukawaSame_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ addThreeTopYukawaSame.toMultiset, x ∈ nonPhenoConstrainedCharges .same := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_mem_nonPhenoConstrainedCharges_of_same {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : IsPresent topYukawa (toChargeProfile topYukawa x))
    (hsub : x ∈ ofFinset same.allowedBarFiveCharges same.allowedTenCharges)
    (hcomplete : IsComplete x) :
    x ∈ nonPhenoConstrainedCharges .same:= by
  have h1 :=  completeness_of_completionTopYukawaSame_addTopYukawaSame
    hx htopYukawa hsub hcomplete
  rcases h1 with hr | hr | hr | hr
  · exact completionTopYukawaSame_subset_nonPhenoConstrainedCharges x
      ((mem_iff_mem_toMultiset completionTopYukawaSame x).mp hr)
  · exact addOneTopYukawaSame_subset_nonPhenoConstrainedCharges x
      ((mem_iff_mem_toMultiset addOneTopYukawaSame x).mp hr)
  · exact addTwoTopYukawaSame_subset_nonPhenoConstrainedCharges x
      ((mem_iff_mem_toMultiset addTwoTopYukawaSame x).mp hr)
  · exact addThreeTopYukawaSame_subset_nonPhenoConstrainedCharges x
      ((mem_iff_mem_toMultiset addThreeTopYukawaSame x).mp hr)

set_option maxRecDepth 4000 in
lemma nonPhenoConstrainedCharges_complete_ten :
  ∀ x ∈ (nonPhenoConstrainedCharges .same).toMultiset,
      ¬ (-3) ∈ x.2.2.2 →
      ¬ (nonPhenoConstrainedCharges .same).mem ((x.1, x.2.1, x.2.2.1, insert (-3) x.2.2.2) : Charges)
     → IsPhenoConstrained (x.1, x.2.1, x.2.2.1, insert (-3) x.2.2.2)
    := by
  decide


end Charges

end SU5U1

end FTheory
