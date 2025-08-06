/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimallyAllowsTerm.OfFinset
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Yukawa
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfRationalSection
import Mathlib.Tactic.FinCases
/-!

# Charges which are not phenoconstrained and do not regenerate dangerous couplings with Yukawas


-/
namespace FTheory

namespace SU5U1

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig
open Tree
open PhysLean

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling. Unlike `nonPhenoConstrainedCharges`, these trees are calculated
  and therefore not good when using `decide` etc.
-/
def nonPhenoConstrainedChargesExt (I : CodimensionOneConfig) :
    Multiset (Charges ℤ) :=
  let completionTopYukawa := (((minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
      I.allowedTenCharges topYukawa).bind
    (completions I.allowedBarFiveCharges I.allowedTenCharges)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addOneTopYukawa := (((completionTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addTwoTopYukawa := (((addOneTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addThreeTopYukawa := (((addTwoTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  ((completionTopYukawa + addOneTopYukawa +
    addTwoTopYukawa + addThreeTopYukawa).filter fun x => ¬ YukawaGeneratesDangerousAtLevel x 1)

private def nonPhenoConstrainedChargesSame : Multiset (Charges ℤ) :=
   {(some (-2), some (-3), {2}, {-3, 0}), (some (-1), some (-3), {1}, {-3, 0}),
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
    (some 1, some 3, {-1}, {0, 3}), (some 2, some 3, {-2}, {0, 3}),
    (some 1, some (-3), {-1, 2}, {-3, 0}), (some 2, some (-3), {-2, 1}, {-3, 0}),
    (some (-3), some (-2), {0}, {3, -1}), (some (-3), some (-2), {0, 2}, {-1}),
    (some (-3), some (-2), {2}, {-3, -1}), (some (-1), some (-2), {0, 2}, {-1}),
    (some 0, some (-2), {-3}, {3, -1}), (some 0, some (-2), {-3, 1}, {-1}),
    (some 0, some (-2), {1}, {3, -1}), (some 1, some (-2), {0}, {3, -1}),
    (some 2, some (-2), {-3}, {-3, -1}), (some 2, some (-2), {-3, -1}, {-1}),
    (some 2, some (-2), {-3, 0}, {-1}), (some 2, some (-2), {-1, 1}, {-1}),
    (some 0, some (-2), {-1, 3}, {-3, 1}), (some (-2), some 2, {-1, 1}, {1}),
    (some (-2), some 2, {0, 3}, {1}), (some (-2), some 2, {1, 3}, {1}),
    (some (-2), some 2, {3}, {3, 1}), (some (-1), some 2, {0}, {-3, 1}),
    (some 0, some 2, {-1}, {-3, 1}), (some 0, some 2, {-1, 3}, {1}),
    (some 0, some 2, {3}, {-3, 1}), (some 1, some 2, {-2, 0}, {1}),
    (some 3, some 2, {-2}, {3, 1}), (some 3, some 2, {-2, 0}, {1}),
    (some 3, some 2, {0}, {-3, 1}), (some 0, some 2, {-3, 1}, {-1, 3}),
    (some (-2), some 3, {-1, 2}, {0, 3}), (some (-1), some 3, {-2, 1}, {0, 3}),
    (some 0, some (-2), {-3, 1}, {3, -1}), (some 0, some 2, {-1, 3}, {-3, 1})}

private def nonPhenoConstrainedChargesNN : Multiset (Charges ℤ) :=
  {(some (-9), some (-14), {-4}, {-7}), (some (-9), some (-14), {1}, {-7}),
    (some (-9), some (-14), {6}, {-7}), (some (-9), some (-14), {11}, {-7}),
    (some (-4), some (-14), {-9}, {-7}), (some (-4), some (-14), {1}, {-7}),
    (some (-4), some (-14), {6}, {-7}), (some (-4), some (-14), {11}, {-7}),
    (some 1, some (-14), {-9}, {-7}), (some 1, some (-14), {-4}, {-7}),
    (some 1, some (-14), {6}, {-7}), (some 1, some (-14), {11}, {-7}),
    (some 6, some (-14), {-9}, {-7}), (some 6, some (-14), {-4}, {-7}),
    (some 6, some (-14), {1}, {-7}),  (some 6, some (-14), {11}, {-7}),
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
    (some (-4), some 6, {11}, {-7, 13}), (some 11, some 6, {-4}, {-7, 13}),
    (some (-9), some (-14), {-4}, {13, -7}), (some (-9), some (-14), {-4, 6}, {-7}),
    (some (-4), some (-14), {-9}, {13, -7}), (some (-4), some (-14), {-9, 6}, {-7}),
    (some (-4), some (-14), {-9, 11}, {-7}), (some (-4), some (-14), {6, 11}, {-7}),
    (some (-4), some (-14), {11}, {13, -7}), (some 1, some (-14), {-4, 6}, {-7}),
    (some 6, some (-14), {-9, -4}, {-7}), (some 6, some (-14), {-4}, {-12, -7}),
    (some 6, some (-14), {-9, 1}, {-7}), (some 6, some (-14), {1, 11}, {-7}),
    (some 11, some (-14), {-9, -4}, {-7}), (some 11, some (-14), {-4}, {13, -7}),
    (some 11, some (-14), {-4, 1}, {-7}), (some 11, some (-14), {-9, 6}, {-7}),
    (some (-9), some (-4), {-14, 11}, {-2}), (some (-9), some (-4), {11}, {-12, -2}),
    (some 1, some (-4), {-14, 11}, {-2}), (some (-14), some 6, {1, 11}, {3}),
    (some 11, some 6, {-14, -4}, {3}), (some (-4), some 6, {-9, 11}, {-7, 13}),
    (some (-4), some (-14), {-9, 11}, {13, -7})}

private def nonPhenoConstrainedChargesNtoNN : Multiset (Charges ℤ) :=
  {(some (-13), some (-8), {7}, {-4}), (some (-3), some (-8), {7}, {-4}),
    (some 2, some (-8), {-13}, {-4}), (some 2, some (-8), {-3}, {-4}),
    (some 2, some (-8), {7}, {-4}), (some 7, some (-8), {-13}, {-4}),
    (some 7, some (-8), {-3}, {-4}), (some (-13), some 2, {-8}, {1}),
    (some (-13), some 2, {7}, {1}), (some (-13), some 2, {12}, {1}),
    (some (-8), some 2, {-13}, {1}), (some (-8), some 2, {7}, {1}),
    (some 7, some 2, {-13}, {1}), (some 7, some 2, {-8}, {1}),
    (some 7, some 2, {12}, {1}), (some 12, some 2, {-13}, {1}),
    (some 12, some 2, {7}, {1}), (some (-8), some 2, {-3}, {-9, 11}),
    (some (-3), some 2, {-8}, {-9, 11}), (some (-3), some 2, {12}, {-9, 11}),
    (some 12, some 2, {-3}, {-9, 11}), (some (-13), some 12, {-8}, {6}),
    (some (-13), some 12, {2}, {6}), (some (-13), some 12, {7}, {6}),
    (some (-8), some 12, {-13}, {6}), (some (-8), some 12, {2}, {6}),
    (some (-8), some 12, {7}, {6}), (some (-3), some 12, {-13}, {6}),
    (some (-3), some 12, {-8}, {6}), (some (-3), some 12, {2}, {6}),
    (some (-3), some 12, {7}, {6}), (some 2, some 12, {-13}, {6}),
    (some 2, some 12, {-8}, {6}), (some 2, some 12, {7}, {6}),
    (some 7, some 12, {-13}, {6}), (some 7, some 12, {-8}, {6}),
    (some 7, some 12, {2}, {6}), (some (-13), some 2, {-8, 12}, {1}),
    (some (-8), some 2, {-13, 7}, {1}), (some 7, some 2, {-8, 12}, {1}),
    (some 12, some 2, {-13, 7}, {1}), (some (-3), some 2, {-8, 12}, {-9, 11}),
    (some (-13), some 12, {-8}, {-9, 6}), (some (-13), some 12, {-8, 7}, {6}),
    (some (-13), some 12, {7}, {-4, 6}), (some (-8), some 12, {-13}, {-9, 6}),
    (some (-8), some 12, {-13, 2}, {6}), (some (-8), some 12, {2, 7}, {6}),
    (some 2, some 12, {-13, -8}, {6}), (some 2, some 12, {-8, 7}, {6}),
    (some 7, some 12, {-13, 2}, {6})}

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling.

  These trees can be found with e.g.
  `#eval nonPhenoConstrainedChargesExt nextToNearestNeighbor`. -/
def nonPhenoConstrainedCharges : (I : CodimensionOneConfig) →  Multiset (Charges ℤ)
  | same => nonPhenoConstrainedChargesSame
  | nearestNeighbor => nonPhenoConstrainedChargesNN
  | nextToNearestNeighbor => nonPhenoConstrainedChargesNtoNN

/-!

## Basic properties

-/

lemma nonPhenoConstrainedCharges_card (I : CodimensionOneConfig) :
    (nonPhenoConstrainedCharges I).card =
    if I = .same then 102 else
    if I = .nearestNeighbor then 71 else 51  := by
  decide +revert

lemma isComplete_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), IsComplete x := by
 revert I
 decide

lemma allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), x.AllowsTerm topYukawa := by
  revert I
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), ¬ IsPhenoConstrained x := by
  revert I
  decide

set_option maxRecDepth 2000 in
lemma not_yukawaGeneratesDangerousAtLevel_one_of_mem_nonPhenoConstrainedCharges
    (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  revert I
  decide

lemma card_five_bar_le_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), x.2.2.1.card ≤ 2 := by
  revert I
  decide

lemma card_ten_le_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I), x.2.2.2.card ≤ 2 := by
  revert I
  decide

/-!

## Pheno insert
-/
set_option maxRecDepth 2000 in
lemma phenoInsert_Q5_same  :
    ∀ q5 ∈ same.allowedBarFiveCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges same),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges same
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma phenoInsert_Q5_nn  :
    ∀ q5 ∈ nearestNeighbor.allowedBarFiveCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges nearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma phenoInsert_Q5_nnTon  :
    ∀ q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges nextToNearestNeighbor
    ∨ YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

lemma phenoInsert_Q5 (I : CodimensionOneConfig) :
    ∀ q5 ∈ I.allowedBarFiveCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges I),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges I
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  fin_cases I
  · exact phenoInsert_Q5_same
  · exact phenoInsert_Q5_nn
  · exact phenoInsert_Q5_nnTon


set_option maxRecDepth 2000 in
lemma phenoInsert_Q10_same  :
    ∀ q10 ∈ same.allowedTenCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges same),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges same
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma phenoInsert_Q10_nn  :
    ∀ q10 ∈ nearestNeighbor.allowedTenCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges nearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  repeat decide

set_option maxRecDepth 2000 in
lemma phenoInsert_Q10_nnTon  :
    ∀ q10 ∈ nextToNearestNeighbor.allowedTenCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges nextToNearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  repeat decide

lemma phenoInsert_Q10 (I : CodimensionOneConfig) :
    ∀ q10 ∈ I.allowedTenCharges,
    ∀ x ∈ (nonPhenoConstrainedCharges I),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ nonPhenoConstrainedCharges I
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  fin_cases I
  · exact phenoInsert_Q10_same
  · exact phenoInsert_Q10_nn
  · exact phenoInsert_Q10_nnTon

end Charges

end SU5U1

end FTheory
