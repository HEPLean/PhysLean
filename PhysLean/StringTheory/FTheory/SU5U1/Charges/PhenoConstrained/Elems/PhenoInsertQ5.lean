/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# PhenoInsert of nonPhenoConstrainedCharges

We prove show that the phenoInsertQ5
of `nonPhenoConstrainedCharges I` is empty. This result is used
in the completeness proof.

-/
namespace FTheory

namespace SU5U1

namespace Charges
open SuperSymmetry.SU5
open PotentialTerm
open CodimensionOneConfig
open PhysLean Tree

/-!

### phenoInsertQ5 on nonPhenoConstrainedCharges is empty

This result is used to help show completeness.

-/

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same_of_neg :
    ∀ q5 ∈ same.allowedBarFiveCharges,
    q5 < 0 → (phenoInsertQ5 (nonPhenoConstrainedCharges same) q5).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same_of_pos :
    ∀ q5 ∈ same.allowedBarFiveCharges,
    0 ≤ q5 → (phenoInsertQ5 (nonPhenoConstrainedCharges same) q5).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same :
    ∀ q5 ∈ same.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges same) q5).card = 0 := by
  intro q5 hq5
  by_cases hq5_neg : q5 < 0
  · exact nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same_of_neg q5 hq5 hq5_neg
  · simp at hq5_neg
    exact nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same_of_pos q5 hq5 hq5_neg

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nearestNeighbor :
    ∀ q5 ∈ nearestNeighbor.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges nearestNeighbor) q5).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nextToNearestNeighbor :
    ∀ q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges nextToNearestNeighbor) (q5)).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero (I : CodimensionOneConfig) :
    ∀ q5 ∈ I.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges I) q5).card = 0 :=
  match I with
  | same => nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same
  | nearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nearestNeighbor
  | nextToNearestNeighbor =>
    nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
