/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# PhenoInsert of nonPhenoConstrainedCharges

We prove show that the phenoInsertQ10
of `nonPhenoConstrainedCharges I` is empty. This result is used
in the completeness proof.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

/-!

### phenoInsertQ10 on nonPhenoConstrainedCharges is empty

This result is used to help show completeness.

-/

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_same : ∀ q10 ∈ same.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges same) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nearestNeighbor :
    ∀ q10 ∈ nearestNeighbor.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges nearestNeighbor) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nextToNearestNeighbor :
    ∀ q10 ∈ nextToNearestNeighbor.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges nextToNearestNeighbor) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero (I : CodimensionOneConfig) :
    ∀ q10 ∈ I.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges I) q10).card = 0 :=
  match I with
  | same => nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_same
  | nearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nearestNeighbor
  | nextToNearestNeighbor =>
    nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
