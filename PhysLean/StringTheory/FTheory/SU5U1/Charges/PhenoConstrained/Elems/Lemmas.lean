/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# Other lemmas related to nonPhenoConstrainedCharges

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

set_option maxRecDepth 5000 in
lemma card_Q5_le_three_of_nonPhenoConstrainedCharges_of_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, x.2.2.1.card ≤ 4 := by
  decide

set_option maxRecDepth 2000 in
lemma card_Q5_le_three_of_nonPhenoConstrainedCharges_of_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, x.2.2.1.card ≤ 4 := by
  decide

set_option maxRecDepth 2000 in
lemma card_Q5_le_three_of_nonPhenoConstrainedCharges_of_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, x.2.2.1.card ≤ 4 := by
  decide

lemma card_Q5_le_three_of_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
     ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, x.2.2.1.card ≤ 4 :=
  match I with
  | same => card_Q5_le_three_of_nonPhenoConstrainedCharges_of_same
  | nearestNeighbor => card_Q5_le_three_of_nonPhenoConstrainedCharges_of_nearestNeighbor
  | nextToNearestNeighbor =>
    card_Q5_le_three_of_nonPhenoConstrainedCharges_of_nextToNearestNeighbor


set_option maxRecDepth 5000 in
lemma card_Q10_le_three_of_nonPhenoConstrainedCharges_of_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, x.2.2.2.card ≤ 3 := by
  decide

set_option maxRecDepth 2000 in
lemma card_Q10_le_three_of_nonPhenoConstrainedCharges_of_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, x.2.2.2.card ≤ 3 := by
  decide

set_option maxRecDepth 2000 in
lemma card_Q10_le_three_of_nonPhenoConstrainedCharges_of_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, x.2.2.2.card ≤ 3 := by
  decide

lemma card_Q10_le_three_of_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
     ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, x.2.2.2.card ≤ 3 :=
  match I with
  | same => card_Q10_le_three_of_nonPhenoConstrainedCharges_of_same
  | nearestNeighbor => card_Q10_le_three_of_nonPhenoConstrainedCharges_of_nearestNeighbor
  | nextToNearestNeighbor =>
    card_Q10_le_three_of_nonPhenoConstrainedCharges_of_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
