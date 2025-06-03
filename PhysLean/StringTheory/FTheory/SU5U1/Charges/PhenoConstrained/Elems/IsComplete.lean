/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# IsComplete of nonPhenoConstrainedCharges

We prove that each charge in the trees `nonPhenoConstrainedCharges I`,
is complete.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, x.IsComplete := by
  decide

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, x.IsComplete := by
  decide

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, x.IsComplete := by
  decide

lemma isComplete_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, x.IsComplete :=
  match I with
  | same => isComplete_of_mem_nonPhenoConstrainedCharge_same
  | nearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor
  | nextToNearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
