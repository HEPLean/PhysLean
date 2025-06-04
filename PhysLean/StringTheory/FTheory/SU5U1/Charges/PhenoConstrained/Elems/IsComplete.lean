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

set_option maxRecDepth 2400 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, x.IsComplete := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges same).toMultiset.filter fun x => ¬ x.IsComplete:= by
    simp_all
  have hl : Multiset.filter (fun x => ¬ x.IsComplete)
    (nonPhenoConstrainedCharges same).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 900 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, x.IsComplete := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset.filter
      fun x => ¬ x.IsComplete:= by
    simp_all
  have hl : Multiset.filter (fun x => ¬ x.IsComplete)
    (nonPhenoConstrainedCharges nearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 1000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, x.IsComplete := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset.filter
      fun x => ¬ x.IsComplete:= by
    simp_all
  have hl : Multiset.filter (fun x => ¬ x.IsComplete)
    (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

lemma isComplete_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, x.IsComplete :=
  match I with
  | same => isComplete_of_mem_nonPhenoConstrainedCharge_same
  | nearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor
  | nextToNearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
