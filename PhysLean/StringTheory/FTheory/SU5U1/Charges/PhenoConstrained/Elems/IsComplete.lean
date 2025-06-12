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

namespace Charges

open CodimensionOneConfig
open Tree

set_option maxRecDepth 2400 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, IsComplete x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges same).toMultiset.filter fun x => ¬ IsComplete x := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ IsComplete x)
    (nonPhenoConstrainedCharges same).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 900 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, IsComplete x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset.filter
      fun x => ¬ IsComplete x := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ IsComplete x)
    (nonPhenoConstrainedCharges nearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 1000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, IsComplete x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset.filter
      fun x => ¬ IsComplete x := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ IsComplete x)
    (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

lemma isComplete_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, IsComplete x :=
  match I with
  | same => isComplete_of_mem_nonPhenoConstrainedCharge_same
  | nearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor
  | nextToNearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
