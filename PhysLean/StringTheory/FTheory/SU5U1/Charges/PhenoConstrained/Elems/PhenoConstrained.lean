/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# Pheno constraints of nonPhenoConstrainedCharges

We prove that each charge in the trees `nonPhenoConstrainedCharges I`,
is not pheno-constrained and permits a top Yukawa.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig

/-!

### Each change is not pheno-constrained

-/

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, ¬ IsPhenoConstrained x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges same).toMultiset.filter
      fun x => IsPhenoConstrained x := by
    simp_all
  have hl : Multiset.filter (fun x => IsPhenoConstrained x)
    (nonPhenoConstrainedCharges same).toMultiset = ∅ := by decide
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, ¬ IsPhenoConstrained x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset.filter
      fun x => IsPhenoConstrained x := by
    simp_all
  have hl : Multiset.filter (fun x => IsPhenoConstrained x)
    (nonPhenoConstrainedCharges nearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset,
      ¬ IsPhenoConstrained x := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset.filter
      fun x => IsPhenoConstrained x := by
    simp_all
  have hl : Multiset.filter (fun x => IsPhenoConstrained x)
    (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, ¬ IsPhenoConstrained x :=
  match I with
  | same => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor =>
    not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

/-!

### Each change has a top Yukawa coupling

-/

set_option maxRecDepth 2500 in
lemma allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset,
      AllowsTerm x topYukawa := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges same).toMultiset.filter
      fun x => ¬ AllowsTerm x topYukawa := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ AllowsTerm x topYukawa)
    (nonPhenoConstrainedCharges same).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 2000 in
lemma allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset,
      AllowsTerm x topYukawa := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset.filter
      fun x => ¬ AllowsTerm x topYukawa := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ AllowsTerm x topYukawa)
    (nonPhenoConstrainedCharges nearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

set_option maxRecDepth 2000 in
lemma allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset,
      AllowsTerm x topYukawa := by
  intro x hx
  by_contra hnot
  have hx : x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset.filter
      fun x => ¬ AllowsTerm x topYukawa := by
    simp_all
  have hl : Multiset.filter (fun x => ¬ AllowsTerm x topYukawa)
    (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset = ∅ := by rfl
  rw [hl] at hx
  simp at hx

lemma allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset,
      AllowsTerm x topYukawa :=
  match I with
  | same => allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor =>
    allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
