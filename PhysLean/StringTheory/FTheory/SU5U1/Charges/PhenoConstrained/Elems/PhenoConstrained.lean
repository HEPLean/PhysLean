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
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

/-!

### Each change is not pheno-constrained

-/

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, ¬ x.IsPhenoConstrained := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, ¬ x.IsPhenoConstrained := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset,
      ¬ x.IsPhenoConstrained := by
  decide

lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, ¬ x.IsPhenoConstrained :=
  match I with
  | same => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor =>
    not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

/-!

### Each change has a top Yukawa coupling

-/

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) :=
  match I with
  | same => isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor =>
    isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
