/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.IsViable.Elems
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges

open PhysLean  Tree
-- #eval Tree.fromMultiset (filterAnomalyCancellation .nextToNearestNeighbor (nonPhenoConstrainedCharges .nextToNearestNeighbor)).toMultiset


def elemsAnomalyFree : (I :CodimensionOneConfig) →  FourTree  (Option ℤ)  (Option ℤ) (Finset ℤ) (Finset ℤ)
 | .same => root {trunk (some (-3)) {branch (some 0) {twig {-2, -1} {leaf {0}, leaf {-3, 0}}},
      branch (some 1) {twig {-2, 0} {leaf {-2, 3}}, twig {-2, 0, 3} {leaf {-2, 3}}}},
    trunk (some 2) {branch (some (-2)) {twig {-3, -1} {leaf {-3, -1}}, twig {-1, 1} {leaf {-1}, leaf {-3, -1}}, twig {-3, -1, 1} {leaf {-1}, leaf {-3, -1}}},
      branch (some (-1)) {twig {0, 1} {leaf {-3, 2}}},
      branch (some 0) {twig {1, 3} {leaf {2, 0}}},
      branch (some 1) {twig {3} {leaf {0, 1}}}},
    trunk (some (-2)) {branch (some (-1)) {twig {-3} {leaf {-1, 0}}},
      branch (some 0) {twig {-3, -1} {leaf {-2, 0}}},
      branch (some 1) {twig {-1, 0} {leaf {-2, 3}}},
      branch (some 2) {twig {-1, 1} {leaf {1}, leaf {3, 1}}, twig {1, 3} {leaf {3, 1}}, twig {-1, 1, 3} {leaf {1}, leaf {3, 1}}}},
    trunk (some (-1)) {branch (some 0) {twig {-3, -2, -1} {leaf {0}}},
      branch (some 2) {twig {0, 1} {leaf {1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}}}},
    trunk (some 1) {branch (some (-2)) {twig {-1, 0} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, -1}}},
      branch (some 0) {twig {1, 2, 3} {leaf {0}}}},
    trunk (some 3) {branch (some 0) {twig {1, 2} {leaf {0}, leaf {3, 0}}},
      branch (some (-1)) {twig {0, 2} {leaf {-3, 2}}, twig {-3, 0, 2} {leaf {-3, 2}}}}}
  | .nearestNeighbor => root {trunk (some (-9)) {branch (some (-14)) {twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}},
    trunk (some 1) {branch (some (-14)) {twig {-9, -4} {leaf {-7}, leaf {-12, -7}}}},
    trunk (some 6) {branch (some (-14)) {twig {-9, 1} {leaf {-7}, leaf {-12, -7}}, twig {-9, 1, 11} {leaf {-7}}, twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}}}
  | .nextToNearestNeighbor => root {trunk (some (-3)) {branch (some 12) {twig {2, 7} {leaf {6}, leaf {11, 6}}}}}
/- set_option maxRecDepth 2000
example : ∀ x ∈ (filterAnomalyCancellation .same (nonPhenoConstrainedCharges .same)).toMultiset,
    x ∈ testTree := by
  decide-/
open Quanta
open FourTree
set_option maxRecDepth 2000
lemma filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_same :
    (filterAnomalyCancellation .same (nonPhenoConstrainedCharges .same)).toMultiset ⊆
    (elemsAnomalyFree .same).toMultiset := by
  intros x hx
  rw [← mem_iff_mem_toMultiset]
  revert x
  decide

set_option maxRecDepth 2000
lemma filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_NN :
    (filterAnomalyCancellation .nearestNeighbor
      (nonPhenoConstrainedCharges .nearestNeighbor)).toMultiset ⊆
    (elemsAnomalyFree .nearestNeighbor).toMultiset := by
  intros x hx
  rw [← mem_iff_mem_toMultiset]
  revert x
  decide

set_option maxRecDepth 2000
lemma filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_NTNN :
    (filterAnomalyCancellation .nextToNearestNeighbor
      (nonPhenoConstrainedCharges .nextToNearestNeighbor)).toMultiset ⊆
    (elemsAnomalyFree .nextToNearestNeighbor).toMultiset := by
  intros x hx
  rw [← mem_iff_mem_toMultiset]
  revert x
  decide

lemma filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree :
    (filterAnomalyCancellation I (nonPhenoConstrainedCharges I)).toMultiset ⊆
    (elemsAnomalyFree I).toMultiset :=
  match I with
  | .same =>
    filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_same
  | .nearestNeighbor =>
    filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_NN
  | .nextToNearestNeighbor =>
    filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree_of_NTNN

lemma toCharges_mem_elemsAnomalyFree_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ elemsAnomalyFree I := by
  rw [mem_iff_mem_toMultiset]
  apply filterAnomalyCancellation_nonPhenoConstrainedCharges_subset_elemsAnomalyFree
  rw [← mem_iff_mem_toMultiset]
  exact toCharges_mem_nonPhenoConstrainedCharges_filterAnomalyCancellation_of_isViable I x h

end Charges

namespace Quanta
open Charges

/-!

## Lifting to Quanta

-/

open PhysLean FourTree

set_option maxRecDepth 2000 in
lemma  mem_viableElems_of_ofCharges_elemsAnomalyFree_of_same :
    ∀ x ∈ (elemsAnomalyFree .same).toMultiset, ∀ y ∈ Quanta.ofCharges .same x,
      AnomalyCancellation y.1 y.2.1 y.2.2.1 y.2.2.2 → y ∈ viableElems .same := by
  decide

set_option maxRecDepth 2000 in
lemma  mem_viableElems_of_ofCharges_elemsAnomalyFree_of_NN :
    ∀ x ∈ (elemsAnomalyFree .nearestNeighbor).toMultiset, ∀ y ∈ Quanta.ofCharges .nearestNeighbor x,
      AnomalyCancellation y.1 y.2.1 y.2.2.1 y.2.2.2 → y ∈ viableElems .nearestNeighbor := by
  decide

set_option maxRecDepth 2000 in
lemma mem_viableElems_of_ofCharges_elemsAnomalyFree_of_NTNN :
    ∀ x ∈ (elemsAnomalyFree .nextToNearestNeighbor).toMultiset,
    ∀ y ∈ Quanta.ofCharges .nextToNearestNeighbor x,
      AnomalyCancellation y.1 y.2.1 y.2.2.1 y.2.2.2 → y ∈ viableElems .nextToNearestNeighbor := by
  decide

lemma mem_viableElems_of_ofCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (elemsAnomalyFree I).toMultiset,
    ∀ y ∈ Quanta.ofCharges I x, AnomalyCancellation y.1 y.2.1 y.2.2.1 y.2.2.2 →
    y ∈ viableElems I :=
  match I with
  | .same => mem_viableElems_of_ofCharges_elemsAnomalyFree_of_same
  | .nearestNeighbor => mem_viableElems_of_ofCharges_elemsAnomalyFree_of_NN
  | .nextToNearestNeighbor => mem_viableElems_of_ofCharges_elemsAnomalyFree_of_NTNN

lemma mem_viableElems_of_isViable
    (I : CodimensionOneConfig) (𝓠 : Quanta) (h : IsViable I 𝓠) :
    𝓠 ∈ viableElems I := by
  apply mem_viableElems_of_ofCharges I 𝓠.toCharges
  · rw [← mem_iff_mem_toMultiset]
    exact toCharges_mem_elemsAnomalyFree_of_isViable I 𝓠 h
  · exact mem_ofCharges_self_of_isViable I 𝓠 h
  · exact anomalyCancellation_of_isViable I 𝓠 h

lemma isViable_iff_mem_viableElems (I : CodimensionOneConfig) (𝓠 : Quanta) :
    IsViable I 𝓠 ↔ 𝓠 ∈ viableElems I := by
  constructor
  · intro h
    exact mem_viableElems_of_isViable I 𝓠 h
  · intro h
    exact isViable_of_mem_viableElems I 𝓠 h

end Quanta
end SU5U1

end FTheory
