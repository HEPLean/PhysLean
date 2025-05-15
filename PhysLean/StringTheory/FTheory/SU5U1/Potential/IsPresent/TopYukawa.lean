/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Presence of Top Yukawa coupling

This module contains results related to the presence of a top Yukawa coupling
based on the additional `U(1)` charges carried by the `SU(5)` representations.

## Key results

- `topYukawaPresentSubsets`: For a given `qHu` charge, this gives the finite sets which
  permit a top Yukawa coupling. Thus if one of these sets is a subset of `Q10`, then a top Yukawa
  coupling is present.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

open PotentialTerm CodimensionOneConfig

lemma isPresent_topYukawa_iff_subset_card_two (qHu : ℤ) (Q10 : Finset ℤ) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      ∃ x ⊆ Q10, x.card ≤ 2 ∧ IsPresent topYukawa (qHu, x.val) := by
  constructor
  · intro hTop
    simp [IsPresent, charges] at hTop
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := hTop
    use {q1, q2}
    constructor
    · simpa [Finset.insert_subset_iff] using And.intro h1 h2
    · constructor
      · exact Finset.card_le_two
      · simp [IsPresent, charges]
        use q1, q2
        simp_all
  · intro ⟨x, hSubset, hCard, hTop⟩
    simp [IsPresent, charges] at hTop ⊢
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := hTop
    use q1, q2
    simp_all
    constructor
    · exact hSubset h1
    · exact hSubset h2

/-- For a `CodimensionOneConfig`, `I`, and a `qHu` charge, the executable
  definition giving the allowed finite sets of ten-dimensional charges which permit a
  top Yukawa quark, with the assumption of less then or equal to `3` Ten-dimensional quarks.
-/
def topYukawaHiggsMapExe (I : CodimensionOneConfig) (qHu : ℤ) : Finset (Finset ℤ) :=
  let prod1 := I.allowedBarFiveCharges.val
  let prod2 := prod1.product (I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)).val
  let prod3 := (prod2.filter fun (qHu, Q10) => IsPresent topYukawa (qHu, Q10.val)).toFinset
  (((prod3).filter (fun x => x.1 = qHu)).val.map (fun x => x.2)).toFinset

/-- For a given `CodimensionOneConfig`, `I`, and a valid `qHu`,
  the irreducible set of finite sets for which if they are a subset of
  `Q10`, then a top Yukawa coupling is present. -/
def topYukawaPresentSubsets : (I : CodimensionOneConfig) → (qHu : ℤ) → Finset (Finset ℤ)
  | same, -3 => {{-2, -1}, {-3, 0}}
  | same, -2 => {{-1}, {-2, 0}, {-3, 1}}
  | same, -1 => {{-1, 0}, {-2, 1}, {-3, 2}}
  | same, 0 => {{0}, {-1, 1}, {-2, 2}, {-3, 3}}
  | same, 1 => {{0, 1}, {-1, 2}, {-2, 3}}
  | same, 2 => {{1}, {0, 2}, {-1, 3}}
  | same, 3 => {{1, 2}, {0, 3}}
  | same, _ => ∅
  | nearestNeighbor, -14 => {{-7}, {-12, -2}}
  | nearestNeighbor, -9 => {{-7, -2}, {-12, 3}}
  | nearestNeighbor, -4 => {{-2}, {-7, 3}, {-12, 8}}
  | nearestNeighbor, 1 => {{-2, 3}, {-7, 8}, {-12, 13}}
  | nearestNeighbor, 6 => {{3}, {-2, 8}, {-7, 13}}
  | nearestNeighbor, 11 => {{3, 8}, {-2, 13}}
  | nearestNeighbor, _ => ∅
  | nextToNearestNeighbor, -13 =>{{-9, -4}}
  | nextToNearestNeighbor, -8 =>  {{-4}, {-9, 1}}
  | nextToNearestNeighbor, -3 => {{-4, 1}, {-9, 6}}
  | nextToNearestNeighbor, 2 => {{1}, {-4, 6}, {-9, 11}}
  | nextToNearestNeighbor, 7 => {{1, 6}, {-4, 11}}
  | nextToNearestNeighbor, 12 => {{6}, {1, 11}}
  | nextToNearestNeighbor, _ => ∅

lemma isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_same (Q10 : Finset ℤ) (qHu : ℤ)
    (hmem : Q10 ∈ same.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2))
    (hqHu : qHu ∈ same.allowedBarFiveCharges) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      (∃ (x : topYukawaPresentSubsets .same qHu), x.1 ⊆ Q10) := by
  rw [isPresent_topYukawa_iff_Q10_product_Q10]
  simp only
  revert Q10
  revert qHu
  decide

lemma isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_nearestNeighbor (Q10 : Finset ℤ) (qHu : ℤ)
    (hmem : Q10 ∈ nearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2))
    (hqHu : qHu ∈ nearestNeighbor.allowedBarFiveCharges) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      (∃ (x : topYukawaPresentSubsets .nearestNeighbor qHu), x.1 ⊆ Q10) := by
  rw [isPresent_topYukawa_iff_Q10_product_Q10]
  simp only
  revert Q10
  revert qHu
  decide

lemma isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_nextToNearestNeighbor
    (Q10 : Finset ℤ) (qHu : ℤ)
    (hmem : Q10 ∈ nextToNearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2))
    (hqHu : qHu ∈ nextToNearestNeighbor.allowedBarFiveCharges) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      (∃ (x : topYukawaPresentSubsets .nextToNearestNeighbor qHu), x.1 ⊆ Q10) := by
  rw [isPresent_topYukawa_iff_Q10_product_Q10]
  simp only
  revert Q10
  revert qHu
  decide

lemma isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_card_two (I : CodimensionOneConfig)
    (Q10 : Finset ℤ) (qHu : ℤ)
    (hmem : Q10 ∈ I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2))
    (hqHu : qHu ∈ I.allowedBarFiveCharges) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      (∃ (x : topYukawaPresentSubsets I qHu), x.1 ⊆ Q10) := by
  cases I
  case same =>
    exact isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_same Q10 qHu hmem hqHu
  case nearestNeighbor =>
    exact isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_nearestNeighbor Q10 qHu hmem hqHu
  case nextToNearestNeighbor =>
    exact isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_of_nextToNearestNeighbor
      Q10 qHu hmem hqHu

lemma isPresent_topYukawa_iff_topYukawaPresentSubsets_mem (I : CodimensionOneConfig)
    (Q10 : Finset ℤ) (qHu : ℤ)
    (hmem : Q10 ∈ I.allowedTenCharges.powerset)
    (hqHu : qHu ∈ I.allowedBarFiveCharges) :
    IsPresent topYukawa (qHu, Q10.val) ↔
      (∃ (x : topYukawaPresentSubsets I qHu), x.1 ⊆ Q10) := by
  constructor
  · intro hTop
    rw [isPresent_topYukawa_iff_subset_card_two] at hTop
    obtain ⟨x, hSubset, hCard, hTop'⟩ := hTop
    rw [isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_card_two (I := I) x qHu _ hqHu] at hTop'
    · obtain ⟨x', hSub⟩ := hTop'
      use x'
      exact fun ⦃a⦄ a_1 => hSubset (hSub a_1)
    · simp
      apply And.intro
      · simp at hmem
        exact fun ⦃a⦄ a_1 => hmem (hSubset a_1)
      · exact hCard
  · intro ⟨x, hSubset⟩
    rw [isPresent_topYukawa_iff_subset_card_two ]
    use x
    have hxcard : x.1.card ≤ 2 := by
      clear hSubset
      revert x
      revert qHu
      match I with
      | same => decide
      | nearestNeighbor => decide
      | nextToNearestNeighbor => decide
    simp_all
    rw [isPresent_topYukawa_iff_topYukawaPresentSubsets_mem_card_two (I := I) x qHu _ hqHu]
    · exact Exists.intro x fun ⦃a⦄ a => a
    · simp
      apply And.intro
      · exact fun ⦃a⦄ a_1 => hmem (hSubset a_1)
      · exact hxcard

end SU5U1
end FTheory
