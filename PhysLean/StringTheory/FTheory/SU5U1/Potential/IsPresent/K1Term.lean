/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Presence of K1 term

This module contains results related to the presence of a `K1` coupling
based on the additional `U(1)` charges carried by the `SU(5)` representations.

## Key results

- `termK1PresentSubsets`: The irreducible set of pairs of finite sets
  which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a `K1` coupling.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

open PotentialTerm CodimensionOneConfig

lemma isPresent_K1_iff_Q5_subset_card_one (Q5 Q10 : Finset ℤ) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      ∃ x ⊆ Q5, x.card ≤ 1 ∧ IsPresent K1 (x.val, Q10.val) := by
  constructor
  · intro hΛ
    simp [IsPresent, charges] at hΛ
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := hΛ
    use {q3}
    constructor
    · simpa [Finset.insert_subset_iff] using h3
    · constructor
      · exact Nat.factorial_eq_one.mp rfl
      · simp [IsPresent, charges]
        use q1, q2
  · intro ⟨x, hSubset, hCard, hΛ⟩
    simp [IsPresent, charges] at hΛ ⊢
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := hΛ
    use q1, q2, q3
    simp_all
    exact hSubset h3

lemma isPresent_K1_iff_Q10_subset_card_two (Q5 Q10 : Finset ℤ) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      ∃ x ⊆ Q10, x.card ≤ 2 ∧ IsPresent K1 (Q5.val, x.val) := by
  constructor
  · intro hΛ
    simp [IsPresent, charges] at hΛ
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := hΛ
    use {q1, q2}
    constructor
    · simpa [Finset.insert_subset_iff] using And.intro h1 h2
    · constructor
      · exact Finset.card_le_two
      · simp [IsPresent, charges]
        use q1, q2, q3
        simp_all
  · intro ⟨x, hSubset, hCard, hΛ⟩
    simp [IsPresent, charges] at hΛ ⊢
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := hΛ
    use q1, q2, q3
    simp_all
    constructor
    · exact hSubset h1
    · exact hSubset h2

/-- An executable function which gives, for a given `CodimensionOneConfig`, all finite sets
  of 5bar-charges and 10d-charges of cardiniality less then or equal to 1 and 2 respectively,
  which permit the `K1` coupling. -/
def termK1PermitExe (I : CodimensionOneConfig) : Finset (Finset ℤ × Finset ℤ) :=
  let prod1 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
  let prod2 := prod1.val.product (I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)).val
  let prod3 := (prod2.filter fun (Q5, Q10) => IsPresent K1 (Q5.val, Q10.val)).toFinset
  prod3

/-- An executable function which gives, for a given `CodimensionOneConfig`, gives
  the finite sets for which if contained in `Q5` and `Q10` permit a `K1`-coupling. -/
def termK1PermitSubsetExe (I : CodimensionOneConfig) : Finset (Finset ℤ × Finset ℤ) :=
  let X1 := termK1PermitExe I
  let X2 := X1.filter (fun x => ∀ y ∈ X1, x = y ∨ ¬ (y.1 ⊆ x.1 ∧ y.2 ⊆ x.2))
  X2

/-- For a given `CodimensionOneConfig`, `I`, the irreducible set of
  pair a sets which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a `K1` coupling.

  These subsets can be found with: e.g.
  `#eval (termK1PermitSubsetExe .nextToNearestNeighbor)`
-/
def termK1PresentSubsets : (I : CodimensionOneConfig) → Finset (Finset ℤ × Finset ℤ)
  | same => {({-3}, {-2, -1}), ({-3}, {-3, 0}), ({-2}, {-1}), ({-2}, {-2, 0}), ({-2}, {-3, 1}),
    ({-1}, {-1, 0}), ({-1}, {-2, 1}), ({-1}, {-3, 2}), ({0}, {0}), ({0}, {-1, 1}), ({0}, {-2, 2}),
    ({0}, {-3, 3}), ({1}, {0, 1}), ({1}, {-1, 2}), ({1}, {-2, 3}), ({2}, {1}), ({2}, {0, 2}),
    ({2}, {-1, 3}), ({3}, {1, 2}), ({3}, {0, 3})}
  | nearestNeighbor => {({-14}, {-7}), ({-14}, {-12, -2}),  ({-9}, {-7, -2}), ({-9}, {-12, 3}),
    ({-4}, {-2}), ({-4}, {-7, 3}), ({-4}, {-12, 8}), ({1}, {-2, 3}), ({1}, {-7, 8}),
    ({1}, {-12, 13}), ({6}, {3}), ({6}, {-2, 8}), ({6}, {-7, 13}), ({11}, {3, 8}), ({11}, {-2, 13})}
  | nextToNearestNeighbor => {({-13}, {-9, -4}), ({-8}, {-4}), ({-8}, {-9, 1}), ({-3}, {-4, 1}),
    ({-3}, {-9, 6}), ({2}, {1}), ({2}, {-4, 6}), ({2}, {-9, 11}), ({7}, {1, 6}), ({7}, {-4, 11}),
    ({12}, {6}), ({12}, {1, 11})}

lemma isPresent_K1_iff_termK1PresentSubsets_mem_of_same (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ same.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ same.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      (∃ (x : termK1PresentSubsets .same), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_K1_iff_termK1PresentSubsets_mem_of_nearestNeighbor (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nearestNeighbor.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ nearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      (∃ (x : termK1PresentSubsets .nearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_K1_iff_termK1PresentSubsets_mem_of_nextToNearestNeighbor (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ nextToNearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      (∃ (x : termK1PresentSubsets .nextToNearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_K1_iff_termK1PresentSubsets_mem_of_card (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      (∃ (x : termK1PresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  cases I
  case same =>
    exact isPresent_K1_iff_termK1PresentSubsets_mem_of_same Q5 Q10 h5 h10
  case nearestNeighbor =>
    exact isPresent_K1_iff_termK1PresentSubsets_mem_of_nearestNeighbor Q5 Q10 h5 h10
  case nextToNearestNeighbor =>
    exact isPresent_K1_iff_termK1PresentSubsets_mem_of_nextToNearestNeighbor Q5 Q10 h5 h10

/-- The term `K1` is present for `Q5` and `Q10` if and only if there is a pair of finite sets
  in `termK1PresentSubsets I` with the first a subset of `Q5` and the second a subset of `Q10`. -/
lemma isPresent_K1_iff_termK1PresentSubsets_mem (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset) (h10 : Q10 ∈ I.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ↔
      (∃ (x : termK1PresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  constructor
  · intro hPres
    rw [isPresent_K1_iff_Q5_subset_card_one] at hPres
    obtain ⟨Q5', h5sub, h5card, h5pres⟩ := hPres
    rw [isPresent_K1_iff_Q10_subset_card_two] at h5pres
    obtain ⟨Q10', h10sub, h10card, h10pres⟩ := h5pres
    rw [isPresent_K1_iff_termK1PresentSubsets_mem_of_card Q5' Q10'] at h10pres
    · obtain ⟨x, hx5, hx10⟩ := h10pres
      use x
      constructor
      · exact fun ⦃a⦄ a_1 => h5sub (hx5 a_1)
      · exact fun ⦃a⦄ a_1 => h10sub (hx10 a_1)
    · simp
      apply And.intro
      · simp at h5
        exact fun ⦃a⦄ a_1 => h5 (h5sub a_1)
      · exact h5card
    · simp
      apply And.intro
      · simp at h10
        exact fun ⦃a⦄ a_1 => h10 (h10sub a_1)
      · exact h10card
  · intro ⟨⟨x, hx⟩, hx5, hx10⟩
    simp_all
    have hx5card : x.1.card ≤ 1 := by
      clear hx5 hx10
      revert x
      match I with
      | same => decide
      | nearestNeighbor => decide
      | nextToNearestNeighbor => decide
    have hx10card : x.2.card ≤ 2 := by
      clear hx5 hx10
      revert x
      match I with
      | same => decide
      | nearestNeighbor => decide
      | nextToNearestNeighbor => decide
    rw [isPresent_K1_iff_Q5_subset_card_one]
    use x.1
    simp_all
    rw [isPresent_K1_iff_Q10_subset_card_two]
    use x.2
    simp_all
    rw [isPresent_K1_iff_termK1PresentSubsets_mem_of_card]
    use ⟨x, hx⟩
    simp_all
    exact fun ⦃a⦄ a_1 => h5 (hx5 a_1)
    simp_all
    exact fun ⦃a⦄ a_1 => h10 (hx10 a_1)

end SU5U1
end FTheory
