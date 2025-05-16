/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Presence of W1 term

This module contains results related to the presence of a `W1` coupling
based on the additional `U(1)` charges carried by the `SU(5)` representations.

## Key results

- `termW1PresentSubsets`: The irreducible set of pairs of finite sets
  which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a `W1` coupling.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

open PotentialTerm CodimensionOneConfig

lemma isPresent_W1_of_Q10_subset {Q5 Q10' Q10 : Finset ℤ} (h : Q10' ⊆ Q10)
    (hPres : IsPresent W1 (Q5.val, Q10'.val)) : IsPresent W1 (Q5.val, Q10.val) := by
  simp [IsPresent, charges] at hPres ⊢
  obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hPres
  use q1, q2, q3, q4
  simp_all
  exact ⟨h h1, h h2, h h3⟩

lemma isPresent_W1_of_Q5_subset {Q5' Q5 Q10 : Finset ℤ} (h : Q5' ⊆ Q5)
    (hPres : IsPresent W1 (Q5'.val, Q10.val)) : IsPresent W1 (Q5.val, Q10.val) := by
  simp [IsPresent, charges] at hPres ⊢
  obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hPres
  use q1, q2, q3, q4
  simp_all
  exact h h4

lemma isPresent_W1_iff_Q5_subset_card_one (Q5 Q10 : Finset ℤ) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      ∃ x ⊆ Q5, x.card ≤ 1 ∧ IsPresent W1 (x.val, Q10.val) := by
  constructor
  · intro hΛ
    simp [IsPresent, charges] at hΛ
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hΛ
    use {q4}
    constructor
    · simpa [Finset.insert_subset_iff] using h4
    · constructor
      · exact Nat.factorial_eq_one.mp rfl
      · simp [IsPresent, charges]
        use q1, q2, q3
  · intro ⟨x, hSubset, hCard, hΛ⟩
    simp [IsPresent, charges] at hΛ ⊢
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hΛ
    use q1, q2, q3, q4
    simp_all
    exact hSubset h4

lemma isPresent_W1_iff_Q10_subset_card_three (Q5 Q10 : Finset ℤ) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      ∃ x ⊆ Q10, x.card ≤ 3 ∧ IsPresent W1 (Q5.val, x.val) := by
  constructor
  · intro hΛ
    simp [IsPresent, charges] at hΛ
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hΛ
    use {q1, q2, q3}
    constructor
    · simpa [Finset.insert_subset_iff] using ⟨h1, h2, h3⟩
    · constructor
      · exact Finset.card_le_three
      · simp [IsPresent, charges]
        use q1, q2, q3, q4
        simp_all
  · intro ⟨x, hSubset, hCard, hΛ⟩
    simp [IsPresent, charges] at hΛ ⊢
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := hΛ
    use q1, q2, q3, q4
    simp_all
    exact ⟨hSubset h1, hSubset h2, hSubset h3⟩


/-- An executable function which gives, for a given `CodimensionOneConfig`, all finite sets
  of 5bar-charges and 10d-charges of cardiniality less then or equal to 1 and 2 respectively,
  which permit the `W1` coupling. -/
def termW1PermitExe (I : CodimensionOneConfig) : Finset (Finset ℤ × Finset ℤ) :=
  let prod1 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
  let prod2 := prod1.val.product (I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)).val
  let prod3 := (prod2.filter fun (Q5, Q10) => IsPresent W1 (Q5.val, Q10.val)).toFinset
  prod3

/-- An executable function which gives, for a given `CodimensionOneConfig`, gives
  the finite sets for which if contained in `Q5` and `Q10` permit a `W1`-coupling. -/
def termW1PermitSubsetExe (I : CodimensionOneConfig) : Finset (Finset ℤ × Finset ℤ) :=
  let X1 := termW1PermitExe I
  let X2 := X1.filter (fun x => ∀ y ∈ X1, x = y ∨ ¬ (y.1 ⊆ x.1 ∧ y.2 ⊆ x.2))
  X2

-- #eval (termW1PermitSubsetExe .nextToNearestNeighbor)
/-- For a given `CodimensionOneConfig`, `I`, the irreducible set of
  pair a sets which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a `W1` coupling.

  These subsets can be found with: e.g.
  `#eval (termW1PermitSubsetExe .nextToNearestNeighbor)`
-/
def termW1PresentSubsets : (I : CodimensionOneConfig) → Finset (Finset ℤ × Finset ℤ)
  | same => {({-3}, {1}), ({-3}, {-1, 2}), ({-3}, {-3, 3}), ({-3}, {0, 3}), ({-3}, {-2, 2, 3}),
    ({-2}, {0, 1}), ({-2}, {-2, 2}), ({-2}, {0, 2}), ({-2}, {-1, 1, 2}), ({-2}, {-1, 0, 3}),
    ({-2}, {-2, 1, 3}), ({-2}, {-3, 2, 3}), ({-1}, {-1, 1}), ({-1}, {0, 1}), ({-1}, {-3, 2}),
    ({-1}, {-1, 0, 2}), ({-1}, {-2, 1, 2}), ({-1}, {-1, 3}), ({-1}, {-2, 0, 3}), ({-1}, {-3, 1, 3}),
    ({0}, {0}), ({0}, {-2, 1}), ({0}, {-1, 2}), ({0}, {-3, 1, 2}), ({0}, {-2, -1, 3}),
    ({1}, {-1, 0}), ({1}, {-3, 1}), ({1}, {-1, 1}), ({1}, {-2, 0, 1}), ({1}, {-2, -1, 2}),
    ({1}, {-3, 0, 2}), ({1}, {-2, 3}), ({1}, {-3, -1, 3}), ({2}, {-2, 0}), ({2}, {-1, 0}),
    ({2}, {-2, -1, 1}), ({2}, {-3, 0, 1}), ({2}, {-2, 2}), ({2}, {-3, -1, 2}), ({2}, {-3, -2, 3}),
    ({3}, {-1}), ({3}, {-3, 0}), ({3}, {-2, 1}), ({3}, {-3, -2, 2}), ({3}, {-3, 3})}
  | nearestNeighbor => {({-14}, {-2, 8}), ({-14}, {3, 8}), ({-14}, {-12, 13}), ({-14}, {-2, 3, 13}),
    ({-14}, {-7, 8, 13}), ({-9}, {3}), ({-9}, {-7, 8}), ({-9}, {-2, 13}), ({-9}, {-12, 8, 13}),
    ({-4}, {-2, 3}), ({-4}, {-12, 8}), ({-4}, {-2, 8}), ({-4}, {-7, 3, 8}), ({-4}, {-7, -2, 13}),
    ({-4}, {-12, 3, 13}), ({1}, {-7, 3}), ({1}, {-2, 3}), ({1}, {-7, -2, 8}), ({1}, {-12, 3, 8}),
    ({1}, {-7, 13}), ({1}, {-12, -2, 13}), ({6}, {-2}), ({6}, {-12, 3}), ({6}, {-7, 8}),
    ({6}, {-12, -7, 13}), ({11}, {-7, -2}), ({11}, {-7, 3}), ({11}, {-12, -2, 3}),
    ({11}, {-12, -7, 8}), ({11}, {-12, 13})}
  | nextToNearestNeighbor => {({-13}, {1, 6}), ({-13}, {-9, 11}), ({-13}, {1, 11}),
    ({-13}, {-4, 6, 11}), ({-8}, {-4, 6}),  ({-8}, {1, 6}), ({-8}, {-4, 1, 11}),
    ({-8}, {-9, 6, 11}), ({-3}, {1}), ({-3}, {-9, 6}), ({-3}, {-4, 11}), ({2}, {-4, 1}),
    ({2}, {-4, 6}), ({2}, {-9, 1, 6}), ({2}, {-9, -4, 11}), ({7}, {-9, 1}), ({7}, {-4, 1}),
    ({7}, {-9, -4, 6}), ({7}, {-9, 11}), ({12}, {-4}), ({12}, {-9, 6})}

set_option maxRecDepth 2000 in
lemma isPresent_W1_iff_termW1PresentSubsets_mem_of_same (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ same.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ same.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      (∃ (x : termW1PresentSubsets .same), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_W1_iff_termW1PresentSubsets_mem_of_nearestNeighbor (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nearestNeighbor.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ nearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      (∃ (x : termW1PresentSubsets .nearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_W1_iff_termW1PresentSubsets_mem_of_nextToNearestNeighbor (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ nextToNearestNeighbor.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      (∃ (x : termW1PresentSubsets .nextToNearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  revert Q10
  revert Q5
  decide

lemma isPresent_W1_iff_termW1PresentSubsets_mem_of_card (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1))
    (h10 : Q10 ∈ I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      (∃ (x : termW1PresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  cases I
  case same =>
    exact isPresent_W1_iff_termW1PresentSubsets_mem_of_same Q5 Q10 h5 h10
  case nearestNeighbor =>
    exact isPresent_W1_iff_termW1PresentSubsets_mem_of_nearestNeighbor Q5 Q10 h5 h10
  case nextToNearestNeighbor =>
    exact isPresent_W1_iff_termW1PresentSubsets_mem_of_nextToNearestNeighbor Q5 Q10 h5 h10

set_option maxRecDepth 1000 in
/-- The term `W1` is present for `Q5` and `Q10` if and only if there is a pair of finite sets
  in `termW1PresentSubsets I` with the first a subset of `Q5` and the second a subset of `Q10`. -/
lemma isPresent_W1_iff_termW1PresentSubsets_mem (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset) (h10 : Q10 ∈ I.allowedTenCharges.powerset) :
    IsPresent W1 (Q5.val, Q10.val) ↔
      (∃ (x : termW1PresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  constructor
  · intro hPres
    rw [isPresent_W1_iff_Q5_subset_card_one] at hPres
    obtain ⟨Q5', h5sub, h5card, h5pres⟩ := hPres
    rw [isPresent_W1_iff_Q10_subset_card_three] at h5pres
    obtain ⟨Q10', h10sub, h10card, h10pres⟩ := h5pres
    rw [isPresent_W1_iff_termW1PresentSubsets_mem_of_card Q5' Q10'] at h10pres
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
    have hx10card : x.2.card ≤ 3 := by
      clear hx5 hx10
      revert x
      match I with
      | same => decide
      | nearestNeighbor => decide
      | nextToNearestNeighbor => decide
    rw [isPresent_W1_iff_Q5_subset_card_one]
    use x.1
    simp_all
    rw [isPresent_W1_iff_Q10_subset_card_three]
    use x.2
    simp_all
    rw [isPresent_W1_iff_termW1PresentSubsets_mem_of_card]
    use ⟨x, hx⟩
    simp_all
    exact fun ⦃a⦄ a_1 => h5 (hx5 a_1)
    simp_all
    exact fun ⦃a⦄ a_1 => h10 (hx10 a_1)

end SU5U1
end FTheory
