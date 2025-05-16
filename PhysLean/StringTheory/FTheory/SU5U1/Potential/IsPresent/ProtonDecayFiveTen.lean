/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.IsPresent.K1Term
import PhysLean.StringTheory.FTheory.SU5U1.Potential.IsPresent.LambdaTerm
import PhysLean.StringTheory.FTheory.SU5U1.Potential.IsPresent.W1Term
/-!

# Presence of proton decay through 5bar and 10d matter

This module contains results related to the presence of a proton-decay couplings
only involving the 5-bar and 10d matter fields
based on the additional `U(1)` charges carried by the `SU(5)` representations.
That is, not couplings containing also the Higgs.


## Key results

- `protonDecayFiveTenPresentSubsets`: The irreducible set of pairs of finite sets
  which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a  proton-decay coupling.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

open PotentialTerm CodimensionOneConfig

/-- An executable function which gives, for a given `CodimensionOneConfig`, gives
  the finite sets for which if contained in `Q5` and `Q10` permit a proton-decay coupling. -/
def protonDecayFiveTenPermitSubsetExe (I : CodimensionOneConfig) : Finset (Finset ℤ × Finset ℤ) :=
  let X1 := (termK1PresentSubsets I) ∪ (termLambdaPresentSubsets I) ∪ (termW1PresentSubsets I)
  let X2 := X1.filter (fun x => ∀ y ∈ X1, x = y ∨ ¬ (y.1 ⊆ x.1 ∧ y.2 ⊆ x.2))
  X2

/-- For a given `CodimensionOneConfig`, `I`, the irreducible set of
  pair a sets which if the first is a subset of `Q5` and the second is a subset of `Q10`,
  then `Q5` and `Q10` permit a proton-decay coupling.

  These subsets can be found with: e.g.
  `#eval (protonDecayFiveTenPermitSubsetExe nextToNearestNeighbor)`
-/
def protonDecayFiveTenPresentSubsets : (I : CodimensionOneConfig) → Finset (Finset ℤ × Finset ℤ)
  | same => {({-3}, {-2, -1}), ({-3}, {-3, 0}), ({-2}, {-1}), ({-2}, {-2, 0}), ({-2}, {-3, 1}),
    ({-1}, {-1, 0}), ({-1}, {-2, 1}), ({0}, {-1, 1}), ({0}, {-2, 2}), ({0}, {-3, 3}), ({1}, {0, 1}),
    ({1}, {-1, 2}), ({2}, {1}), ({2}, {0, 2}), ({2}, {-1, 3}), ({3}, {1, 2}), ({3}, {0, 3}),
    ({-1}, {2}), ({-2, -1}, {3}), ({-3, 0}, {3}), ({-2, 0}, {2}), ({-1, 0}, {1}), ({1}, {-2}),
    ({-3, 1}, {2}), ({-2, 1}, {1}), ({-1, 1}, {0}), ({0, 1}, {-1}), ({-2, 2}, {0}),
    ({-1, 2}, {-1}), ({0, 2}, {-2}), ({1, 2}, {-3}), ({-3, 3}, {0}), ({-1, 3}, {-2}),
    ({0, 3}, {-3}), ({-3}, {1}), ({-3}, {-1, 2}), ({-3}, {-3, 3}), ({-3}, {0, 3}),
    ({-3}, {-2, 2, 3}), ({-2}, {0, 1}), ({-2}, {-2, 2}), ({-2}, {0, 2}), ({-2}, {-2, 1, 3}),
    ({-2}, {-3, 2, 3}), ({-1}, {-1, 1}), ({-1}, {0, 1}), ({-1}, {-1, 3}), ({-1}, {-2, 0, 3}),
    ({-1}, {-3, 1, 3}), ({0}, {0}), ({0}, {-2, 1}), ({0}, {-1, 2}), ({0}, {-3, 1, 2}),
    ({0}, {-2, -1, 3}), ({1}, {-1, 0}), ({1}, {-3, 1}), ({1}, {-1, 1}), ({1}, {-3, 0, 2}),
    ({1}, {-3, -1, 3}), ({2}, {-2, 0}), ({2}, {-1, 0}), ({2}, {-2, 2}), ({2}, {-3, -1, 2}),
    ({2}, {-3, -2, 3}), ({3}, {-1}), ({3}, {-3, 0}), ({3}, {-2, 1}), ({3}, {-3, -2, 2}),
    ({3}, {-3, 3})}
  | nearestNeighbor => {({-14}, {-7}), ({-14}, {-12, -2}), ({-9}, {-7, -2}), ({-4}, {-2}),
    ({-4}, {-7, 3}), ({1}, {-7, 8}), ({1}, {-12, 13}), ({6}, {3}), ({6}, {-7, 13}),
    ({11}, {3, 8}), ({11}, {-2, 13}), ({-4}, {8}), ({-9, -4}, {13}), ({1}, {-2}),
    ({-14, 1}, {13}), ({-9, 1}, {8}), ({-4, 1}, {3}), ({6}, {-12}), ({-14, 6}, {8}),
    ({1, 6}, {-7}), ({-14, 11}, {3}), ({-9, 11}, {-2}), ({-4, 11}, {-7}), ({1, 11}, {-12}),
    ({-14}, {-2, 8}), ({-14}, {3, 8}), ({-14}, {-12, 13}), ({-14}, {-2, 3, 13}), ({-9}, {3}),
    ({-9}, {-7, 8}), ({-9}, {-2, 13}), ({-9}, {-12, 8, 13}), ({-4}, {-12, 3, 13}), ({1}, {-7, 3}),
    ({1}, {-12, 3, 8}), ({1}, {-7, 13}), ({6}, {-2}), ({6}, {-7, 8}), ({11}, {-7, -2}),
    ({11}, {-7, 3}), ({11}, {-12, -2, 3}), ({11}, {-12, -7, 8}), ({11}, {-12, 13})}
  | nextToNearestNeighbor => {({-13}, {-9, -4}), ({-8}, {-4}), ({-8}, {-9, 1}), ({2}, {1}),
    ({2}, {-9, 11}), ({7}, {1, 6}), ({7}, {-4, 11}), ({12}, {6}), ({12}, {1, 11}), ({-3}, {6}),
    ({-8, -3}, {11}), ({2}, {-4}), ({-13, 2}, {11}), ({-8, 2}, {6}), ({-13, 7}, {6}),
    ({-8, 7}, {1}), ({-3, 7}, {-4}), ({2, 7}, {-9}), ({-13, 12}, {1}), ({-3, 12}, {-9}),
    ({-13}, {1, 6}), ({-13}, {-9, 11}), ({-13}, {1, 11}), ({-13}, {-4, 6, 11}), ({-8}, {1, 6}),
    ({-8}, {-9, 6, 11}), ({-3}, {1}), ({-3}, {-4, 11}), ({7}, {-9, 1}), ({7}, {-4, 1}),
    ({7}, {-9, -4, 6}), ({7}, {-9, 11}), ({12}, {-4})}

lemma isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_subset_cond
    {I : CodimensionOneConfig}
    (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ I.allowedTenCharges.powerset)
    (hSubset1 :  ∀ (x : (termK1PresentSubsets I ∪ termW1PresentSubsets I ∪
      termLambdaPresentSubsets I : Finset (Finset ℤ × Finset ℤ))),
      ∃ (y : protonDecayFiveTenPresentSubsets I), y.1.1 ⊆ x.1.1 ∧ y.1.2 ⊆ x.1.2)
    (hSubset2 : ∀ (y : protonDecayFiveTenPresentSubsets I), y.1 ∈
      (termK1PresentSubsets I ∪ termW1PresentSubsets I ∪
      termLambdaPresentSubsets I : Finset (Finset ℤ × Finset ℤ))) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ↔
    (∃ (x : protonDecayFiveTenPresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  rw [isPresent_K1_iff_termK1PresentSubsets_mem Q5 Q10 h5 h10]
  rw [isPresent_W1_iff_termW1PresentSubsets_mem Q5 Q10 h5 h10]
  rw [isPresent_Λ_iff_termLambdaPresentSubsets_mem Q5 Q10 h5 h10]
  have h1 : (∃ (x : termK1PresentSubsets I), (x.1).1 ⊆ Q5 ∧ (x.1).2 ⊆ Q10) ↔
      ∃ x, (x ∈  termK1PresentSubsets I) ∧ (x.1 ⊆ Q5 ∧ x.2 ⊆ Q10) := by
    rw [Finset.exists_coe]
    refine exists_congr ?_
    intro x
    simp_all only [Finset.mem_powerset, exists_and_left, exists_prop]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]
  have h2 : (∃ (x : termW1PresentSubsets I), (x.1).1 ⊆ Q5 ∧ (x.1).2 ⊆ Q10) ↔
      ∃ x, (x ∈  termW1PresentSubsets I) ∧ (x.1 ⊆ Q5 ∧ x.2 ⊆ Q10) := by
    rw [Finset.exists_coe]
    refine exists_congr ?_
    intro x
    simp_all only [Finset.mem_powerset, exists_and_left, exists_prop]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]
  have h3 : (∃ (x : termLambdaPresentSubsets I), (x.1).1 ⊆ Q5 ∧ (x.1).2 ⊆ Q10) ↔
      ∃ x, (x ∈  termLambdaPresentSubsets I) ∧ (x.1 ⊆ Q5 ∧ x.2 ⊆ Q10) := by
    rw [Finset.exists_coe]
    refine exists_congr ?_
    intro x
    simp_all only [Finset.mem_powerset, exists_and_left, exists_prop]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]
  rw [h1, h2, h3]
  rw [← exists_or, ← exists_or]
  let X1 := termK1PresentSubsets I ∪ termW1PresentSubsets I ∪ termLambdaPresentSubsets I
  have h4 :  (∃ x,
    x ∈ termK1PresentSubsets I ∧ x.1 ⊆ Q5 ∧ x.2 ⊆ Q10 ∨
      x ∈ termW1PresentSubsets I ∧ x.1 ⊆ Q5 ∧ x.2 ⊆ Q10 ∨ x ∈ termLambdaPresentSubsets I ∧ x.1 ⊆ Q5 ∧ x.2 ⊆ Q10)
      ↔ ∃ (x : X1 ), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10 := by
    rw [Finset.exists_coe]
    refine exists_congr ?_
    intro x
    simp_all only [Finset.mem_powerset, Subtype.exists, exists_and_left, exists_prop, Prod.exists, Finset.union_assoc,
      Finset.mem_union, X1]
    apply Iff.intro
    · intro a
      cases a with
      | inl h => simp_all only [true_or, and_self]
      | inr h_1 =>
        cases h_1 with
        | inl h => simp_all only [true_or, or_true, and_self]
        | inr h_2 => simp_all only [or_true, and_self]
    · intro a
      simp_all only [and_self, and_true]
  rw [h4]
  have hredu {X1 X2 : Finset (Finset ℤ × Finset ℤ)}
      (h1 : ∀ (x : X1), ∃ (y : X2), y.1.1 ⊆ x.1.1 ∧ y.1.2 ⊆ x.1.2)
      (h2 : ∀ (y : X2), y.1 ∈ X1) :
      (∃ (x : X1), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) ↔ ∃ (x : X2), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10 := by
    constructor
    · intro ⟨x, hx5, hx10⟩
      obtain ⟨y, hy5, hy10⟩ := h1 x
      use y
      constructor
      · exact fun ⦃a⦄ a_1 => hx5 (hy5 a_1)
      · exact fun ⦃a⦄ a_1 => hx10 (hy10 a_1)
    · intro ⟨x, hx5, hx10⟩
      use ⟨x, h2 x⟩
  exact hredu hSubset1 hSubset2

set_option maxRecDepth 2000 in
lemma isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_same
    (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ same.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ same.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ↔
    (∃ (x : protonDecayFiveTenPresentSubsets .same), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  apply isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_subset_cond Q5 Q10 h5 h10
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nearestNeighbor
    (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nearestNeighbor.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ nearestNeighbor.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ↔
    (∃ (x : protonDecayFiveTenPresentSubsets .nearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  apply isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_subset_cond Q5 Q10 h5 h10
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nextToNearestNeighbor
    (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ nextToNearestNeighbor.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ↔
    (∃ (x : protonDecayFiveTenPresentSubsets .nextToNearestNeighbor), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  apply isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_subset_cond Q5 Q10 h5 h10
  · decide
  · decide

lemma isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem {I : CodimensionOneConfig}
    (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ I.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ↔
    (∃ (x : protonDecayFiveTenPresentSubsets I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  cases I with
  | same =>
    exact isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_same Q5 Q10 h5 h10
  | nearestNeighbor =>
    exact isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nearestNeighbor Q5 Q10 h5 h10
  | nextToNearestNeighbor =>
    exact isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nextToNearestNeighbor Q5 Q10 h5 h10

/-
def test (Q10 : Finset ℤ): Finset (Finset ℤ) :=
  let X := (((protonDecayFiveTenPresentSubsets same).filter (fun x => x.2 ⊆ Q10)).val.map
    (fun x => x.1)).toFinset
  let Q5P := same.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 5 ∧ 0 < x.card)
  Q5P.filter (fun Q5 => ∀ (x : X), ¬ (x.1 ⊆ Q5))-/

end SU5U1

end FTheory
