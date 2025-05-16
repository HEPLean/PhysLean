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
      x ∈ termW1PresentSubsets I ∧ x.1 ⊆ Q5 ∧ x.2 ⊆ Q10 ∨
      x ∈ termLambdaPresentSubsets I ∧ x.1 ⊆ Q5 ∧ x.2 ⊆ Q10)
      ↔ ∃ (x : X1 ), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10 := by
    rw [Finset.exists_coe]
    refine exists_congr ?_
    intro x
    simp_all only [Finset.mem_powerset, Subtype.exists, exists_and_left, exists_prop, Prod.exists,
      Finset.union_assoc, Finset.mem_union, X1]
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
    (∃ (x : protonDecayFiveTenPresentSubsets .nextToNearestNeighbor),
    x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) := by
  apply isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_subset_cond Q5 Q10 h5 h10
  · decide
  · decide

/-- The proton decay contributing term is present for `Q5` and `Q10` if and only if there is a
  pair of finite sets in `protonDecayFiveTenPresentSubsets I` with the first a subset of
  `Q5` and the second a subset of `Q10`. -/
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
    exact isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nearestNeighbor
      Q5 Q10 h5 h10
  | nextToNearestNeighbor =>
    exact isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem_of_nextToNearestNeighbor
      Q5 Q10 h5 h10

/-!

## Proton decay always present: Q10 sets.

There are some finite sets of `Q10` charges which if present, independent of the `Q5` charges,
will always permit a proton decay coupling (involving just the 5-bar and 10d matter fields).

This section gives the specifies these finite sets.
-/

def protonDecay510AllowedQ5OfQ10Exe (I : CodimensionOneConfig) (Q10 : Finset ℤ): Finset (Finset ℤ) :=
  let X := (((protonDecayFiveTenPresentSubsets I).filter (fun x => x.2 ⊆ Q10)).val.map
    (fun x => x.1)).toFinset
  let Q5P := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1 ∧ 0 < x.card)
  Q5P.filter (fun Q5 => ∀ (x : X), ¬ (x.1 ⊆ Q5))

def protonDecay510AlwaysPresentQ10Exe (I : CodimensionOneConfig) : Finset (Finset ℤ) :=
  let X := I.allowedTenCharges.powerset.filter (fun x => 0 < x.card)
  let X2 := X.filter (fun x => protonDecay510AllowedQ5OfQ10Exe I x = ∅)
  let X3 := X2.filter (fun x => ∀ y ∈ X2, x = y ∨ ¬ (y ⊆ x))
  X3

-- #eval protonDecay510AlwaysPresentQ10Exe nextToNearestNeighbor
def protonDecayAlwaysPresentQ10 : (I : CodimensionOneConfig) →  Finset (Finset ℤ)
  | same => {{-3, -1, 0}, {-2, -1, 0}, {-3, -2, 1}, {-1, 1}, {-3, 0, 1}, {-2, 0, 1}, {-3, -1, 2},
    {-2, -1, 2}, {-3, 0, 2}, {-1, 0, 2}, {-3, 1, 2}, {-2, 1, 2}, {0, 1, 2}, {-3, -1, 3},
    {-2, -1, 3}, {-2, 0, 3}, {-1, 0, 3}, {-3, 1, 3}, {-2, 1, 3}, {0, 1, 3}, {-3, -2, 2, 3},
    {-1, 2, 3}}
  | nearestNeighbor => {{-7, -2}, {-7, 3}, {-12, -2, 3}, {-12, -7, 8}, {-12, 3, 8}, {-2, 3, 8},
    {-12, -2, 13}, {-12, 3, 13}, {-2, 3, 13}, {-12, 8, 13}, {-2, 8, 13}}
  | nextToNearestNeighbor => {{-9, -4, 1}, {-9, -4, 6}, {1, 6}, {-9, -4, 11}, {-9, 1, 11},
    {-4, 1, 11}, {-9, 6, 11}, {-4, 6, 11}}

lemma mem_powerset_of_mem_protonDecayAlwaysPresentQ10 {I : CodimensionOneConfig}
    (x : Finset ℤ) (hx : x ∈ protonDecayAlwaysPresentQ10 I) :
    x ∈ I.allowedTenCharges.powerset := by
  revert x
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide

set_option maxRecDepth 2000 in
lemma protonDecayAlwaysPresentQ10_proton_decay_forall_Q5_card_one (I : CodimensionOneConfig) :
      ∀ (y : protonDecayAlwaysPresentQ10 I),
      ∀ (Q5' : I.allowedBarFiveCharges.powerset.filter (fun S => S.card ≤ 1 ∧ 0 < S.card )),
      (∃ (x : protonDecayFiveTenPresentSubsets I), x.1.1 ⊆ Q5' ∧ x.1.2 ⊆ y) := by
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide

lemma isPresent_protonDecay_of_Q10_mem_protonDecayAlwaysPresentQ10
    (I : CodimensionOneConfig) (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset)
    (h10Mem : ∃ (x : protonDecayAlwaysPresentQ10 I), x.1 ⊆ Q10) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ∨ Q5 = ∅ := by
  by_cases h5_empty : Q5 = ∅
  · simp [h5_empty]
  simp [h5_empty]
  have hl2 := protonDecayAlwaysPresentQ10_proton_decay_forall_Q5_card_one I
  by_contra hproton
  conv at hl2 =>
    enter [y, Q5']
    rw [← isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem _ _ (by
      have h2 := Q5'.2
      simp  [Finset.card_pos, -Finset.coe_mem] at h2
      simpa using h2.1) (mem_powerset_of_mem_protonDecayAlwaysPresentQ10 y.1 y.2)]
  simp at hproton
  rw [isPresent_K1_iff_Q5_subset_card_one] at hproton
  rw [isPresent_W1_iff_Q5_subset_card_one] at hproton
  rw [isPresent_Λ_iff_Q5_subset_card_two] at hproton
  simp at hproton
  have hexst : ∃ (S : Finset ℤ), S ⊆ Q5 ∧ S.card = 1 := by
    simp at h5_empty
    rw [@Finset.eq_empty_iff_forall_not_mem] at h5_empty
    simp at h5_empty
    obtain ⟨s, hs⟩ := h5_empty
    use {s}
    simp_all
  obtain ⟨S, hsub, hScard⟩ := hexst
  obtain ⟨y, hy⟩ := h10Mem
  have hSmem : S ∈ {S ∈ I.allowedBarFiveCharges.powerset | S.card ≤ 1 ∧ 0 < S.card} := by
    simp_all
    apply And.intro
    · exact fun ⦃a⦄ a_1 => h5 (hsub a_1)
    · rw [← Finset.one_le_card]
      omega
  have hl2' := hl2 y ⟨S, hSmem⟩
  simp_all
  have hP1 := hproton.1 S hsub (by omega)
  have hP2 := hproton.2.1 S hsub (by omega)
  have hP3 := hproton.2.2 S hsub (by omega)
  rcases hl2' with hr | hr | hr
  · have hr' := isPresent_K1_of_Q10_subset hy hr
    simp_all
  · have hr' := isPresent_W1_of_Q10_subset hy hr
    simp_all
  · have hr' := isPresent_Λ_of_Q10_subset hy hr
    simp_all

/-!

## Proton decay always present: Q5 sets.

There are some finite sets of `Q5` charges which if present, independent of the `Q10` charges,
will always permit a proton decay coupling (involving just the 5-bar and 10d matter fields).

This section gives the specifies these finite sets.

-/

def protonDecay510AllowedQ5OfQ5Exe (I : CodimensionOneConfig) (Q5 : Finset ℤ): Finset (Finset ℤ) :=
  let X := (((protonDecayFiveTenPresentSubsets I).filter (fun x => x.1 ⊆ Q5)).val.map
    (fun x => x.2)).toFinset
  let Q10P := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 1 ∧ 0 < x.card)
  Q10P.filter (fun Q10 => ∀ (x : X), ¬ (x.1 ⊆ Q10))

def protonDecay510AlwaysPresentQ5Exe (I : CodimensionOneConfig) : Finset (Finset ℤ) :=
  let X := I.allowedBarFiveCharges.powerset.filter (fun x => 0 < x.card)
  let X2 := X.filter (fun x => protonDecay510AllowedQ5OfQ5Exe I x = ∅)
  let X3 := X2.filter (fun x => ∀ y ∈ X2, x = y ∨ ¬ (y ⊆ x))
  X3

#eval protonDecay510AlwaysPresentQ5Exe nextToNearestNeighbor

def protonDecayAlwaysPresentQ5 : (I : CodimensionOneConfig) →  Finset (Finset ℤ)
  | same => {{-2, -1, 1, 2}, {-3, 0, 1, 2}, {-3, -1, 0, 3}, {-2, -1, 0, 3}, {-3, 0, 1, 3},
    {-3, -2, 0, 2, 3}}
  | nearestNeighbor => {{-14, -9, -4, 6}, {-14, 1, 6}, {-9, -4, 1, 6}, {-14, -9, 1, 11},
    {-14, -4, 1, 11}, {-9, -4, 1, 11}, {-9, -4, 6, 11}}
  | nextToNearestNeighbor => {{-13, 2, 7}, {-8, -3, 2, 7}, {-8, -3, 12}, {-13, -3, 2, 12}}

lemma mem_powerset_of_mem_protonDecayAlwaysPresentQ5 {I : CodimensionOneConfig}
    (x : Finset ℤ) (hx : x ∈ protonDecayAlwaysPresentQ5 I) :
    x ∈ I.allowedBarFiveCharges.powerset := by
  revert x
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide

set_option maxRecDepth 2000 in
lemma protonDecayAlwaysPresentQ5_proton_decay_forall_Q10_card_one (I : CodimensionOneConfig) :
      ∀ (y : protonDecayAlwaysPresentQ5 I),
      ∀ (Q10' : I.allowedTenCharges.powerset.filter (fun S => S.card ≤ 1 ∧ 0 < S.card )),
      (∃ (x : protonDecayFiveTenPresentSubsets I), x.1.1 ⊆ y ∧ x.1.2 ⊆ Q10') := by
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide

lemma isPresent_protonDecay_of_Q5_mem_protonDecayAlwaysPresentQ5
    (I : CodimensionOneConfig) (Q5 Q10 : Finset ℤ)
    (h5Mem : ∃ (x : protonDecayAlwaysPresentQ5 I), x.1 ⊆ Q5)
    (h10 : Q10 ∈ I.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ∨ Q10 = ∅ := by
  by_cases h10_empty : Q10 = ∅
  · simp [h10_empty]
  simp [h10_empty]
  have hl2 := protonDecayAlwaysPresentQ5_proton_decay_forall_Q10_card_one I
  by_contra hproton
  conv at hl2 =>
    enter [y, Q10']
    rw [← isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem _ _
      (mem_powerset_of_mem_protonDecayAlwaysPresentQ5 y.1 y.2)
      (by
      have h2 := Q10'.2
      simp  [Finset.card_pos, -Finset.coe_mem] at h2
      simpa using h2.1) ]
  simp at hproton
  rw [isPresent_K1_iff_Q10_subset_card_two] at hproton
  rw [isPresent_W1_iff_Q10_subset_card_three] at hproton
  rw [isPresent_Λ_iff_Q10_subset_card_one] at hproton
  simp at hproton
  have hexst : ∃ (S : Finset ℤ), S ⊆ Q10 ∧ S.card = 1 := by
    simp at h10_empty
    rw [@Finset.eq_empty_iff_forall_not_mem] at h10_empty
    simp at h10_empty
    obtain ⟨s, hs⟩ := h10_empty
    use {s}
    simp_all
  obtain ⟨S, hsub, hScard⟩ := hexst
  obtain ⟨y, hy⟩ := h5Mem
  have hSmem : S ∈ {S ∈ I.allowedTenCharges.powerset | S.card ≤ 1 ∧ 0 < S.card} := by
    simp_all
    apply And.intro
    · exact fun ⦃a⦄ a_1 => h10 (hsub a_1)
    · rw [← Finset.one_le_card]
      omega
  have hl2' := hl2 y ⟨S, hSmem⟩
  simp_all
  have hP1 := hproton.1 S hsub (by omega)
  have hP2 := hproton.2.1 S hsub (by omega)
  have hP3 := hproton.2.2 S hsub (by omega)
  rcases hl2' with hr | hr | hr
  · have hr' := isPresent_K1_of_Q5_subset hy hr
    simp_all
  · have hr' := isPresent_W1_of_Q5_subset hy hr
    simp_all
  · have hr' := isPresent_Λ_of_Q5_subset hy hr
    simp_all

lemma isPresent_protonDecay_of_Q5_card_ge_six
    (I : CodimensionOneConfig) (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset.filter (fun S => 6 ≤ S.card ∧ 0 < S.card))
    (h10 : Q10 ∈ I.allowedTenCharges.powerset) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ∨ Q10 = ∅ := by
  apply isPresent_protonDecay_of_Q5_mem_protonDecayAlwaysPresentQ5 I Q5 Q10 _ h10
  revert Q5
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide
/-!

## Combined

-/

def protonDecay510PresentSubsetsWithAlwaysExe (I : CodimensionOneConfig) :
    Finset (Finset ℤ × Finset ℤ) :=
  let X1 :=
    ((protonDecayAlwaysPresentQ5 I).val.map (fun Q5 => (Q5, ∅))).toFinset ∪
    ((protonDecayAlwaysPresentQ10 I).val.map (fun Q10 => (∅, Q10))).toFinset ∪
    protonDecayFiveTenPresentSubsets I
  let X2 := X1.filter (fun x => ∀ y ∈ X1, x = y ∨ ¬ (y.1 ⊆ x.1 ∧ y.2 ⊆ x.2))
  X2


#eval protonDecay510PresentSubsetsWithAlwaysExe nextToNearestNeighbor
def protonDecay510PresentSubsetsWithAlways :  (I : CodimensionOneConfig) →
    Finset (Finset ℤ × Finset ℤ)
  | same => {({-2, -1, 1, 2}, ∅), ({-3, 0, 1, 2}, ∅), ({-3, -1, 0, 3}, ∅), ({-2, -1, 0, 3}, ∅),
    ({-3, 0, 1, 3}, ∅), ({-3, -2, 0, 2, 3}, ∅), (∅, {-3, -1, 0}), (∅, {-2, -1, 0}),
    (∅, {-3, -2, 1}), (∅, {-1, 1}), (∅, {-3, 0, 1}), (∅, {-2, 0, 1}), (∅, {-3, -1, 2}),
    (∅, {-2, -1, 2}), (∅, {-3, 0, 2}), (∅, {-1, 0, 2}), (∅, {-3, 1, 2}), (∅, {-2, 1, 2}),
    (∅, {0, 1, 2}), (∅, {-3, -1, 3}), (∅, {-2, -1, 3}), (∅, {-2, 0, 3}), (∅, {-1, 0, 3}),
    (∅, {-3, 1, 3}), (∅, {-2, 1, 3}), (∅, {0, 1, 3}), (∅, {-3, -2, 2, 3}), (∅, {-1, 2, 3}),
    ({-3}, {-2, -1}), ({-3}, {-3, 0}), ({-2}, {-1}), ({-2}, {-2, 0}), ({-2}, {-3, 1}),
    ({-1}, {-1, 0}), ({-1}, {-2, 1}), ({0}, {-2, 2}), ({0}, {-3, 3}), ({1}, {0, 1}),
    ({1}, {-1, 2}), ({2}, {1}), ({2}, {0, 2}), ({2}, {-1, 3}), ({3}, {1, 2}), ({3}, {0, 3}),
    ({-1}, {2}), ({-2, -1}, {3}), ({-3, 0}, {3}), ({-2, 0}, {2}), ({-1, 0}, {1}), ({1}, {-2}),
    ({-3, 1}, {2}), ({-2, 1}, {1}), ({-1, 1}, {0}), ({0, 1}, {-1}), ({-2, 2}, {0}), ({-1, 2}, {-1}),
    ({0, 2}, {-2}), ({1, 2}, {-3}), ({-3, 3}, {0}), ({-1, 3}, {-2}), ({0, 3}, {-3}), ({-3}, {1}),
    ({-3}, {-1, 2}), ({-3}, {-3, 3}), ({-3}, {0, 3}), ({-3}, {-2, 2, 3}), ({-2}, {0, 1}),
    ({-2}, {-2, 2}), ({-2}, {0, 2}), ({-2}, {-3, 2, 3}), ({-1}, {0, 1}), ({-1}, {-1, 3}),
    ({0}, {0}), ({0}, {-2, 1}), ({0}, {-1, 2}), ({1}, {-1, 0}), ({1}, {-3, 1}), ({2}, {-2, 0}),
    ({2}, {-1, 0}), ({2}, {-2, 2}), ({2}, {-3, -2, 3}), ({3}, {-1}), ({3}, {-3, 0}), ({3}, {-2, 1}),
    ({3}, {-3, -2, 2}), ({3}, {-3, 3})}
  | nearestNeighbor => {({-14, -9, -4, 6}, ∅), ({-14, 1, 6}, ∅), ({-9, -4, 1, 6}, ∅),
    ({-14, -9, 1, 11}, ∅), ({-14, -4, 1, 11}, ∅), ({-9, -4, 1, 11}, ∅), ({-9, -4, 6, 11}, ∅),
    (∅, {-7, -2}), (∅, {-7, 3}), (∅, {-12, -2, 3}), (∅, {-12, -7, 8}), (∅, {-12, 3, 8}),
    (∅, {-2, 3, 8}), (∅, {-12, -2, 13}), (∅, {-12, 3, 13}), (∅, {-2, 3, 13}), (∅, {-12, 8, 13}),
    (∅, {-2, 8, 13}), ({-14}, {-7}), ({-14}, {-12, -2}), ({-4}, {-2}), ({1}, {-7, 8}),
    ({1}, {-12, 13}), ({6}, {3}), ({6}, {-7, 13}), ({11}, {3, 8}), ({11}, {-2, 13}),
    ({-4}, {8}), ({-9, -4}, {13}), ({1}, {-2}), ({-14, 1}, {13}), ({-9, 1}, {8}), ({-4, 1}, {3}),
    ({6}, {-12}), ({-14, 6}, {8}), ({1, 6}, {-7}), ({-14, 11}, {3}), ({-9, 11}, {-2}),
    ({-4, 11}, {-7}), ({1, 11}, {-12}), ({-14}, {-2, 8}), ({-14}, {3, 8}), ({-14}, {-12, 13}),
    ({-9}, {3}), ({-9}, {-7, 8}), ({-9}, {-2, 13}), ({1}, {-7, 13}), ({6}, {-2}), ({6}, {-7, 8}),
    ({11}, {-12, 13})}
  | nextToNearestNeighbor => {({-13, 2, 7}, ∅), ({-8, -3, 2, 7}, ∅), ({-8, -3, 12}, ∅),
    ({-13, -3, 2, 12}, ∅), (∅, {-9, -4, 1}), (∅, {-9, -4, 6}), (∅, {1, 6}), (∅, {-9, -4, 11}),
    (∅, {-9, 1, 11}), (∅, {-4, 1, 11}), (∅, {-9, 6, 11}), (∅, {-4, 6, 11}), ({-13}, {-9, -4}),
    ({-8}, {-4}), ({-8}, {-9, 1}), ({2}, {1}), ({2}, {-9, 11}), ({7}, {-4, 11}), ({12}, {6}),
    ({12}, {1, 11}), ({-3}, {6}), ({-8, -3}, {11}), ({2}, {-4}), ({-13, 2}, {11}), ({-8, 2}, {6}),
    ({-13, 7}, {6}), ({-8, 7}, {1}), ({-3, 7}, {-4}), ({2, 7}, {-9}), ({-13, 12}, {1}),
    ({-3, 12}, {-9}), ({-13}, {-9, 11}), ({-13}, {1, 11}), ({-3}, {1}), ({-3}, {-4, 11}),
    ({7}, {-9, 1}), ({7}, {-4, 1}), ({7}, {-9, 11}), ({12}, {-4})}

set_option maxRecDepth 2000 in
lemma mem_of_mem_protonDecay510PresentSubsetsWithAlways
    {I : CodimensionOneConfig} {x : Finset ℤ × Finset ℤ}
    (hx : x ∈ protonDecay510PresentSubsetsWithAlways I) :
    x ∈ (protonDecayAlwaysPresentQ5 I).val.map (fun Q5 => (Q5, ∅)) ∨
    x ∈ ((protonDecayAlwaysPresentQ10 I).val.map (fun Q10 => (∅, Q10))) ∨
    x ∈ protonDecayFiveTenPresentSubsets I := by
  revert x
  match I with
  | same => decide
  | nearestNeighbor => decide
  | nextToNearestNeighbor => decide

lemma isPresent_protonDecay_of_Q5_mem_rotonDecay510PresentSubsetsWithAlways
    (I : CodimensionOneConfig) (Q5 Q10 : Finset ℤ)
    (h5 : Q5 ∈ I.allowedBarFiveCharges.powerset)
    (h10 : Q10 ∈ I.allowedTenCharges.powerset)
    (hMem : ∃ (x : protonDecay510PresentSubsetsWithAlways I), x.1.1 ⊆ Q5 ∧ x.1.2 ⊆ Q10) :
    IsPresent K1 (Q5.val, Q10.val) ∨ IsPresent W1 (Q5.val, Q10.val) ∨
    IsPresent Λ (Q5.val, Q10.val) ∨ Q5 = ∅ ∨ Q10 = ∅ := by
  obtain ⟨⟨x, hx⟩, hx5, hx10⟩ := hMem
  rcases mem_of_mem_protonDecay510PresentSubsetsWithAlways hx with hr | hr | hr
  · simp at hr
    obtain ⟨y, hy, rfl⟩ := hr
    by_cases hQ5 : Q5 = ∅
    · simp [hQ5]
    · simp [hQ5]
      exact isPresent_protonDecay_of_Q5_mem_protonDecayAlwaysPresentQ5
        I Q5 Q10 ⟨⟨y, hy⟩, hx5⟩ h10
  · simp at hr
    obtain ⟨y, hy, rfl⟩ := hr
    by_cases hQ10 : Q10 = ∅
    · simp [hQ10]
    · simp [hQ10]
      exact isPresent_protonDecay_of_Q10_mem_protonDecayAlwaysPresentQ10
        I Q5 Q10 h5 ⟨⟨y, hy⟩, hx10⟩
  · have hl :   K1.IsPresent (Q5.val, Q10.val) ∨ W1.IsPresent (Q5.val, Q10.val) ∨
        Λ.IsPresent (Q5.val, Q10.val) := by
      rw [isPresent_protonDecay_for_five_ten_iff_termPresentSubsets_mem _ _ h5 h10]
      use ⟨x, hr⟩
    aesop

end SU5U1

end FTheory
