/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimallyAllowsTerm.OfFinset
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Yukawa
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfRationalSection
import Mathlib.Tactic.FinCases
/-!

# Charges which are not pheno-constrained and do not regenerate dangerous couplings with Yukawas

In this module we give a multiset of `ℤ`-valued charges which have values allowed
by a `CodimensionOneConfig`, `I`, which permit a top Yukawa coupling,
are not phenomenologically constrained, and do not regenerate dangerous couplings
with one insertion of a Yuakawa coupling.

## Key results

- `viableCharges` contains all charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.
- The lemma `mem_viableCharges_iff` expresses membership of `viableCharges I`, i.e.
  that it contains all charges which permit a top Yukawa coupling,
  are not phenomenologically constrained, and do not regenerate dangerous couplings.
- The proof of `mem_viableCharges_iff` is via `viableCompletions` which
  contains all completions of charges which minimally allow the top Yukawa,
  which are not phenomenologically constrained, and do not regenerate dangerous couplings.

## Implementation details

- This will eventually replace the files within `Charges.PhenoConstrainedElems`.
- Note that this file is slow to run, any improvements to the speed of this file
  will be very welcome.

-/
namespace FTheory

namespace SU5U1

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig
open Tree
open PhysLean

/-!

## Viable completions

-/


/--
The multiset of charges which are completions of charges which minimally allow the top Yukawa,
  which are not phenomenologically constrained, and do not regenerate dangerous couplings.

This can be constructed via

#eval
    ((minimallyAllowsTermsOfFinset same.allowedBarFiveCharges
        same.allowedTenCharges topYukawa).bind <|
      completions same.allowedBarFiveCharges same.allowedTenCharges).dedup.filter
    fun x => ¬ IsPhenoConstrained x
-/
private def viableCompletions (I : CodimensionOneConfig) : Multiset (Charges ℤ) :=
  match I with
  | same => {(some (-2), some (-3), {2}, {-3, 0}), (some (-1), some (-3), {1}, {-3, 0}),
    (some 1, some (-3), {-1}, {-3, 0}), (some 1, some (-3), {2}, {-3, 0}),
    (some 2, some (-3), {-2}, {-3, 0}), (some 2, some (-3), {1}, {-3, 0}),
    (some (-3), some (-2), {0}, {-1}), (some (-3), some (-2), {1}, {-1}),
    (some (-3), some (-2), {2}, {-1}), (some (-1), some (-2), {0}, {-1}),
    (some (-1), some (-2), {1}, {-1}), (some (-1), some (-2), {2}, {-1}),
    (some 0, some (-2), {-3}, {-1}), (some 0, some (-2), {-1}, {-1}),
    (some 0, some (-2), {1}, {-1}), (some 0, some (-2), {2}, {-1}),
    (some 1, some (-2), {-3}, {-1}), (some 1, some (-2), {-1}, {-1}),
    (some 1, some (-2), {0}, {-1}), (some 1, some (-2), {2}, {-1}),
    (some 2, some (-2), {-3}, {-1}), (some 2, some (-2), {-1}, {-1}),
    (some 2, some (-2), {0}, {-1}), (some 2, some (-2), {1}, {-1}),
    (some (-3), some (-2), {3}, {-2, 0}), (some (-1), some (-2), {3}, {-2, 0}),
    (some 3, some (-2), {-3}, {-2, 0}), (some (-1), some (-2), {0}, {-3, 1}),
    (some 0, some (-2), {-1}, {-3, 1}), (some 0, some (-2), {3}, {-3, 1}),
    (some 3, some (-2), {0}, {-3, 1}), (some (-2), some 0, {-1}, {-3, 3}),
    (some (-2), some 0, {1}, {-3, 3}), (some (-1), some 0, {-2}, {-3, 3}),
    (some (-1), some 0, {2}, {-3, 3}), (some 1, some 0, {-2}, {-3, 3}),
    (some 1, some 0, {2}, {-3, 3}), (some 2, some 0, {-1}, {-3, 3}),
    (some 2, some 0, {1}, {-3, 3}), (some (-2), some 2, {-1}, {1}),
    (some (-2), some 2, {0}, {1}), (some (-2), some 2, {1}, {1}),
    (some (-2), some 2, {3}, {1}), (some (-1), some 2, {-2}, {1}),
    (some (-1), some 2, {0}, {1}), (some (-1), some 2, {1}, {1}),
    (some (-1), some 2, {3}, {1}), (some 0, some 2, {-2}, {1}),
    (some 0, some 2, {-1}, {1}), (some 0, some 2, {1}, {1}),
    (some 0, some 2, {3}, {1}), (some 1, some 2, {-2}, {1}),
    (some 1, some 2, {-1}, {1}), (some 1, some 2, {0}, {1}),
    (some 3, some 2, {-2}, {1}), (some 3, some 2, {-1}, {1}),
    (some 3, some 2, {0}, {1}), (some (-3), some 2, {3}, {0, 2}),
    (some 1, some 2, {-3}, {0, 2}), (some 3, some 2, {-3}, {0, 2}),
    (some (-3), some 2, {0}, {-1, 3}), (some 0, some 2, {-3}, {-1, 3}),
    (some 0, some 2, {1}, {-1, 3}), (some 1, some 2, {0}, {-1, 3}),
    (some (-2), some 3, {-1}, {0, 3}), (some (-2), some 3, {2}, {0, 3}),
    (some (-1), some 3, {-2}, {0, 3}), (some (-1), some 3, {1}, {0, 3}),
    (some 1, some 3, {-1}, {0, 3}), (some 2, some 3, {-2}, {0, 3})}
  | nearestNeighbor => {(some (-9), some (-14), {-4}, {-7}), (some (-9), some (-14), {1}, {-7}),
    (some (-9), some (-14), {6}, {-7}), (some (-9), some (-14), {11}, {-7}),
    (some (-4), some (-14), {-9}, {-7}), (some (-4), some (-14), {1}, {-7}),
    (some (-4), some (-14), {6}, {-7}), (some (-4), some (-14), {11}, {-7}),
    (some 1, some (-14), {-9}, {-7}), (some 1, some (-14), {-4}, {-7}),
    (some 1, some (-14), {6}, {-7}), (some 1, some (-14), {11}, {-7}),
    (some 6, some (-14), {-9}, {-7}), (some 6, some (-14), {-4}, {-7}),
    (some 6, some (-14), {1}, {-7}), (some 6, some (-14), {11}, {-7}),
    (some 11, some (-14), {-9}, {-7}), (some 11, some (-14), {-4}, {-7}),
    (some 11, some (-14), {1}, {-7}), (some 11, some (-14), {6}, {-7}),
    (some 11, some (-14), {-9}, {-12, -2}), (some 1, some (-9), {11}, {-12, 3}),
    (some 11, some (-9), {1}, {-12, 3}), (some (-14), some (-4), {-9}, {-2}),
    (some (-14), some (-4), {11}, {-2}), (some (-9), some (-4), {-14}, {-2}),
    (some (-9), some (-4), {11}, {-2}), (some 1, some (-4), {-14}, {-2}),
    (some 1, some (-4), {11}, {-2}), (some 11, some (-4), {-14}, {-2}),
    (some 11, some (-4), {-9}, {-2}), (some (-9), some 1, {-4}, {-12, 13}),
    (some (-4), some 1, {-9}, {-12, 13}), (some 6, some 1, {-9}, {-12, 13}),
    (some (-14), some 6, {-4}, {3}), (some (-14), some 6, {1}, {3}),
    (some (-14), some 6, {11}, {3}), (some (-4), some 6, {-14}, {3}),
    (some (-4), some 6, {1}, {3}), (some (-4), some 6, {11}, {3}),
    (some 1, some 6, {-14}, {3}), (some 1, some 6, {-4}, {3}),
    (some 11, some 6, {-14}, {3}), (some 11, some 6, {-4}, {3}),
    (some (-9), some 6, {-4}, {-7, 13}), (some (-4), some 6, {-9}, {-7, 13}),
    (some (-4), some 6, {11}, {-7, 13}), (some 11, some 6, {-4}, {-7, 13})}
  | nextToNearestNeighbor => {(some (-13), some (-8), {7}, {-4}),
    (some (-3), some (-8), {7}, {-4}), (some 2, some (-8), {-13}, {-4}),
    (some 2, some (-8), {-3}, {-4}), (some 2, some (-8), {7}, {-4}),
    (some 7, some (-8), {-13}, {-4}), (some 7, some (-8), {-3}, {-4}),
    (some (-13), some 2, {-8}, {1}), (some (-13), some 2, {7}, {1}),
    (some (-13), some 2, {12}, {1}), (some (-8), some 2, {-13}, {1}),
    (some (-8), some 2, {7}, {1}), (some 7, some 2, {-13}, {1}),
    (some 7, some 2, {-8}, {1}), (some 7, some 2, {12}, {1}),
    (some 12, some 2, {-13}, {1}), (some 12, some 2, {7}, {1}),
    (some (-8), some 2, {-3}, {-9, 11}), (some (-3), some 2, {-8}, {-9, 11}),
    (some (-3), some 2, {12}, {-9, 11}), (some 12, some 2, {-3}, {-9, 11}),
    (some (-13), some 12, {-8}, {6}), (some (-13), some 12, {2}, {6}),
    (some (-13), some 12, {7}, {6}), (some (-8), some 12, {-13}, {6}),
    (some (-8), some 12, {2}, {6}), (some (-8), some 12, {7}, {6}),
    (some (-3), some 12, {-13}, {6}), (some (-3), some 12, {-8}, {6}),
    (some (-3), some 12, {2}, {6}), (some (-3), some 12, {7}, {6}),
    (some 2, some 12, {-13}, {6}), (some 2, some 12, {-8}, {6}),
    (some 2, some 12, {7}, {6}), (some 7, some 12, {-13}, {6}),
    (some 7, some 12, {-8}, {6}), (some 7, some 12, {2}, {6})}

lemma viableCompletions_card (I : CodimensionOneConfig) :
    (viableCompletions I).card = if I = same then 70 else
      if I = nearestNeighbor then 48 else 37 := by
  cases I <;> rfl

lemma viableCompletions_nodup (I : CodimensionOneConfig) :
    (viableCompletions I).Nodup := by
  cases I <;> decide

/-!

## Viable completions

We now prove that `viableCompletions I` contains all completions of
charges which minimally allow the top Yukawa, which are not
phenomenologically constrained, and which do not regenerate dangerous couplings
with one insertion of a Yukawa coupling.

This is broken up into a series of lemmas, but the main result is:
`viableCompletions_complete`.

-/

lemma viableCompletions_complete_of_same :
    ∀ x ∈ (minimallyAllowsTermsOfFinset CodimensionOneConfig.same.allowedBarFiveCharges
      CodimensionOneConfig.same.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions same.allowedBarFiveCharges same.allowedTenCharges x, ¬ y.IsPhenoConstrained
    ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ viableCompletions .same := by
  decide


lemma viableCompletions_complete_of_nearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nearestNeighbor.allowedBarFiveCharges
      nearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ viableCompletions .nearestNeighbor := by
  decide

lemma viableCompletions_complete_of_nextToNearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nextToNearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nextToNearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nextToNearestNeighbor.allowedBarFiveCharges
      nextToNearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
      ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ viableCompletions .nextToNearestNeighbor := by
  decide

lemma viableCompletions_complete {I : CodimensionOneConfig} (x : Charges)
    (hx : x ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
      I.allowedTenCharges topYukawa))
    (hPheno : ¬ x.IsPhenoConstrained) :
    ∀ y ∈ completions I.allowedBarFiveCharges I.allowedTenCharges x, ¬ y.IsPhenoConstrained
    ∧ ¬ y.YukawaGeneratesDangerousAtLevel 1
    → y ∈ viableCompletions I := by
  cases I
  case same => exact viableCompletions_complete_of_same x hx hPheno
  case nearestNeighbor => exact viableCompletions_complete_of_nearestNeighbor x hx hPheno
  case nextToNearestNeighbor => exact
    viableCompletions_complete_of_nextToNearestNeighbor x hx hPheno

/-!

## Existence of a subset in `viableCompletions`
-/

set_option maxRecDepth 2000 in
/-- Every charge `x : Charges` with values determined by an `I : CodimensionOneConfig`,
  which is not phenomenologically constrained, permits the top Yukawa, and
  does not regenerate danergours couplings with the Yukawa terms,
  has a subset which is contained within `viableCompletions I`.  -/
lemma exists_subset_viableCompletions_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (htopYukawa : AllowsTerm x topYukawa)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) : ∃ (y : Charges), y ∈ viableCompletions I ∧ y ⊆ x := by
  have hIrreducible :
        ∃ y ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
        I.allowedTenCharges topYukawa), y ⊆ x := by
      rw [allowsTerm_iff_subset_minimallyAllowsTerm] at htopYukawa
      obtain ⟨y, hPower, hIrre⟩ := htopYukawa
      use y
      constructor
      · rw [← minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset]
        · exact hIrre
        · simp at hPower
          exact mem_ofFinset_antitone I.allowedBarFiveCharges I.allowedTenCharges hPower hsub
      · simpa using hPower
  obtain ⟨y, hyMem, hysubsetx⟩ := hIrreducible
  obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete
    I.allowedBarFiveCharges I.allowedTenCharges y x hysubsetx hsub hcomplete
  use z
  constructor
  · refine viableCompletions_complete y hyMem ?_ z hz1 ?_
    · by_contra hn
      have h' := isPhenoConstrained_mono hysubsetx hn
      simp_all
    · apply And.intro
      · by_contra hn
        have h' := isPhenoConstrained_mono hz2 hn
        simp_all
      · by_contra hn
        have h' := yukawaGeneratesDangerousAtLevel_of_subset hz2 hn
        simp_all
  · simp_all
/-!

## The multisets of viable charges.

-/

TODO "JGVOQ" "Make the result `viableChargesExt` a safe definition."

/-- All charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  Note this is fast for evaluation, but to slow with `decide`. See `viableCharges`
  for an explicit vesion of this. -/
unsafe def viableChargesExt (I : CodimensionOneConfig) :
    Multiset (Charges ℤ) :=
    (aux (viableCompletions I) (viableCompletions I)).dedup
where
  /-- Auxillary recursive function to define `viableChargesExt`. -/
  aux : Multiset (Charges ℤ) →  Multiset (Charges ℤ) →  Multiset (Charges ℤ) :=
    fun all add  =>
      if add = ∅ then all else
      let s := add.bind fun x =>
         (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val
      let s2 := s.filter fun y => y ∉ all ∧
        ¬ IsPhenoConstrained y ∧ ¬ YukawaGeneratesDangerousAtLevel y 1
      aux (all + s2) s2

/-- All charges, for `I = same`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.  -/
private def viableChargesSame : Multiset (Charges ℤ) :=
   {(some (-2), some (-3), {2}, {-3, 0}), (some (-1), some (-3), {1}, {-3, 0}),
    (some 1, some (-3), {-1}, {-3, 0}), (some 1, some (-3), {2}, {-3, 0}),
    (some 2, some (-3), {-2}, {-3, 0}), (some 2, some (-3), {1}, {-3, 0}),
    (some (-3), some (-2), {0}, {-1}), (some (-3), some (-2), {1}, {-1}),
    (some (-3), some (-2), {2}, {-1}), (some (-1), some (-2), {0}, {-1}),
    (some (-1), some (-2), {1}, {-1}), (some (-1), some (-2), {2}, {-1}),
    (some 0, some (-2), {-3}, {-1}), (some 0, some (-2), {-1}, {-1}),
    (some 0, some (-2), {1}, {-1}), (some 0, some (-2), {2}, {-1}),
    (some 1, some (-2), {-3}, {-1}), (some 1, some (-2), {-1}, {-1}),
    (some 1, some (-2), {0}, {-1}), (some 1, some (-2), {2}, {-1}),
    (some 2, some (-2), {-3}, {-1}), (some 2, some (-2), {-1}, {-1}),
    (some 2, some (-2), {0}, {-1}), (some 2, some (-2), {1}, {-1}),
    (some (-3), some (-2), {3}, {-2, 0}), (some (-1), some (-2), {3}, {-2, 0}),
    (some 3, some (-2), {-3}, {-2, 0}), (some (-1), some (-2), {0}, {-3, 1}),
    (some 0, some (-2), {-1}, {-3, 1}), (some 0, some (-2), {3}, {-3, 1}),
    (some 3, some (-2), {0}, {-3, 1}), (some (-2), some 0, {-1}, {-3, 3}),
    (some (-2), some 0, {1}, {-3, 3}), (some (-1), some 0, {-2}, {-3, 3}),
    (some (-1), some 0, {2}, {-3, 3}), (some 1, some 0, {-2}, {-3, 3}),
    (some 1, some 0, {2}, {-3, 3}), (some 2, some 0, {-1}, {-3, 3}),
    (some 2, some 0, {1}, {-3, 3}), (some (-2), some 2, {-1}, {1}),
    (some (-2), some 2, {0}, {1}), (some (-2), some 2, {1}, {1}),
    (some (-2), some 2, {3}, {1}), (some (-1), some 2, {-2}, {1}),
    (some (-1), some 2, {0}, {1}), (some (-1), some 2, {1}, {1}),
    (some (-1), some 2, {3}, {1}), (some 0, some 2, {-2}, {1}),
    (some 0, some 2, {-1}, {1}), (some 0, some 2, {1}, {1}),
    (some 0, some 2, {3}, {1}), (some 1, some 2, {-2}, {1}),
    (some 1, some 2, {-1}, {1}), (some 1, some 2, {0}, {1}),
    (some 3, some 2, {-2}, {1}), (some 3, some 2, {-1}, {1}),
    (some 3, some 2, {0}, {1}), (some (-3), some 2, {3}, {0, 2}),
    (some 1, some 2, {-3}, {0, 2}), (some 3, some 2, {-3}, {0, 2}),
    (some (-3), some 2, {0}, {-1, 3}), (some 0, some 2, {-3}, {-1, 3}),
    (some 0, some 2, {1}, {-1, 3}), (some 1, some 2, {0}, {-1, 3}),
    (some (-2), some 3, {-1}, {0, 3}), (some (-2), some 3, {2}, {0, 3}),
    (some (-1), some 3, {-2}, {0, 3}), (some (-1), some 3, {1}, {0, 3}),
    (some 1, some 3, {-1}, {0, 3}), (some 2, some 3, {-2}, {0, 3}),
    (some 1, some (-3), {-1, 2}, {-3, 0}), (some 2, some (-3), {-2, 1}, {-3, 0}),
    (some (-3), some (-2), {0}, {3, -1}), (some (-3), some (-2), {0, 2}, {-1}),
    (some (-3), some (-2), {2}, {-3, -1}), (some (-1), some (-2), {0, 2}, {-1}),
    (some 0, some (-2), {-3}, {3, -1}), (some 0, some (-2), {-3, 1}, {-1}),
    (some 0, some (-2), {1}, {3, -1}), (some 1, some (-2), {0}, {3, -1}),
    (some 2, some (-2), {-3}, {-3, -1}), (some 2, some (-2), {-3, -1}, {-1}),
    (some 2, some (-2), {-3, 0}, {-1}), (some 2, some (-2), {-1, 1}, {-1}),
    (some 0, some (-2), {-1, 3}, {-3, 1}), (some (-2), some 2, {-1, 1}, {1}),
    (some (-2), some 2, {0, 3}, {1}), (some (-2), some 2, {1, 3}, {1}),
    (some (-2), some 2, {3}, {3, 1}), (some (-1), some 2, {0}, {-3, 1}),
    (some 0, some 2, {-1}, {-3, 1}), (some 0, some 2, {-1, 3}, {1}),
    (some 0, some 2, {3}, {-3, 1}), (some 1, some 2, {-2, 0}, {1}),
    (some 3, some 2, {-2}, {3, 1}), (some 3, some 2, {-2, 0}, {1}),
    (some 3, some 2, {0}, {-3, 1}), (some 0, some 2, {-3, 1}, {-1, 3}),
    (some (-2), some 3, {-1, 2}, {0, 3}), (some (-1), some 3, {-2, 1}, {0, 3}),
    (some 0, some (-2), {-3, 1}, {3, -1}), (some 0, some 2, {-1, 3}, {-3, 1})}

/-- All charges, for `I = nearestNeighbor`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.  -/
private def viableChargesNN : Multiset (Charges ℤ) :=
  {(some (-9), some (-14), {-4}, {-7}), (some (-9), some (-14), {1}, {-7}),
    (some (-9), some (-14), {6}, {-7}), (some (-9), some (-14), {11}, {-7}),
    (some (-4), some (-14), {-9}, {-7}), (some (-4), some (-14), {1}, {-7}),
    (some (-4), some (-14), {6}, {-7}), (some (-4), some (-14), {11}, {-7}),
    (some 1, some (-14), {-9}, {-7}), (some 1, some (-14), {-4}, {-7}),
    (some 1, some (-14), {6}, {-7}), (some 1, some (-14), {11}, {-7}),
    (some 6, some (-14), {-9}, {-7}), (some 6, some (-14), {-4}, {-7}),
    (some 6, some (-14), {1}, {-7}),  (some 6, some (-14), {11}, {-7}),
    (some 11, some (-14), {-9}, {-7}), (some 11, some (-14), {-4}, {-7}),
    (some 11, some (-14), {1}, {-7}), (some 11, some (-14), {6}, {-7}),
    (some 11, some (-14), {-9}, {-12, -2}), (some 1, some (-9), {11}, {-12, 3}),
    (some 11, some (-9), {1}, {-12, 3}), (some (-14), some (-4), {-9}, {-2}),
    (some (-14), some (-4), {11}, {-2}), (some (-9), some (-4), {-14}, {-2}),
    (some (-9), some (-4), {11}, {-2}), (some 1, some (-4), {-14}, {-2}),
    (some 1, some (-4), {11}, {-2}), (some 11, some (-4), {-14}, {-2}),
    (some 11, some (-4), {-9}, {-2}), (some (-9), some 1, {-4}, {-12, 13}),
    (some (-4), some 1, {-9}, {-12, 13}), (some 6, some 1, {-9}, {-12, 13}),
    (some (-14), some 6, {-4}, {3}), (some (-14), some 6, {1}, {3}),
    (some (-14), some 6, {11}, {3}), (some (-4), some 6, {-14}, {3}),
    (some (-4), some 6, {1}, {3}), (some (-4), some 6, {11}, {3}),
    (some 1, some 6, {-14}, {3}), (some 1, some 6, {-4}, {3}),
    (some 11, some 6, {-14}, {3}), (some 11, some 6, {-4}, {3}),
    (some (-9), some 6, {-4}, {-7, 13}), (some (-4), some 6, {-9}, {-7, 13}),
    (some (-4), some 6, {11}, {-7, 13}), (some 11, some 6, {-4}, {-7, 13}),
    (some (-9), some (-14), {-4}, {13, -7}), (some (-9), some (-14), {-4, 6}, {-7}),
    (some (-4), some (-14), {-9}, {13, -7}), (some (-4), some (-14), {-9, 6}, {-7}),
    (some (-4), some (-14), {-9, 11}, {-7}), (some (-4), some (-14), {6, 11}, {-7}),
    (some (-4), some (-14), {11}, {13, -7}), (some 1, some (-14), {-4, 6}, {-7}),
    (some 6, some (-14), {-9, -4}, {-7}), (some 6, some (-14), {-4}, {-12, -7}),
    (some 6, some (-14), {-9, 1}, {-7}), (some 6, some (-14), {1, 11}, {-7}),
    (some 11, some (-14), {-9, -4}, {-7}), (some 11, some (-14), {-4}, {13, -7}),
    (some 11, some (-14), {-4, 1}, {-7}), (some 11, some (-14), {-9, 6}, {-7}),
    (some (-9), some (-4), {-14, 11}, {-2}), (some (-9), some (-4), {11}, {-12, -2}),
    (some 1, some (-4), {-14, 11}, {-2}), (some (-14), some 6, {1, 11}, {3}),
    (some 11, some 6, {-14, -4}, {3}), (some (-4), some 6, {-9, 11}, {-7, 13}),
    (some (-4), some (-14), {-9, 11}, {13, -7})}

/-- All charges, for `I = nextToNearestNeighbor`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.  -/
private def viableChargesNtoNN : Multiset (Charges ℤ) :=
  {(some (-13), some (-8), {7}, {-4}), (some (-3), some (-8), {7}, {-4}),
    (some 2, some (-8), {-13}, {-4}), (some 2, some (-8), {-3}, {-4}),
    (some 2, some (-8), {7}, {-4}), (some 7, some (-8), {-13}, {-4}),
    (some 7, some (-8), {-3}, {-4}), (some (-13), some 2, {-8}, {1}),
    (some (-13), some 2, {7}, {1}), (some (-13), some 2, {12}, {1}),
    (some (-8), some 2, {-13}, {1}), (some (-8), some 2, {7}, {1}),
    (some 7, some 2, {-13}, {1}), (some 7, some 2, {-8}, {1}),
    (some 7, some 2, {12}, {1}), (some 12, some 2, {-13}, {1}),
    (some 12, some 2, {7}, {1}), (some (-8), some 2, {-3}, {-9, 11}),
    (some (-3), some 2, {-8}, {-9, 11}), (some (-3), some 2, {12}, {-9, 11}),
    (some 12, some 2, {-3}, {-9, 11}), (some (-13), some 12, {-8}, {6}),
    (some (-13), some 12, {2}, {6}), (some (-13), some 12, {7}, {6}),
    (some (-8), some 12, {-13}, {6}), (some (-8), some 12, {2}, {6}),
    (some (-8), some 12, {7}, {6}), (some (-3), some 12, {-13}, {6}),
    (some (-3), some 12, {-8}, {6}), (some (-3), some 12, {2}, {6}),
    (some (-3), some 12, {7}, {6}), (some 2, some 12, {-13}, {6}),
    (some 2, some 12, {-8}, {6}), (some 2, some 12, {7}, {6}),
    (some 7, some 12, {-13}, {6}), (some 7, some 12, {-8}, {6}),
    (some 7, some 12, {2}, {6}), (some (-13), some 2, {-8, 12}, {1}),
    (some (-8), some 2, {-13, 7}, {1}), (some 7, some 2, {-8, 12}, {1}),
    (some 12, some 2, {-13, 7}, {1}), (some (-3), some 2, {-8, 12}, {-9, 11}),
    (some (-13), some 12, {-8}, {-9, 6}), (some (-13), some 12, {-8, 7}, {6}),
    (some (-13), some 12, {7}, {-4, 6}), (some (-8), some 12, {-13}, {-9, 6}),
    (some (-8), some 12, {-13, 2}, {6}), (some (-8), some 12, {2, 7}, {6}),
    (some 2, some 12, {-13, -8}, {6}), (some 2, some 12, {-8, 7}, {6}),
    (some 7, some 12, {-13, 2}, {6})}

/-- All charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  These trees can be found with e.g.
  `#eval viableChargesExt nextToNearestNeighbor`. -/
def viableCharges : (I : CodimensionOneConfig) →  Multiset (Charges ℤ)
  | same => viableChargesSame
  | nearestNeighbor => viableChargesNN
  | nextToNearestNeighbor => viableChargesNtoNN

/-!

## Basic properties

-/

lemma viableCharges_nodup (I : CodimensionOneConfig) :
    (viableCharges I).Nodup := by
  decide +revert

lemma viableCharges_card (I : CodimensionOneConfig) :
    (viableCharges I).card =
    if I = .same then 102 else
    if I = .nearestNeighbor then 71 else 51  := by
  decide +revert

lemma isComplete_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), IsComplete x := by
 revert I
 decide

lemma allowsTerm_topYukawa_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.AllowsTerm topYukawa := by
  revert I
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ IsPhenoConstrained x := by
  revert I
  decide

set_option maxRecDepth 2000 in
lemma not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges
    (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  revert I
  decide

lemma card_five_bar_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.2.2.1.card ≤ 2 := by
  revert I
  decide

lemma card_ten_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.2.2.2.card ≤ 2 := by
  revert I
  decide

set_option maxRecDepth 2000 in
lemma not_viable_of_insert_5_bar_viableCharges_same  :
    ∀ q5 ∈ same.allowedBarFiveCharges,
    ∀ x ∈ (viableCharges same),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges same
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma not_viable_of_insert_5_bar_viableCharges_NN :
    ∀ q5 ∈ nearestNeighbor.allowedBarFiveCharges,
    ∀ x ∈ (viableCharges nearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges nearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma not_viable_of_insert_5_bar_viableCharges_NNToN  :
    ∀ q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges,
    ∀ x ∈ (viableCharges nextToNearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges nextToNearestNeighbor
    ∨ YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Inserting a `q5` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenolically constrained or regenerates dangourous couplings
  with the Yukawas. -/
lemma not_viable_of_insert_5_bar_viableCharges (I : CodimensionOneConfig) :
    ∀ q5 ∈ I.allowedBarFiveCharges,
    ∀ x ∈ (viableCharges I),
    let y : Charges ℤ := (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges I
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  fin_cases I
  · exact not_viable_of_insert_5_bar_viableCharges_same
  · exact not_viable_of_insert_5_bar_viableCharges_NN
  · exact not_viable_of_insert_5_bar_viableCharges_NNToN


set_option maxRecDepth 2000 in
lemma not_viable_of_insert_ten_viableCharges_same  :
    ∀ q10 ∈ same.allowedTenCharges,
    ∀ x ∈ (viableCharges same),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges same
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

set_option maxRecDepth 2000 in
lemma not_viable_of_insert_ten_viableCharges_NN  :
    ∀ q10 ∈ nearestNeighbor.allowedTenCharges,
    ∀ x ∈ (viableCharges nearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges nearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  repeat decide

set_option maxRecDepth 2000 in
lemma not_viable_of_insert_ten_viableCharges_NNToN  :
    ∀ q10 ∈ nextToNearestNeighbor.allowedTenCharges,
    ∀ x ∈ (viableCharges nextToNearestNeighbor),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges nextToNearestNeighbor
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  intro q5 hq5
  fin_cases hq5
  repeat decide

/-- Inserting a `q5` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenolically constrained or regenerates dangourous couplings
  with the Yukawas. -/
lemma not_viable_of_insert_ten_viableCharges (I : CodimensionOneConfig) :
    ∀ q10 ∈ I.allowedTenCharges,
    ∀ x ∈ (viableCharges I),
    let y : Charges ℤ := (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2)
    IsPhenoConstrained y ∨ y ∈ viableCharges I
    ∨  YukawaGeneratesDangerousAtLevel y 1 := by
  fin_cases I
  · exact not_viable_of_insert_ten_viableCharges_same
  · exact not_viable_of_insert_ten_viableCharges_NN
  · exact not_viable_of_insert_ten_viableCharges_NNToN

/-!

## Proof of completeness.

-/


set_option maxRecDepth 2000 in
lemma viableCompletions_subset_viableCharges (I : CodimensionOneConfig) :
      ∀ x ∈ (viableCompletions I), x ∈ viableCharges I := by
  decide +revert

set_option maxRecDepth 2000 in
lemma not_viable_of_not_mem_viableCharges {x : Charges}
    (hx : ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) :
    x ∉ viableCharges I → ¬ ((¬ IsPhenoConstrained x ∧
    ¬ YukawaGeneratesDangerousAtLevel x 1) ∧
      AllowsTerm x topYukawa) := by
  by_cases hn : ¬ (AllowsTerm x topYukawa)
  · simp [hn]
  rw [not_and]
  simp only [hn, imp_false]
  simp at hn
  obtain ⟨y, y_mem, hyx⟩ :=
    exists_subset_viableCompletions_of_not_isPhenoConstrained hx hn hsub hcomplete
  refine subset_insert_filter_card_zero (viableCharges I)
    I.allowedBarFiveCharges I.allowedTenCharges (fun x =>
      (¬x.IsPhenoConstrained ∧ ¬x.YukawaGeneratesDangerousAtLevel 1))
    ?_ ?_ y ?_ x hyx hsub ?_ ?_
  · intro x y hxy
    simp only [Decidable.not_not]
    simp
    intro h1 h2
    apply yukawaGeneratesDangerousAtLevel_of_subset hxy
    apply h1
    intro hn
    apply h2
    exact isPhenoConstrained_mono hxy hn
  · intro x
    exact fun a => isComplete_of_mem_viableCharges I x a
  · apply viableCompletions_subset_viableCharges
    exact y_mem
  · intro q10
    rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
    simp
    intro z hz hzP h2
    have h1 := not_viable_of_insert_ten_viableCharges I q10 q10.2 z hz
    simp_all
  · intro q5
    rw [Multiset.empty_eq_zero, Multiset.eq_zero_iff_forall_notMem]
    simp
    intro z hz hzP h2
    have h1 := not_viable_of_insert_5_bar_viableCharges I q5 q5.2 z hz
    simp_all

lemma mem_viableCharges_iff {x : Charges}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    x ∈ viableCharges I ↔ AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact allowsTerm_topYukawa_of_mem_viableCharges I x h
    · exact not_isPhenoConstrained_of_mem_viableCharges I x h
    · exact not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges I x h
    · exact isComplete_of_mem_viableCharges I x h
  · intro ⟨hTop, hPheno, hY, hComplete⟩
    by_contra hn
    apply not_viable_of_not_mem_viableCharges ⟨hPheno, hY⟩ hsub hComplete hn
    simp_all

end Charges

end SU5U1

end FTheory
