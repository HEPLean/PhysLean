/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.PhenoClosed
import PhysLean.StringTheory.FTheory.SU5.Charges.OfRationalSection
/-!

Note this file takes a long time to compile.

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
- The lemma `mem_viableCharges_iff` follows directly from
  `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`
  and a number of conditions on `viableCharges` which can be proved using the `decide`
  tactic.
- `viableCharges` itself is constructed via `viableCompletions` which
  contains all completions of charges which minimally allow the top Yukawa,
  which are not phenomenologically constrained, and do not regenerate dangerous couplings.

## Implementation details

- Note that this file is slow to run, any improvements to the speed of this file
  will be very welcome. In particular working out a way to restrict by anomaly cancellation.

-/
namespace FTheory

namespace SU5

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig
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
  | same => {
    /- qHu = -3, and Q10 = {-3, 0} -/
    (some (-2), some (-3), {2}, {-3, 0}), (some (-1), some (-3), {1}, {-3, 0}),
    (some 1, some (-3), {-1}, {-3, 0}), (some 1, some (-3), {2}, {-3, 0}),
    (some 2, some (-3), {-2}, {-3, 0}), (some 2, some (-3), {1}, {-3, 0}),
    /- qHu = -2, and Q10 = {-1} -/
    (some (-3), some (-2), {0}, {-1}), (some (-3), some (-2), {1}, {-1}),
    (some (-3), some (-2), {2}, {-1}), (some (-1), some (-2), {0}, {-1}),
    (some (-1), some (-2), {1}, {-1}), (some (-1), some (-2), {2}, {-1}),
    (some 0, some (-2), {-3}, {-1}), (some 0, some (-2), {-1}, {-1}),
    (some 0, some (-2), {1}, {-1}), (some 0, some (-2), {2}, {-1}),
    (some 1, some (-2), {-3}, {-1}), (some 1, some (-2), {-1}, {-1}),
    (some 1, some (-2), {0}, {-1}), (some 1, some (-2), {2}, {-1}),
    (some 2, some (-2), {-3}, {-1}), (some 2, some (-2), {-1}, {-1}),
    (some 2, some (-2), {0}, {-1}), (some 2, some (-2), {1}, {-1}),
    /- qHu = -2, and Q10 = {-2, 0} -/
    (some (-3), some (-2), {3}, {-2, 0}), (some (-1), some (-2), {3}, {-2, 0}),
    (some 3, some (-2), {-3}, {-2, 0}),
    /- qHu = -2, and Q10 = {-3, 1} -/
    (some (-1), some (-2), {0}, {-3, 1}),(some 0, some (-2), {-1}, {-3, 1}),
    (some 0, some (-2), {3}, {-3, 1}), (some 3, some (-2), {0}, {-3, 1}),
    /- qHu = 0, and Q10 = {-3, 3} -/
    (some (-2), some 0, {-1}, {-3, 3}), (some (-2), some 0, {1}, {-3, 3}),
    (some (-1), some 0, {-2}, {-3, 3}), (some (-1), some 0, {2}, {-3, 3}),
    (some 1, some 0, {-2}, {-3, 3}), (some 1, some 0, {2}, {-3, 3}),
    (some 2, some 0, {-1}, {-3, 3}), (some 2, some 0, {1}, {-3, 3}),
    /- qHu = 2, and Q10 = {1} -/
    (some (-2), some 2, {-1}, {1}), (some (-2), some 2, {0}, {1}), (some (-2), some 2, {1}, {1}),
    (some (-2), some 2, {3}, {1}), (some (-1), some 2, {-2}, {1}), (some (-1), some 2, {0}, {1}),
    (some (-1), some 2, {1}, {1}), (some (-1), some 2, {3}, {1}), (some 0, some 2, {-2}, {1}),
    (some 0, some 2, {-1}, {1}), (some 0, some 2, {1}, {1}), (some 0, some 2, {3}, {1}),
    (some 1, some 2, {-2}, {1}), (some 1, some 2, {-1}, {1}), (some 1, some 2, {0}, {1}),
    (some 3, some 2, {-2}, {1}), (some 3, some 2, {-1}, {1}), (some 3, some 2, {0}, {1}),
    /- qHu = 2, and Q10 = {0, 2} -/
    (some (-3), some 2, {3}, {0, 2}), (some 1, some 2, {-3}, {0, 2}),
    (some 3, some 2, {-3}, {0, 2}),
    /- qHu = 2, and Q10 = {-1, 3} -/
    (some (-3), some 2, {0}, {-1, 3}), (some 0, some 2, {-3}, {-1, 3}),
    (some 0, some 2, {1}, {-1, 3}), (some 1, some 2, {0}, {-1, 3}),
    /- qHu = 3, and Q10 = {0, 3} -/
    (some (-2), some 3, {-1}, {0, 3}), (some (-2), some 3, {2}, {0, 3}),
    (some (-1), some 3, {-2}, {0, 3}), (some (-1), some 3, {1}, {0, 3}),
    (some 1, some 3, {-1}, {0, 3}), (some 2, some 3, {-2}, {0, 3})}
  | nearestNeighbor => {
    /- qHu = -14, and Q10 = {-7} -/
    (some (-9), some (-14), {-4}, {-7}), (some (-9), some (-14), {1}, {-7}),
    (some (-9), some (-14), {6}, {-7}), (some (-9), some (-14), {11}, {-7}),
    (some (-4), some (-14), {-9}, {-7}), (some (-4), some (-14), {1}, {-7}),
    (some (-4), some (-14), {6}, {-7}), (some (-4), some (-14), {11}, {-7}),
    (some 1, some (-14), {-9}, {-7}), (some 1, some (-14), {-4}, {-7}),
    (some 1, some (-14), {6}, {-7}), (some 1, some (-14), {11}, {-7}),
    (some 6, some (-14), {-9}, {-7}), (some 6, some (-14), {-4}, {-7}),
    (some 6, some (-14), {1}, {-7}), (some 6, some (-14), {11}, {-7}),
    (some 11, some (-14), {-9}, {-7}), (some 11, some (-14), {-4}, {-7}),
    (some 11, some (-14), {1}, {-7}), (some 11, some (-14), {6}, {-7}),
    /- qHu = -14, and Q10 = {-12, -2} -/
    (some 11, some (-14), {-9}, {-12, -2}),
    /- qHu = -9, and Q10 = {-12, 3} -/
    (some 1, some (-9), {11}, {-12, 3}), (some 11, some (-9), {1}, {-12, 3}),
    /- qHu = -4, and Q10 = {-2} -/
    (some (-14), some (-4), {-9}, {-2}), (some (-14), some (-4), {11}, {-2}),
    (some (-9), some (-4), {-14}, {-2}), (some (-9), some (-4), {11}, {-2}),
    (some 1, some (-4), {-14}, {-2}), (some 1, some (-4), {11}, {-2}),
    (some 11, some (-4), {-14}, {-2}), (some 11, some (-4), {-9}, {-2}),
    /- qHu = 1, and Q10 = {-12, 13} -/
    (some (-9), some 1, {-4}, {-12, 13}), (some (-4), some 1, {-9}, {-12, 13}),
    (some 6, some 1, {-9}, {-12, 13}),
    /- qHu = 6, and Q10 = {3} -/
    (some (-14), some 6, {-4}, {3}), (some (-14), some 6, {1}, {3}),
    (some (-14), some 6, {11}, {3}), (some (-4), some 6, {-14}, {3}),
    (some (-4), some 6, {1}, {3}), (some (-4), some 6, {11}, {3}),
    (some 1, some 6, {-14}, {3}), (some 1, some 6, {-4}, {3}),
    (some 11, some 6, {-14}, {3}), (some 11, some 6, {-4}, {3}),
    /- qHu = 6, and Q10 = {-7, 13} -/
    (some (-9), some 6, {-4}, {-7, 13}), (some (-4), some 6, {-9}, {-7, 13}),
    (some (-4), some 6, {11}, {-7, 13}), (some 11, some 6, {-4}, {-7, 13})}
  | nextToNearestNeighbor => {
    /- qHu = -8, and Q10 = {-4} -/
    (some (-13), some (-8), {7}, {-4}), (some (-3), some (-8), {7}, {-4}),
    (some 2, some (-8), {-13}, {-4}), (some 2, some (-8), {-3}, {-4}),
    (some 2, some (-8), {7}, {-4}), (some 7, some (-8), {-13}, {-4}),
    (some 7, some (-8), {-3}, {-4}),
    /- qHu = 2, and Q10 = {1} -/
    (some (-13), some 2, {-8}, {1}), (some (-13), some 2, {7}, {1}),
    (some (-13), some 2, {12}, {1}), (some (-8), some 2, {-13}, {1}),
    (some (-8), some 2, {7}, {1}), (some 7, some 2, {-13}, {1}), (some 7, some 2, {-8}, {1}),
    (some 7, some 2, {12}, {1}), (some 12, some 2, {-13}, {1}), (some 12, some 2, {7}, {1}),
    /- qHu = 2, and Q10 = {-9, 11} -/
    (some (-8), some 2, {-3}, {-9, 11}), (some (-3), some 2, {-8}, {-9, 11}),
    (some (-3), some 2, {12}, {-9, 11}), (some 12, some 2, {-3}, {-9, 11}),
    /- qHu = 12, and Q10 = {6} -/
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
  cases I <;> decide +kernel

lemma viableCompletions_isPhenoConstrained (I : CodimensionOneConfig) :
    ∀ x ∈ viableCompletions I, ¬ IsPhenoConstrained x := by
  cases I <;> decide +kernel

lemma viableCompletions_yukawaGeneratesDangerousAtLevel_one (I : CodimensionOneConfig) :
    ∀ x ∈ viableCompletions I, ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  cases I <;> decide +kernel

lemma containsPhenoCompletionsOfMinimallyAllows_viableCompletions :
    (I : CodimensionOneConfig) →
    ContainsPhenoCompletionsOfMinimallyAllows I.allowedBarFiveCharges
      I.allowedTenCharges (viableCompletions I) := by
  decide +kernel

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
  aux : Multiset (Charges ℤ) → Multiset (Charges ℤ) → Multiset (Charges ℤ) :=
    fun all add =>
      if add = ∅ then all else
      let s := add.bind fun x =>
        (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val
      let s2 := s.filter fun y => y ∉ all ∧
        ¬ IsPhenoConstrained y ∧ ¬ YukawaGeneratesDangerousAtLevel y 1
      aux (all + s2) s2

/-- The charges in addition to `viableCompletions` which which permit a top Yukawa coupling,
  are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  These can be found with e.g.
  #eval (viableChargesExt .nextToNearestNeighbor).toFinset \
    (viableCompletions .nextToNearestNeighbor).toFinset
-/
def viableChargesAdditional : CodimensionOneConfig → Multiset (Charges ℤ)
  | .same =>
    {(some 1, some (-3), {-1, 2}, {-3, 0}), (some 2, some (-3), {-2, 1}, {-3, 0}),
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
  | .nearestNeighbor =>
      {(some (-9), some (-14), {-4}, {13, -7}), (some (-9), some (-14), {-4, 6}, {-7}),
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
  | .nextToNearestNeighbor =>
      {(some (-13), some 2, {-8, 12}, {1}), (some (-8), some 2, {-13, 7}, {1}),
      (some 7, some 2, {-8, 12}, {1}), (some 12, some 2, {-13, 7}, {1}),
      (some (-3), some 2, {-8, 12}, {-9, 11}), (some (-13), some 12, {-8}, {-9, 6}),
      (some (-13), some 12, {-8, 7}, {6}), (some (-13), some 12, {7}, {-4, 6}),
      (some (-8), some 12, {-13}, {-9, 6}), (some (-8), some 12, {-13, 2}, {6}),
      (some (-8), some 12, {2, 7}, {6}), (some 2, some 12, {-13, -8}, {6}),
      (some 2, some 12, {-8, 7}, {6}), (some 7, some 12, {-13, 2}, {6})}

lemma viableChargesAdditional_nodup (I : CodimensionOneConfig) :
    (viableChargesAdditional I).Nodup := by
  cases I <;> decide +kernel

lemma not_isPhenoConstrained_of_mem_viableChargesAdditional (I : CodimensionOneConfig) :
    ∀ x ∈ (viableChargesAdditional I), ¬ IsPhenoConstrained x := by
  cases I <;> decide +kernel

lemma yukawaGeneratesDangerousAtLevel_one_of_mem_viableChargesAdditional
    (I : CodimensionOneConfig) :
    ∀ x ∈ (viableChargesAdditional I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  cases I <;> decide +kernel

lemma viableCompletions_disjiont_viableChargesAdditional (I : CodimensionOneConfig) :
    Disjoint (viableCompletions I) (viableChargesAdditional I) := by
  refine Multiset.inter_eq_zero_iff_disjoint.mp ?_
  cases I
  <;> decide +kernel

/-- All charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  These trees can be found with e.g.
  `#eval viableChargesExt nextToNearestNeighbor`. -/
def viableCharges (I : CodimensionOneConfig) : Multiset (Charges ℤ) :=
  viableCompletions I + viableChargesAdditional I

/-!

## Basic properties

-/

lemma viableCharges_nodup (I : CodimensionOneConfig) :
    (viableCharges I).Nodup := (Multiset.Nodup.add_iff (viableCompletions_nodup I)
    (viableChargesAdditional_nodup I)).mpr (viableCompletions_disjiont_viableChargesAdditional I)

lemma viableCharges_card (I : CodimensionOneConfig) :
    (viableCharges I).card =
    if I = .same then 102 else
    if I = .nearestNeighbor then 71 else 51 := by
  decide +revert

lemma isComplete_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), IsComplete x := by
  revert I
  decide

lemma allowsTerm_topYukawa_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.AllowsTerm topYukawa := by
  revert I
  decide

lemma not_isPhenoConstrained_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ IsPhenoConstrained x := by
  rw [viableCharges]
  intro x hs
  simp at hs
  rcases hs with hs | hs
  · exact viableCompletions_isPhenoConstrained I x hs
  · exact not_isPhenoConstrained_of_mem_viableChargesAdditional I x hs

lemma not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges
    (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  rw [viableCharges]
  intro x hs
  simp at hs
  rcases hs with hs | hs
  · exact viableCompletions_yukawaGeneratesDangerousAtLevel_one I x hs
  · exact yukawaGeneratesDangerousAtLevel_one_of_mem_viableChargesAdditional I x hs

lemma card_five_bar_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.2.2.1.card ≤ 2 := by
  revert I
  decide

lemma card_ten_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.2.2.2.card ≤ 2 := by
  revert I
  decide

/-!

## Closed under inserting charges

We now show that adding a Q5 or a Q10 charge to an element of `viableCharges I` leads to a
charge which is either not phenomenologically constrained, or does not regenerate dangerous
couplings, or is already in `viableCharges I`.

-/

/-- Inserting a `q5` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenolically constrained or regenerates dangourous couplings
  with the Yukawas. -/
lemma isPhenoClosedQ5_viableCharges : (I : CodimensionOneConfig) →
    IsPhenoClosedQ5 I.allowedBarFiveCharges (viableCharges I) := by
  intro I
  apply isPhenClosedQ5_of_isPhenoConstrainedQ5
  revert I
  decide +kernel

/-- Inserting a `q10` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenolically constrained or regenerates dangourous couplings
  with the Yukawas. -/
lemma isPhenoClosedQ10_viableCharges : (I : CodimensionOneConfig) →
    IsPhenoClosedQ10 I.allowedTenCharges (viableCharges I) := by
  intro I
  apply isPhenClosedQ10_of_isPhenoConstrainedQ10
  revert I
  decide +kernel

/-!

## Proof of completeness.

-/

lemma viableCompletions_subset_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCompletions I), x ∈ viableCharges I := by
  rw [viableCharges]
  intro x hx
  simp only [Multiset.mem_add]
  left
  exact hx

lemma mem_viableCharges_iff {I} {x : Charges}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    x ∈ viableCharges I ↔ AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x :=
  completeness_of_isPhenoClosedQ5_isPhenoClosedQ10
    (allowsTerm_topYukawa_of_mem_viableCharges I)
    (not_isPhenoConstrained_of_mem_viableCharges I)
    (not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges I)
    (isComplete_of_mem_viableCharges I)
    (isPhenoClosedQ5_viableCharges I)
    (isPhenoClosedQ10_viableCharges I)
    (containsPhenoCompletionsOfMinimallyAllows_of_subset
      (containsPhenoCompletionsOfMinimallyAllows_viableCompletions I)
      (viableCompletions_subset_viableCharges I))
    hsub

end Charges

end SU5

end FTheory
