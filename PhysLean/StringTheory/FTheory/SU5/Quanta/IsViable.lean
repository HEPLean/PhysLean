/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Charges.AnomalyFree
/-!

# Viable Quanta with Yukawa

## i. Overview

We say a term of a type `Quanta` is viable
  if it satisfies the following properties:
- It has a `Hd`, `Hu` and at leat one matter particle in the 5 and 10 representation.
- It has no exotic chiral particles.
- It leads to a top Yukawa coupling.
- It does not lead to a pheno constraining terms.
- It does not lead to a dangerous Yukawa coupling at one insertion of the Yukawa singlets.
- It satisfies anomaly cancellation.
- The charges are allowed by an `I` configuration.

This somes with one caveat, the `IsViable` constraint enforces the anomaly
  cancellation condition:
`∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0`
to hold, which is not always necessary, see arXiv:1401.5084.

We also write down the explicit set of viable quanta, and prove that this set is complete.

## ii. Key results

- `Quanta.IsViable` : The proposition on a `Quanta` that it is viable.
- `Quanta.viableElems` : The multiset of viable quanta.
- `Quanta.isViable_iff_mem_viableElems` : A quanta is viable if and only if it is in the
  `Quanta.viableElems`.

## iii. Table of contents

- A. The condition for a `Quanta` to be viable
  - A.1. Simplification of the prop to use the set of viable charges `viableCharges I`
  - A.2. Further simplification of the prop to use the set of viable charges `Quanta.liftCharge`
  - A.3. Further simplification of the prop to use the anomaly free set of viable charges
- B. The multiset of viable quanta
  - B.1. Every element of the multiset is viable
  - B.2. A quanta is viable if and only if it is in the multiset
  - B.3. Every element of the multiset regenerates Yukawa at two insertions of the Yukawa singlets

## iv. References

The key reference for the material in this module is: arXiv:1507.05961.

-/
namespace FTheory

namespace SU5

variable {I : CodimensionOneConfig}

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm ChargeSpectrum

/-!

## A. The condition for a `Quanta` to be viable

-/

/-- For a given `I : CodimensionOneConfig` the condition on a `Quanta` for it to be
  phenomenologically viable. -/
def IsViable (x : Quanta) : Prop :=
  /- 1. Conditions just on the charges. -/
  x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
  (∃ I : CodimensionOneConfig, x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) ∧
  x.F.toCharges.Nodup ∧
  x.T.toCharges.Nodup ∧
  AllowsTerm x.toCharges topYukawa ∧
  /- 2. Conditions just on the fluxes. -/
  x.F.toFluxesFive.NoExotics ∧
  x.F.toFluxesFive.HasNoZero ∧
  x.T.toFluxesTen.NoExotics ∧
  x.T.toFluxesTen.HasNoZero ∧
  /- 3. Conditions on the combination of the charges on the flux. -/
  AnomalyCancellation x.qHd x.qHu x.F x.T

/-!

### A.1. Simplification of the prop to use the set of viable charges `viableCharges I`

-/

lemma isViable_iff_charges_mem_viableCharges (x : Quanta) :
    IsViable x ↔
        /- 1. Conditions just on the charges. -/
        (∃ I, x.toCharges ∈ viableCharges I) ∧
        x.F.toCharges.Nodup ∧
        x.T.toCharges.Nodup ∧
        /- 2. Conditions just on the fluxes -/
        x.F.toFluxesFive.NoExotics ∧
        x.F.toFluxesFive.HasNoZero ∧
        x.T.toFluxesTen.NoExotics ∧
        x.T.toFluxesTen.HasNoZero ∧
        /- 3. Conditions on the fluxes and the charges. -/
        AnomalyCancellation x.qHd x.qHu x.F x.T := by
  rw [IsViable]
  conv_rhs =>
    enter [1, 1, I]
    rw [mem_viableCharges_iff']
  aesop

/-!

### A.2. Further simplification of the prop to use the set of viable charges `Quanta.liftCharge`

-/

lemma isViable_iff_charges_mem_viableCharges_mem_liftCharges (x : Quanta) :
    IsViable x ↔ (∃ I, x.toCharges ∈ viableCharges I) ∧
      x ∈ Quanta.liftCharge x.toCharges ∧
      AnomalyCancellation x.qHd x.qHu x.F x.T := by
  rw [Quanta.mem_liftCharge_iff]
  simp [toCharges_qHd, toCharges_qHu]
  rw [FiveQuanta.mem_liftCharge_iff, TenQuanta.mem_liftCharge_iff]
  rw [isViable_iff_charges_mem_viableCharges, ← FluxesFive.noExotics_iff_mem_elemsNoExotics,
    ← FluxesTen.noExotics_iff_mem_elemsNoExotics]
  aesop

/-!

### A.3. Further simplification of the prop to use the anomaly free set of viable charges

-/

lemma isViable_iff_filter (x : Quanta) :
    IsViable x ↔ (∃ I, x.toCharges ∈ (viableCharges I).filter IsAnomalyFree) ∧
      x ∈ Quanta.liftCharge x.toCharges
      ∧ AnomalyCancellation x.qHd x.qHu x.F x.T := by
  rw [isViable_iff_charges_mem_viableCharges_mem_liftCharges]
  simp [IsAnomalyFree]
  aesop

/-!

## B. The multiset of viable quanta

-/

/-- Given a `CodimensionOneConfig` the `Quanta` which statisfy the condition `IsViable`. -/
def viableElems : Multiset Quanta :=
  {⟨some 2, some (-2), {(-1, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
    ⟨some 2, some (-2), {(-1, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
    ⟨some (-2), some 2, {(-1, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
    ⟨some (-2), some 2, {(-1, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
    ⟨some 6, some (-14), {(-9, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
    ⟨some 6, some (-14), {(-9, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩}

/-!

### B.1. Every element of the multiset is viable

-/

lemma isViable_of_mem_viableElems (x : Quanta) (h : x ∈ viableElems) :
    IsViable x := by
  rw [isViable_iff_charges_mem_viableCharges_mem_liftCharges]
  revert x
  decide

/-!

### B.2. A quanta is viable if and only if it is in the multiset

-/
lemma isViable_iff_mem_viableElems (x : Quanta) :
    x.IsViable ↔ x ∈ viableElems := by
  constructor
  · intro h
    rw [isViable_iff_filter] at h
    obtain ⟨⟨I, hc⟩, hl, ha⟩ := h
    generalize x.toCharges = c at *
    revert ha
    revert x
    rw [viable_anomalyFree] at hc
    revert c
    revert I
    decide
  · exact isViable_of_mem_viableElems x

/-!

### B.3. Every element of the multiset regenerates Yukawa at two insertions of the Yukawa singlets

-/

/-- Every viable Quanta regenerates a dangerous coupling at two insertions of the Yukawa
  singlets. -/
lemma yukawaSingletsRegenerateDangerousInsertion_two_of_isViable
    (x : Quanta) (h : IsViable x) :
    (toCharges x).YukawaGeneratesDangerousAtLevel 2 := by
  rw [isViable_iff_mem_viableElems] at h
  revert x
  decide

end Quanta

end SU5

end FTheory
