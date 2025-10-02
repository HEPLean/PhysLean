/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Charges.AnomalyFree
/-!

# Viable Quanta with Yukawa

We say a term of a type `Quanta` is viable for a given `I : CodimensionOneConfig`,
  if it satisfies the following properties:
- It has a `Hd`, `Hu` and at leat one matter particle in the 5 and 10 representation.
- It has no exotic chiral particles.
- It leads to a top Yukawa coupling.
- It does not lead to a pheno constraining terms.
- It does not lead to a dangerous Yukawa coupling at one insertion of the Yukawa singlets.
- It satisfies anomaly cancellation.
- The charges are allowed by the `I` configuration.

This somes with one caveat, the `IsViable` constraint enforces the anomaly
  cancellation condition:
`∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0`
to hold, which is not always necessary, see arXiv:1401.5084.

-/
namespace FTheory

namespace SU5

variable {I : CodimensionOneConfig}

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm ChargeSpectrum

/-- For a given `I : CodimensionOneConfig` the condition on a `Quanta` for it to be
  phenomenologically viable. -/
def IsViable (I : CodimensionOneConfig) (x : Quanta) : Prop :=
  x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
  AllowsTerm x.toCharges topYukawa ∧
  x.F.toFluxesFive.NoExotics ∧
  x.F.toFluxesFive.HasNoZero ∧
  x.T.toFluxesTen.NoExotics ∧
  x.T.toFluxesTen.HasNoZero ∧
  AnomalyCancellation x.qHd x.qHu x.F x.T ∧
  x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges ∧
  x.F.toCharges.Nodup ∧
  x.T.toCharges.Nodup

lemma isViable_iff_expand_ofFinset (I : CodimensionOneConfig) (x : Quanta) :
    IsViable I x ↔
      x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
  AllowsTerm x.toCharges topYukawa ∧
  x.F.toFluxesFive.NoExotics ∧
  x.F.toFluxesFive.HasNoZero ∧
  x.T.toFluxesTen.NoExotics ∧
  x.T.toFluxesTen.HasNoZero ∧
  AnomalyCancellation x.qHd x.qHu x.F x.T ∧
  (x.qHd.toFinset ⊆ I.allowedBarFiveCharges ∧ x.qHu.toFinset ⊆ I.allowedBarFiveCharges ∧
      x.toCharges.Q5 ⊆ I.allowedBarFiveCharges ∧ x.toCharges.Q10 ⊆ I.allowedTenCharges)
      ∧
    x.F.toCharges.Nodup ∧
    x.T.toCharges.Nodup := by
  rw [IsViable, mem_ofFinset_iff]
  simp [toCharges]

instance (I : CodimensionOneConfig) (x : Quanta) : Decidable (IsViable I x) :=
  decidable_of_iff _ (isViable_iff_expand_ofFinset I x).symm

/-!

## Basic properties of charges satisfying `IsViable`

-/

lemma toCharges_five_nodup_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.F.toCharges.Nodup := h.2.2.2.2.2.2.2.2.2.2.1

lemma toCharges_ten_nodup_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.T.toCharges.Nodup := h.2.2.2.2.2.2.2.2.2.2.2

lemma toCharges_mem_ofFinset_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges :=
  h.2.2.2.2.2.2.2.2.2.1

lemma toFluxesFive_noExotics_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.F.toFluxesFive.NoExotics := h.2.2.2.2.1

lemma toFluxesTen_noExotics_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.T.toFluxesTen.NoExotics := h.2.2.2.2.2.2.1

lemma toFluxesFive_hasNoZero_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.F.toFluxesFive.HasNoZero := h.2.2.2.2.2.1

lemma toFluxesTen_hasNoZero_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.T.toFluxesTen.HasNoZero := h.2.2.2.2.2.2.2.1

lemma Q10_charges_mem_allowedBarTenCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    ∀ s ∈ x.T.toCharges, s ∈ I.allowedTenCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViable I x h
  rw [mem_ofFinset_iff] at h1
  have h2 := h1.2.2.2
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma Q5_charges_mem_allowedBarFiveCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    ∀ s ∈ x.F.toCharges, s ∈ I.allowedBarFiveCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViable I x h
  rw [mem_ofFinset_iff] at h1
  have h2 := h1.2.2.1
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma topYukawa_allowsTerm_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    AllowsTerm x.toCharges topYukawa := by
  exact h.2.2.2.1

lemma not_isPhenoConstrained_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    ¬ x.toCharges.IsPhenoConstrained := by
  exact h.2.1

lemma toCharges_isComplete_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges.IsComplete := by
  exact h.1

lemma anomalyCancellation_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    AnomalyCancellation x.qHd x.qHu x.F x.T := by
  exact h.2.2.2.2.2.2.2.2.1

lemma reduce_five_eq_self_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.F.reduce = x.F := by
  match x with
  | ⟨qHd, qHu, F, T⟩ =>
    simp only
    refine FiveQuanta.reduce_eq_self_of_ofCharges_nodup F ?_
    simp [IsViable] at h
    simp_all

lemma reduce_ten_eq_self_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.T.reduce = x.T := by
  match x with
  | ⟨qHd, qHu, F, T⟩ =>
    simp only
    refine TenQuanta.reduce_eq_self_of_ofCharges_nodup T ?_
    simp [IsViable] at h
    simp_all

lemma reduce_eq_self_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.reduce = x := by
  match x with
  | ⟨qHd, qHu, F, T⟩ =>
    simp [reduce]
    constructor
    · exact reduce_five_eq_self_of_isViable I _ h
    · exact reduce_ten_eq_self_of_isViable I _ h

lemma mem_ofChargesExpand_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x ∈ (ofChargesExpand x.toCharges).map reduce := by
  simp [ofChargesExpand]
  have h_five : x.F ∈ (FiveQuanta.ofChargesExpand x.F.toCharges.toFinset).map
      FiveQuanta.reduce := by
    refine (FiveQuanta.mem_ofChargesExpand_map_reduce_iff x.F.toCharges.toFinset x.F).mpr ?_
    · refine ⟨?_, rfl, ?_⟩
      · rw [← SU5.FluxesFive.noExotics_iff_mem_elemsNoExotics]
        refine ⟨?_, ?_⟩
        · exact toFluxesFive_noExotics_of_isViable I x h
        · exact toFluxesFive_hasNoZero_of_isViable I x h
      · exact reduce_five_eq_self_of_isViable I x h
  have h_ten : x.T ∈ (TenQuanta.ofChargesExpand x.T.toCharges.toFinset).map
      TenQuanta.reduce := by
    refine (TenQuanta.mem_ofChargesExpand_map_reduce_iff x.T.toCharges.toFinset x.T).mpr ?_
    · refine ⟨?_, rfl, ?_⟩
      · rw [← SU5.FluxesTen.noExotics_iff_mem_elemsNoExotics]
        refine ⟨?_, ?_⟩
        · exact toFluxesTen_noExotics_of_isViable I x h
        · exact toFluxesTen_hasNoZero_of_isViable I x h
      · exact reduce_ten_eq_self_of_isViable I x h
  rw [Multiset.mem_map] at h_five h_ten
  obtain ⟨F, F_mem, hF⟩ := h_five
  obtain ⟨T, T_mem, hT⟩ := h_ten
  refine ⟨F, ⟨F_mem, ⟨T, ⟨T_mem, ?_⟩⟩⟩⟩
  simp_all [reduce, toCharges]

lemma toCharges_isAnomalyFree_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    IsAnomalyFree x.toCharges := by
  simp only [IsAnomalyFree]
  have h1 := mem_ofChargesExpand_of_isViable I x h
  rw [Multiset.mem_map] at h1
  obtain ⟨y, y_mem, rfl⟩ := h1
  use y
  refine ⟨?_, ?_⟩
  · exact y_mem
  · have acc := anomalyCancellation_of_isViable I _ h
    simp only [AnomalyCancellation, reduce] at acc
    rw [FiveQuanta.anomalyCoefficent_of_reduce, TenQuanta.anomalyCoefficent_of_reduce] at acc
    simp [AnomalyCancellation]
    rw [← acc]

lemma toCharges_mem_viableCharges_filter_isAnomalyFree_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ (viableCharges I).filter IsAnomalyFree := by
  simp only [Multiset.mem_filter]
  apply And.intro
  · refine (mem_viableCharges_iff ?_).mpr ⟨?_, ?_, ?_, ?_⟩
    · exact toCharges_mem_ofFinset_of_isViable I x h
    · exact topYukawa_allowsTerm_of_isViable I x h
    · exact not_isPhenoConstrained_of_isViable I x h
    · exact h.2.2.1
    · exact toCharges_isComplete_of_isViable I x h
  · exact toCharges_isAnomalyFree_of_isViable I x h

/-!

## viableElems
-/

/-- Given a `CodimensionOneConfig` the `Quanta` which statisfy the condition `IsViable`. -/
def viableElems : CodimensionOneConfig → Multiset Quanta
  | .same => {⟨some 2, some (-2), {(-1, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
      ⟨some 2, some (-2), {(-1, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
      ⟨some (-2), some 2, {(-1, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
      ⟨some (-2), some 2, {(-1, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩}
  | .nearestNeighbor => {⟨some 6, some (-14), {(-9, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
    ⟨some 6, some (-14), {(-9, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩}
  | .nextToNearestNeighbor => {}

lemma isViable_of_mem_viableElems
    (I : CodimensionOneConfig) (x : Quanta) (h : x ∈ viableElems I) :
    IsViable I x := by
  revert x I
  decide

lemma viableElems_card_eq (I : CodimensionOneConfig) :
    (viableElems I).card = match I with
    | .same => 4
    | .nearestNeighbor => 2
    | .nextToNearestNeighbor => 0 := by
  cases I <;> rfl

lemma mem_viableElems_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x ∈ viableElems I := by
  have hx := mem_ofChargesExpand_of_isViable I x h
  have hc := toCharges_mem_viableCharges_filter_isAnomalyFree_of_isViable I x h
  rw [viable_anomalyFree] at hc
  generalize x.toCharges = c at hc hx
  fin_cases I
  all_goals
  · dsimp at hc
    fin_cases hc
    all_goals
    · revert h
      revert x
      decide

lemma isViable_iff_mem_viableElems
    (I : CodimensionOneConfig) (x : Quanta) :
    IsViable I x ↔ x ∈ viableElems I := by
  constructor
  · exact mem_viableElems_of_isViable I x
  · exact isViable_of_mem_viableElems I x

/-- Every viable Quanta regenerates a dangerous coupling at two insertions of the Yukawa
  singlets. -/
lemma yukawaSingletsRegenerateDangerousInsertion_two_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    (toCharges x).YukawaGeneratesDangerousAtLevel 2 := by
  rw [isViable_iff_mem_viableElems] at h
  revert I x
  decide

end Quanta

end SU5

end FTheory
