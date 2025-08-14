/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.AnomalyCancellation
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Completeness
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Viable
import PhysLean.StringTheory.FTheory.SU5U1.Charges.AnomalyFree
/-!

# Viable Quanta with Yukawa

We say a term of a type `Quanta` is viable for a given `I : CodimensionOneConfig`,
  if it satisfies the following properties:
- It has a `Hd`, `Hu` and at leat one matter particle in the 5 and 10 representation.
- It has no exotic chiral particles.
- It leads to a top Yukawa coupling.
- It does not lead to a pheno constraining terms.
- It satisfies anomaly cancellation.
- The charges are allowed by the `I` configuration.

This somes with one caveat, the `IsViable` constraint enforces the anomaly cancellation condition:
`∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0`
to hold, which is not always necessary, see arXiv:1401.5084.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm Charges

/-- For a given `I : CodimensionOneConfig` the condition on a `Quanta` for it to be
  phenomenologically viable. -/
def IsViableYukawa (I : CodimensionOneConfig) (x : Quanta) : Prop :=
  x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
  AllowsTerm x.toCharges topYukawa ∧
  x.2.2.1.toFluxesFive.NoExotics ∧
  x.2.2.1.toFluxesFive.HasNoZero ∧
  x.2.2.2.toFluxesTen.NoExotics ∧
  x.2.2.2.toFluxesTen.HasNoZero ∧
  AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
  x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges ∧
  x.2.2.1.toCharges.Nodup ∧
  x.2.2.2.toCharges.Nodup

lemma isViableYukawa_iff_expand_ofFinset (I : CodimensionOneConfig) (x : Quanta) :
    IsViableYukawa I x ↔
      x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
  AllowsTerm x.toCharges topYukawa ∧
  x.2.2.1.toFluxesFive.NoExotics ∧
  x.2.2.1.toFluxesFive.HasNoZero ∧
  x.2.2.2.toFluxesTen.NoExotics ∧
  x.2.2.2.toFluxesTen.HasNoZero ∧
  AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
  (x.1.toFinset ⊆ I.allowedBarFiveCharges ∧ x.2.1.toFinset ⊆ I.allowedBarFiveCharges ∧
      x.toCharges.2.2.1 ⊆ I.allowedBarFiveCharges ∧ x.toCharges.2.2.2 ⊆ I.allowedTenCharges)
      ∧
    x.2.2.1.toCharges.Nodup ∧
    x.2.2.2.toCharges.Nodup := by
  rw [IsViableYukawa, Charges.mem_ofFinset_iff]
  simp [toCharges]

instance (I : CodimensionOneConfig) (x : Quanta) : Decidable (IsViableYukawa I x) :=
  decidable_of_iff _ (isViableYukawa_iff_expand_ofFinset I x).symm

/-!

## Basic properties of charges satisfying `IsViableYukawa`

-/

lemma toCharges_five_nodup_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.1.toCharges.Nodup := h.2.2.2.2.2.2.2.2.2.2.1

lemma toCharges_ten_nodup_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.2.toCharges.Nodup := h.2.2.2.2.2.2.2.2.2.2.2

lemma toCharges_mem_ofFinset_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges :=
  h.2.2.2.2.2.2.2.2.2.1

lemma toFluxesFive_noExotics_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.1.toFluxesFive.NoExotics := h.2.2.2.2.1

lemma toFluxesTen_noExotics_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.2.toFluxesTen.NoExotics := h.2.2.2.2.2.2.1

lemma toFluxesFive_hasNoZero_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.1.toFluxesFive.HasNoZero := h.2.2.2.2.2.1

lemma toFluxesTen_hasNoZero_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.2.toFluxesTen.HasNoZero := h.2.2.2.2.2.2.2.1

lemma Q10_charges_mem_allowedBarTenCharges_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    ∀ s ∈ x.2.2.2.toCharges, s ∈ I.allowedTenCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViableYukawa I x h
  rw [Charges.mem_ofFinset_iff] at h1
  have h2 := h1.2.2.2
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma Q5_charges_mem_allowedBarFiveCharges_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    ∀ s ∈ x.2.2.1.toCharges, s ∈ I.allowedBarFiveCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViableYukawa I x h
  rw [Charges.mem_ofFinset_iff] at h1
  have h2 := h1.2.2.1
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma fiveQuanta_mem_ofCharges_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.1 ∈ FiveQuanta.ofCharges I x.2.2.1.toCharges := by
  rw [FiveQuanta.mem_ofCharges_iff]
  · simp
    constructor
    · exact toFluxesFive_noExotics_of_isViableYukawa I x h
    · exact toFluxesFive_hasNoZero_of_isViableYukawa I x h
  · exact fun s a => Q5_charges_mem_allowedBarFiveCharges_of_isViableYukawa I x h s a

lemma tenQuanta_mem_ofCharges_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.2 ∈ TenQuanta.ofCharges I x.2.2.2.toCharges := by
  rw [TenQuanta.mem_ofCharges_iff]
  · simp
    constructor
    · exact toFluxesTen_noExotics_of_isViableYukawa I x h
    · exact toFluxesTen_hasNoZero_of_isViableYukawa I x h
  · exact fun s a => Q10_charges_mem_allowedBarTenCharges_of_isViableYukawa I x h s a

lemma topYukawa_allowsTerm_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    AllowsTerm x.toCharges topYukawa := by
  exact h.2.2.2.1

lemma not_isPhenoConstrained_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    ¬ x.toCharges.IsPhenoConstrained := by
  exact h.2.1

lemma toCharges_isComplete_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.toCharges.IsComplete := by
  exact h.1

lemma anomalyCancellation_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  exact h.2.2.2.2.2.2.2.2.1

lemma reduce_five_eq_self_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.1.reduce = x.2.2.1 := by
  match x with
  | (qHd, qHu, F, T) =>
    simp [reduce]
    refine FiveQuanta.reduce_eq_self_of_ofCharges_nodup F ?_
    simp [IsViableYukawa] at h
    simp_all

lemma reduce_ten_eq_self_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.2.2.2.reduce = x.2.2.2 := by
  match x with
  | (qHd, qHu, F, T) =>
    simp [reduce]
    refine TenQuanta.reduce_eq_self_of_ofCharges_nodup T ?_
    simp [IsViableYukawa] at h
    simp_all

lemma reduce_eq_self_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.reduce = x := by
  match x with
  | (qHd, qHu, F, T) =>
    simp [reduce]
    constructor
    · exact reduce_five_eq_self_of_isViableYukawa I _ h
    · exact reduce_ten_eq_self_of_isViableYukawa I _ h

lemma mem_ofChargesExpand_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x ∈ (ofChargesExpand x.toCharges).map reduce := by
  simp [ofChargesExpand]
  have h_five : x.2.2.1 ∈ (FiveQuanta.ofChargesExpand x.2.2.1.toCharges.toFinset).map
      FiveQuanta.reduce := by
    refine (FiveQuanta.mem_ofChargesExpand_map_reduce_iff x.2.2.1.toCharges.toFinset x.2.2.1).mpr ?_
    · refine ⟨?_, rfl, ?_⟩
      · rw [← SU5.FluxesFive.noExotics_iff_mem_elemsNoExotics]
        refine ⟨?_, ?_⟩
        · exact toFluxesFive_noExotics_of_isViableYukawa I x h
        · exact toFluxesFive_hasNoZero_of_isViableYukawa I x h
      · exact reduce_five_eq_self_of_isViableYukawa I x h
  have h_ten : x.2.2.2 ∈ (TenQuanta.ofChargesExpand x.2.2.2.toCharges.toFinset).map
      TenQuanta.reduce := by
    refine (TenQuanta.mem_ofChargesExpand_map_reduce_iff x.2.2.2.toCharges.toFinset x.2.2.2).mpr ?_
    · refine ⟨?_, rfl, ?_⟩
      · rw [← SU5.FluxesTen.noExotics_iff_mem_elemsNoExotics]
        refine ⟨?_, ?_⟩
        · exact toFluxesTen_noExotics_of_isViableYukawa I x h
        · exact toFluxesTen_hasNoZero_of_isViableYukawa I x h
      · exact reduce_ten_eq_self_of_isViableYukawa I x h
  rw [Multiset.mem_map] at h_five h_ten
  obtain ⟨F, F_mem, hF⟩ := h_five
  obtain ⟨T, T_mem, hT⟩ := h_ten
  refine ⟨F, ⟨F_mem, ⟨T, ⟨T_mem, ?_⟩⟩⟩⟩
  simp_all [reduce, toCharges]

lemma toCharges_isAnomalyFree_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    IsAnomalyFree x.toCharges := by
  simp only [IsAnomalyFree]
  have h1 := mem_ofChargesExpand_of_isViableYukawa I x h
  rw [Multiset.mem_map] at h1
  obtain ⟨y, y_mem, rfl⟩ := h1
  use y
  refine ⟨?_, ?_⟩
  · exact y_mem
  · have acc := anomalyCancellation_of_isViableYukawa I _ h
    simp only [AnomalyCancellation, reduce] at acc
    rw [FiveQuanta.anomalyCoefficent_of_reduce, TenQuanta.anomalyCoefficent_of_reduce] at acc
    simp [AnomalyCancellation]
    rw [← acc]

lemma toCharges_mem_viableCharges_filter_isAnomalyFree_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x.toCharges ∈ (viableCharges I).filter IsAnomalyFree := by
  simp
  apply And.intro
  · refine (mem_viableCharges_iff ?_).mpr ⟨?_, ?_, ?_, ?_⟩
    · exact toCharges_mem_ofFinset_of_isViableYukawa I x h
    · exact topYukawa_allowsTerm_of_isViableYukawa I x h
    · exact not_isPhenoConstrained_of_isViableYukawa I x h
    · exact h.2.2.1
    · exact toCharges_isComplete_of_isViableYukawa I x h
  · exact toCharges_isAnomalyFree_of_isViableYukawa I x h

/-!

## viableYukawaElems
-/

def viableYukawaElems : CodimensionOneConfig → Multiset Quanta
  | .same => {(some 2, some (-2), {(-1, 1, 2), (1, 2, -2)}, {(-1, 3, 0)}),
      (some 2, some (-2), {(-1, 0, 2), (1, 3, -2)}, {(-1, 3, 0)}),
      (some (-2), some 2, {(-1, 2, -2), (1, 1, 2)}, {(1, 3, 0)}),
      (some (-2), some 2, {(-1, 3, -2), (1, 0, 2)}, {(1, 3, 0)})}
  | .nearestNeighbor => {(some 6, some (-14), {(-9, 1, 2), (1, 2, -2)}, {(-7, 3, 0)}),
    (some 6, some (-14), {(-9, 0, 2), (1, 3, -2)}, {(-7, 3, 0)})}
  | .nextToNearestNeighbor => {}

lemma isViableYukawa_of_mem_viableYukawaElems
    (I : CodimensionOneConfig) (x : Quanta) (h : x ∈ viableYukawaElems I) :
    IsViableYukawa I x := by
 revert x I
 decide


lemma viableYukawaElems_card_eq (I : CodimensionOneConfig) :
    (viableYukawaElems I).card = match I with
    | .same => 4
    | .nearestNeighbor => 2
    | .nextToNearestNeighbor => 0 := by
  cases I <;> rfl

lemma mem_viableYukawaElems_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    x ∈ viableYukawaElems I  := by
  have hx := mem_ofChargesExpand_of_isViableYukawa I x h
  have hc := toCharges_mem_viableCharges_filter_isAnomalyFree_of_isViableYukawa I x h
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

lemma isViableYukawa_iff_mem_viableYukawaElems
    (I : CodimensionOneConfig) (x : Quanta) :
    IsViableYukawa I x ↔ x ∈ viableYukawaElems I := by
  constructor
  · exact mem_viableYukawaElems_of_isViableYukawa I x
  · exact isViableYukawa_of_mem_viableYukawaElems I x

lemma yukawaSingletsRegenerateDangerousInsertion_two_of_isViableYukawa
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViableYukawa I x) :
    (toCharges x).YukawaGeneratesDangerousAtLevel 2 := by
  rw [isViableYukawa_iff_mem_viableYukawaElems] at h
  revert I x
  decide

end Quanta

end SU5U1

end FTheory
