/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.AnomalyCancellation.Tree
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Completeness
/-!

# Viable Quanta

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
def IsViable (I : CodimensionOneConfig) (x : Quanta) : Prop :=
  x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
  AllowsTerm x.toCharges topYukawa ∧
  x.2.2.1.toFluxesFive.NoExotics ∧
  x.2.2.1.toFluxesFive.HasNoZero ∧
  x.2.2.2.toFluxesTen.NoExotics ∧
  x.2.2.2.toFluxesTen.HasNoZero ∧
  AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
  x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges ∧
  x.2.2.1.toCharges.Nodup ∧
  x.2.2.2.toCharges.Nodup

lemma isViable_iff_expand_ofFinset (I : CodimensionOneConfig) (x : Quanta) :
    IsViable I x ↔
      x.toCharges.IsComplete ∧
  ¬ x.toCharges.IsPhenoConstrained ∧
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
  rw [IsViable, Charges.mem_ofFinset_iff]
  simp [toCharges]

instance (I : CodimensionOneConfig) (x : Quanta) : Decidable (IsViable I x) :=
  decidable_of_iff _ (isViable_iff_expand_ofFinset I x).symm

lemma toCharges_five_nodup_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.1.toCharges.Nodup := by
  exact h.2.2.2.2.2.2.2.2.2.1

lemma toCharges_ten_nodup_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.2.toCharges.Nodup := by
  exact h.2.2.2.2.2.2.2.2.2.2

lemma toCharges_mem_ofFinset_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges := by
  exact h.2.2.2.2.2.2.2.2.1

lemma toFluxesFive_noExotics_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.1.toFluxesFive.NoExotics := by
  exact h.2.2.2.1

lemma toFluxesTen_noExotics_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.2.toFluxesTen.NoExotics := by
  exact h.2.2.2.2.2.1

lemma toFluxesFive_hasNoZero_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.1.toFluxesFive.HasNoZero := by
  exact h.2.2.2.2.1

lemma toFluxesTen_hasNoZero_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.2.toFluxesTen.HasNoZero := by
  exact h.2.2.2.2.2.2.1

lemma Q10_charges_mem_allowedBarTenCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    ∀ s ∈ x.2.2.2.toCharges, s ∈ I.allowedTenCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViable I x h
  rw [Charges.mem_ofFinset_iff] at h1
  have h2 := h1.2.2.2
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma Q5_charges_mem_allowedBarFiveCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    ∀ s ∈ x.2.2.1.toCharges, s ∈ I.allowedBarFiveCharges := by
  have h1 := toCharges_mem_ofFinset_of_isViable I x h
  rw [Charges.mem_ofFinset_iff] at h1
  have h2 := h1.2.2.1
  intro y hy
  apply h2
  simp [toCharges]
  exact hy

lemma fiveQuanta_mem_ofCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.1 ∈ FiveQuanta.ofCharges I x.2.2.1.toCharges := by
  rw [FiveQuanta.mem_ofCharges_iff]
  · simp
    constructor
    · exact toFluxesFive_noExotics_of_isViable I x h
    · exact toFluxesFive_hasNoZero_of_isViable I x h
  · exact fun s a => Q5_charges_mem_allowedBarFiveCharges_of_isViable I x h s a

lemma tenQuanta_mem_ofCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.2.2.2 ∈ TenQuanta.ofCharges I x.2.2.2.toCharges := by
  rw [TenQuanta.mem_ofCharges_iff]
  · simp
    constructor
    · exact toFluxesTen_noExotics_of_isViable I x h
    · exact toFluxesTen_hasNoZero_of_isViable I x h
  · exact fun s a => Q10_charges_mem_allowedBarTenCharges_of_isViable I x h s a

lemma topYukawa_allowsTerm_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    AllowsTerm x.toCharges topYukawa := by
  exact h.2.2.1

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
    AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  exact h.2.2.2.2.2.2.2.1
/-!

## toCharges mem

-/

lemma toCharges_mem_nonPhenoConstrainedCharges_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ nonPhenoConstrainedCharges I := by
  rw [← not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge]
  · constructor
    · exact topYukawa_allowsTerm_of_isViable I x h
    constructor
    · exact not_isPhenoConstrained_of_isViable I x h
    · exact toCharges_isComplete_of_isViable I x h
  · exact toCharges_mem_ofFinset_of_isViable I x h

lemma toCharges_mem_nonPhenoConstrainedCharges_filterAnomalyCancellation_of_isViable
    (I : CodimensionOneConfig) (x : Quanta) (h : IsViable I x) :
    x.toCharges ∈ Charges.Tree.filterAnomalyCancellation I (nonPhenoConstrainedCharges I) := by
  rw [Tree.mem_filterAnomalyCancellation_iff]
  constructor
  · exact toCharges_mem_nonPhenoConstrainedCharges_of_isViable I x h
  use x.2.2.1, x.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · simp [toCharges]
    have h1 : FiveQuanta.ofCharges I x.2.2.1.toCharges.dedup =
        FiveQuanta.ofCharges I x.2.2.1.toCharges := by
      congr
      refine Multiset.Nodup.dedup ?_
      exact toCharges_five_nodup_of_isViable I x h
    rw [h1]
    exact fiveQuanta_mem_ofCharges_of_isViable I x h
  · simp [toCharges]
    have h1 : TenQuanta.ofCharges I x.2.2.2.toCharges.dedup =
        TenQuanta.ofCharges I x.2.2.2.toCharges := by
      congr
      refine Multiset.Nodup.dedup ?_
      exact toCharges_ten_nodup_of_isViable I x h
    rw [h1]
    exact tenQuanta_mem_ofCharges_of_isViable I x h
  · exact anomalyCancellation_of_isViable I x h

lemma mem_ofCharges_self_of_isViable (I : CodimensionOneConfig) (𝓠 : Quanta)
    (h : IsViable I 𝓠) :
    𝓠 ∈ ofCharges I 𝓠.toCharges := by
  simp [ofCharges]
  use 𝓠.2.2.1, 𝓠.2.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [toCharges]
    have h1 : FiveQuanta.ofCharges I 𝓠.2.2.1.toCharges.dedup =
        FiveQuanta.ofCharges I 𝓠.2.2.1.toCharges := by
      congr
      refine Multiset.Nodup.dedup ?_
      exact toCharges_five_nodup_of_isViable I 𝓠 h
    rw [h1]
    apply FiveQuanta.mem_ofCharges_self
    exact toFluxesFive_noExotics_of_isViable I 𝓠 h
    exact toFluxesFive_hasNoZero_of_isViable I 𝓠 h
    exact fun s a => Q5_charges_mem_allowedBarFiveCharges_of_isViable I 𝓠 h s a
  · simp [toCharges]
    have h1 : TenQuanta.ofCharges I 𝓠.2.2.2.toCharges.dedup =
        TenQuanta.ofCharges I 𝓠.2.2.2.toCharges := by
      congr
      refine Multiset.Nodup.dedup ?_
      exact toCharges_ten_nodup_of_isViable I 𝓠 h
    rw [h1]
    apply TenQuanta.mem_ofCharges_self
    exact toFluxesTen_noExotics_of_isViable I 𝓠 h
    exact toFluxesTen_hasNoZero_of_isViable I 𝓠 h
    exact fun s a => Q10_charges_mem_allowedBarTenCharges_of_isViable I 𝓠 h s a
  · simp [toCharges]

end Quanta

end SU5U1

end FTheory
