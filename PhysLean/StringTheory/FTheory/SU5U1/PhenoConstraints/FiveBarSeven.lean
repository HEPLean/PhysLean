/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Ten
import Mathlib.Order.CompleteLattice.Finset
/-!

## Excluding seven 5-bar representations.

In this file we exclude the posibility of having seven 5-bar representations
(including the Higges). We primarily use the phenomenological constraint
of having no proton decay.

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

set_option maxRecDepth 1000 in
lemma qHu_eq_quantaTen_map_q_eq_of_card_one_same (𝓜 : MatterContent .same)
    (h : 𝓜.HasATopYukawa) (h1 : 𝓜.quantaTen.card = 1) :
    (𝓜.qHu = ⟨0, by decide⟩ ∧ 𝓜.quantaTen.map QuantaTen.q = {⟨0, by decide⟩}) ∨
    (𝓜.qHu = ⟨2, by decide⟩ ∧ 𝓜.quantaTen.map QuantaTen.q = {⟨1, by decide⟩}) ∨
    (𝓜.qHu = ⟨-2, by decide⟩ ∧ 𝓜.quantaTen.map QuantaTen.q = {⟨-1, by decide⟩}) := by
  have h1 : (𝓜.quantaTen.map QuantaTen.q).card = 1 := by
    rw [Multiset.card_map]
    exact h1
  rw [HasATopYukawa] at h
  rw [quantaTen_map_q_eq_toFinset] at h h1 ⊢
  generalize (Multiset.map QuantaTen.q 𝓜.quantaTen).toFinset = T at h h1 ⊢
  have hT : T ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = 1) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ T
  revert T
  generalize 𝓜.qHu = a
  revert a
  decide

set_option maxRecDepth 2000 in
lemma zero_not_mem_quantaTen_of_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨0, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma one_not_mem_quantaTen_of_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨1, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma neg_one_not_mem_quantaTen_of_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨-1, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma neg_two_not_mem_quantaTen_of_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨-2, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma two_not_mem_quantaTen_of_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨2, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 20000 in
lemma qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_five_mem
    (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 5) (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa)
    (hSpec : 𝓜.ValidMatterSpectrum) :
    𝓜.qHu = ⟨0, by decide⟩ ∧
    𝓜.quantaTen.map QuantaTen.q = {⟨-3, by decide⟩, ⟨3, by decide⟩} := by
  have hcardT : (𝓜.quantaTen.map QuantaTen.q).card ≤ 3 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaTen_card_le_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := zero_not_mem_quantaTen_of_quantaBarFiveMatter_card_five 𝓜 hcard h
  have hN1 := one_not_mem_quantaTen_of_quantaBarFiveMatter_card_five 𝓜 hcard h
  have hN2 := two_not_mem_quantaTen_of_quantaBarFiveMatter_card_five 𝓜 hcard h
  have hNneg1 := neg_one_not_mem_quantaTen_of_quantaBarFiveMatter_card_five 𝓜 hcard h
  have hNneg2 := neg_two_not_mem_quantaTen_of_quantaBarFiveMatter_card_five 𝓜 hcard h
  rw [quantaTen_map_q_eq_toFinset] at hTop hcardT hN0 hN1 hN2 hNneg1 hNneg2 ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = T at hTop hcardT hN0 hN1 hN2 hNneg1 hNneg2 ⊢
  revert T
  generalize 𝓜.qHu = Q
  revert Q
  simp only [Finset.card_val, Finset.mem_val, Int.reduceNeg, Multiset.insert_eq_cons,
    Finset.mem_singleton]
  decide

set_option maxRecDepth 20000 in
lemma not_quantaBarFiveMatter_card_five (𝓜 : MatterContent .same)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    ¬ 𝓜.quantaBarFiveMatter.card = 5 := by
  intro hcard
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter.2.1
  have hW1 := h.1
  have h2 := 𝓜.qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_five_mem hcard h hTop hSpec
  rw [h2.2] at hW1
  rw [h2.1] at h1
  have hmem := 𝓜.quantaBarFiveMatter_map_q_mem_powerset_filter_card hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hW1 h1
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hW1 h1 hmem
  revert F
  simp only [Finset.card_val, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_powerset,
    Int.reduceNeg, and_imp]
  decide

lemma quantaBarFive_card_le_six {I : CodimensionOneConfig} (𝓜 : MatterContent I)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    𝓜.quantaBarFive.card ≤ 6 := by
  match I with
  | .same =>
    have h1 := 𝓜.quantaBarFive_card_le_seven
    rw [quantaBarFive] at h1 ⊢
    simp_all
    have h2 := 𝓜.not_quantaBarFiveMatter_card_five h hTop hSpec
    omega
  | .nearestNeighbor =>
    apply le_of_eq_of_le (by simp :
      𝓜.quantaBarFive.card = (𝓜.quantaBarFive.map QuantaBarFive.q).card)
    rw [← Multiset.dedup_card_eq_card_iff_nodup.mpr 𝓜.quantaBarFive_map_q_noDup]
    change (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset.card ≤ _
    generalize (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset = S at *
    revert S
    decide
  | .nextToNearestNeighbor =>
    apply le_of_eq_of_le (by simp :
      𝓜.quantaBarFive.card = (𝓜.quantaBarFive.map QuantaBarFive.q).card)
    rw [← Multiset.dedup_card_eq_card_iff_nodup.mpr 𝓜.quantaBarFive_map_q_noDup]
    change (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset.card ≤ _
    generalize (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset = S at *
    revert S
    decide

end MatterContent

end SU5U1
end FTheory
