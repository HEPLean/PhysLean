/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Ten
import Mathlib.Order.CompleteLattice.Finset
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.FiveBarSeven
/-!

## Excluding six 5-bar representations.

In this file we exclude the posibility of having six 5-bar representations
(including the Higges).

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

/-!

## Case when CodimensionOneConfig is `same`

-/

set_option maxRecDepth 2000 in
lemma zero_not_mem_quantaTen_of_quantaBarFiveMatter_card_four (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨0, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨1, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma neg_one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨-1, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 20000 in
lemma qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem
    (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa)
    (hSpec : 𝓜.ValidMatterSpectrum) :
    (𝓜.qHu , 𝓜.quantaTen.map QuantaTen.q) ∈  ({
      (⟨0, by decide⟩, {⟨-3, by decide⟩, ⟨3, by decide⟩}),
      (⟨1, by decide⟩, {⟨3, by decide⟩, ⟨-2, by decide⟩}),
      (⟨-1, by decide⟩, {⟨-3, by decide⟩, ⟨2, by decide⟩}),
      (⟨0, by decide⟩, {⟨2, by decide⟩, ⟨-2, by decide⟩}),
      (⟨0, by decide⟩, {⟨-3, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩}),
      (⟨-1, by decide⟩, {⟨-3, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩}),
      (⟨0, by decide⟩, {⟨-3, by decide⟩, ⟨3, by decide⟩, ⟨-2, by decide⟩}),
      (⟨1, by decide⟩, {⟨-3, by decide⟩, ⟨3, by decide⟩, ⟨-2, by decide⟩}),
      (⟨0, by decide⟩, {⟨-3, by decide⟩, ⟨2, by decide⟩, ⟨-2, by decide⟩}),
      (⟨-1, by decide⟩, {⟨-3, by decide⟩, ⟨2, by decide⟩, ⟨-2, by decide⟩}),
      (⟨0, by decide⟩, {⟨3, by decide⟩, ⟨2, by decide⟩, ⟨-2, by decide⟩}),
      (⟨1, by decide⟩, {⟨3, by decide⟩, ⟨2, by decide⟩, ⟨-2, by decide⟩})} :
      Finset (_ × Multiset _)) := by
  have hcardT : (𝓜.quantaTen.map QuantaTen.q).card ≤ 3 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaTen_card_le_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := zero_not_mem_quantaTen_of_quantaBarFiveMatter_card_four 𝓜 hcard h
  have hN1 := one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four 𝓜 hcard h
  have hNneg1 := neg_one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four 𝓜 hcard h
  rw [quantaTen_map_q_eq_toFinset] at hTop hcardT hN0 hN1 hNneg1 ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = T at hTop hcardT hN0 hN1 hNneg1  ⊢
  revert T
  generalize 𝓜.qHu = Q
  revert Q
  simp only [Finset.card_val, Finset.mem_val, Int.reduceNeg, Multiset.insert_eq_cons,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton, Subtype.forall, Subtype.mk.injEq]
  decide

set_option maxRecDepth 20000 in
lemma qHu_eq_quantaTen_quantaBarFiveMatter_map_q_eq_of_quantaBarFiveMatter_card_four_mem_same
    (𝓜 : MatterContent .same)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) : (𝓜.qHu, 𝓜.quantaTen.map QuantaTen.q,
      𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈  ({
      (⟨1, by decide⟩, {⟨3, by decide⟩, ⟨-2, by decide⟩},
      {⟨3, by decide⟩, ⟨2, by decide⟩, ⟨-3, by decide⟩,  ⟨-2, by decide⟩}),
      (⟨-1, by decide⟩, {⟨-3, by decide⟩, ⟨2, by decide⟩},
      {⟨3, by decide⟩, ⟨2, by decide⟩, ⟨-3, by decide⟩,  ⟨-2, by decide⟩})} :
      Finset (_ × Multiset _ × Multiset _)) := by
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter.2.1
  have hL1 := h.2.1
  have hW1 := h.1
  have hK1 := h.2.2.2
  have h5 : ((𝓜.quantaBarFiveMatter).map QuantaBarFive.q).card = 4 := by
    rw [Multiset.card_map]
    exact hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hW1 hK1 hL1 h1 h5 ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hW1 hK1 hL1 h1 h5 ⊢
  have hW1T : F ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = 4) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ F
  revert F
  have hr := qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem  𝓜 hcard h hTop hSpec
  generalize 𝓜.qHu = qHu at hr ⊢
  generalize 𝓜.quantaTen.map QuantaTen.q = qTen at hr ⊢
  fin_cases hr
  all_goals
    decide

lemma not_quantaBarFiveMatter_card_four_same (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum):
    ¬ 𝓜.quantaBarFiveMatter.card = 4 := by
  intro hcard
  rw [MuTermU1Constrained] at hμ
  rw [RParityU1Constrained] at hx
  rw [ProtonDecayU1Constrained] at h
  have hd := 𝓜.distinctly_charged_quantaBarFiveMatter.2.2.1
  have hr := qHu_eq_quantaTen_quantaBarFiveMatter_map_q_eq_of_quantaBarFiveMatter_card_four_mem_same
    𝓜 h hTop hSpec hcard
  generalize 𝓜.qHu = qHu at h hx hr hμ ⊢
  generalize 𝓜.quantaTen.map QuantaTen.q = qTen at h hx hr hμ ⊢
  generalize 𝓜.quantaBarFiveMatter.map QuantaBarFive.q = qBarFive at h hx hr hμ hd ⊢
  generalize 𝓜.qHd = qHd at h hx hr hμ hd ⊢
  revert qHd
  simp only [ne_eq, imp_false, Decidable.not_not, and_imp, Subtype.forall]
  fin_cases hr
  all_goals
    simp only [Int.reduceNeg, Multiset.insert_eq_cons, Multiset.mem_cons, Subtype.mk.injEq,
      Multiset.mem_singleton]
    decide

/-!

## Case when CodimensionOneConfig is `nearestNeighbor`

-/

set_option maxRecDepth 2000 in
lemma neg_two_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor
    (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨-2, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma three_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor
    (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨3, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

set_option maxRecDepth 2000 in
lemma eight_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor
    (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨8, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _

-- 10: {-12, -7,  13}
-- 5bar:  {-14, -9, -4, 1, 6, 11}

set_option maxRecDepth 20000 in
lemma qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem_nearestNeighbor
    (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa)
    (hSpec : 𝓜.ValidMatterSpectrum) :
    (𝓜.qHu , 𝓜.quantaTen.map QuantaTen.q) ∈  ({
      (⟨-14, by decide⟩, {⟨-7, by decide⟩}),
      (⟨-14, by decide⟩, {⟨-7, by decide⟩, ⟨-12, by decide⟩}),
      (⟨-14, by decide⟩, {⟨-7, by decide⟩, ⟨13, by decide⟩}),
      (⟨-14, by decide⟩, {⟨-7, by decide⟩, ⟨-12, by decide⟩, ⟨13, by decide⟩}),
      (⟨1, by decide⟩, {⟨-12, by decide⟩, ⟨13, by decide⟩}),
      (⟨6, by decide⟩, {⟨-7, by decide⟩, ⟨13, by decide⟩}),
      (⟨6, by decide⟩, {⟨-12, by decide⟩, ⟨-7, by decide⟩, ⟨13, by decide⟩}),
      (⟨1, by decide⟩, {⟨-12, by decide⟩, ⟨-7, by decide⟩, ⟨13, by decide⟩})} :
      Finset (_ × Multiset _)) := by
  have hcardT : (𝓜.quantaTen.map QuantaTen.q).card ≤ 3 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaTen_card_le_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := neg_two_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor 𝓜 hcard h
  have hN1 := three_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor 𝓜 hcard h
  have hNneg1 := eight_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nearestNeighbor 𝓜 hcard h
  rw [quantaTen_map_q_eq_toFinset] at hTop hcardT hN0 hN1 hNneg1 ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = T at hTop hcardT hN0 hN1 hNneg1  ⊢
  revert T
  generalize 𝓜.qHu = Q
  revert Q
  simp only [Finset.card_val, Finset.mem_val, Int.reduceNeg, Multiset.insert_eq_cons,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton, Subtype.forall, Subtype.mk.injEq]
  decide


set_option maxRecDepth 20000 in
lemma not_quantaBarFiveMatter_card_four_nearestNeighbor
    (𝓜 : MatterContent .nearestNeighbor)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    ¬ 𝓜.quantaBarFiveMatter.card = 4 := by
  intro hcard
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter.2.1
  have hL1 := h.2.1
  have hW1 := h.1
  have hK1 := h.2.2.2
  have h5 : ((𝓜.quantaBarFiveMatter).map QuantaBarFive.q).card = 4 := by
    rw [Multiset.card_map]
    exact hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hW1 hK1 hL1 h1 h5
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hW1 hK1 hL1 h1 h5 ⊢
  have hW1T : F ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = 4) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ F
  revert F
  have hr := qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem_nearestNeighbor
    𝓜 hcard h hTop hSpec
  generalize 𝓜.qHu = qHu at hr ⊢
  generalize 𝓜.quantaTen.map QuantaTen.q = qTen at hr ⊢
  fin_cases hr
  all_goals
    decide

/-!

## Case when CodimensionOneConfig is `nearestNeighbor`

Ten charges : {-9, -4, 1, 6, 11}
Five bar charges : {-13, -8, -3, 2, 7, 12}
-/

set_option maxRecDepth 2000 in
lemma neg_four_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨-4, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _


set_option maxRecDepth 2000 in
lemma one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨1, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _


set_option maxRecDepth 2000 in
lemma six_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained) :
    ⟨6, by decide⟩ ∉ 𝓜.quantaTen.map QuantaTen.q := by
  exact 𝓜.lambdaTerm_K1Term_W1Term_singleton_check hcard h _


-- Ten charges : {-9, -4, 1, 6, 11}
-- Five bar charges : {-13, -8, -3, 2, 7, 12}

set_option maxRecDepth 20000 in
lemma qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 4) (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa)
    (hSpec : 𝓜.ValidMatterSpectrum) :
    𝓜.qHu =⟨2, by decide⟩ ∧  𝓜.quantaTen.map QuantaTen.q = {⟨-9, by decide⟩, ⟨11, by decide⟩} := by
  have hcardT : (𝓜.quantaTen.map QuantaTen.q).card ≤ 3 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaTen_card_le_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := neg_four_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    𝓜 hcard h
  have hN1 := one_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    𝓜 hcard h
  have hNneg1 := six_not_mem_quantaTen_of_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    𝓜 hcard h
  rw [quantaTen_map_q_eq_toFinset] at hTop hcardT hN0 hN1 hNneg1 ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = T at hTop hcardT hN0 hN1 hNneg1  ⊢
  revert T
  generalize 𝓜.qHu = Q
  revert Q
  simp only [Finset.card_val, Finset.mem_val, Int.reduceNeg, Multiset.insert_eq_cons,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton, Subtype.forall, Subtype.mk.injEq]
  decide


set_option maxRecDepth 20000 in
lemma not_quantaBarFiveMatter_card_four_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    ¬ 𝓜.quantaBarFiveMatter.card = 4 := by
  intro hcard
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter.2.1
  have hL1 := h.2.1
  have hW1 := h.1
  have hK1 := h.2.2.2
  have h5 : ((𝓜.quantaBarFiveMatter).map QuantaBarFive.q).card = 4 := by
    rw [Multiset.card_map]
    exact hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hW1 hK1 hL1 h1 h5
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hW1 hK1 hL1 h1 h5 ⊢
  have hW1T : F ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = 4) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ F
  revert F
  have hr := qHu_eq_quantaTen_map_q_eq_of_quantaBarFiveMatter_card_four_mem_nextToNearestNeighbor
    𝓜 hcard h hTop hSpec
  rw [hr.1, hr.2]
  decide

/-!

## The general case

-/

lemma not_quantaBarFiveMatter_card_four {I : CodimensionOneConfig} (𝓜 : MatterContent I)
    (hμ : 𝓜.MuTermU1Constrained) (h : 𝓜.ProtonDecayU1Constrained) (hr : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    ¬ 𝓜.quantaBarFiveMatter.card = 4 :=
  match I with
  | .same =>
    not_quantaBarFiveMatter_card_four_same 𝓜 hμ h hr hTop hSpec
  | .nearestNeighbor =>
    not_quantaBarFiveMatter_card_four_nearestNeighbor 𝓜 h hTop hSpec
  | .nextToNearestNeighbor =>
    not_quantaBarFiveMatter_card_four_nextToNearestNeighbor 𝓜 h hTop hSpec

lemma not_quantaBarFive_card_six (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained) (h : 𝓜.ProtonDecayU1Constrained) (hr : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    ¬ 𝓜.quantaBarFive.card = 6 := by
  rw [quantaBarFive]
  simp only [Int.reduceNeg, Multiset.card_cons, Nat.reduceEqDiff]
  exact not_quantaBarFiveMatter_card_four_same 𝓜 hμ h hr hTop hSpec

lemma quantaBarFive_le_five (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained) (h : 𝓜.ProtonDecayU1Constrained) (hr : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    𝓜.quantaBarFive.card ≤ 5 := by
  have := 𝓜.quantaBarFive_card_le_six h hTop hSpec
  have := not_quantaBarFive_card_six 𝓜 hμ h hr hTop hSpec
  omega

end MatterContent

end SU5U1
end FTheory
