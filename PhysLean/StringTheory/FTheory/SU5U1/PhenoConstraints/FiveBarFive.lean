/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.HyperchargeFlux
import Mathlib.Order.CompleteLattice.Finset
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.FiveBarSeven
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Multiset
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.TenCharges
/-!

## Studying five 5-bar representations.

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

/-!

## Case when CodimensionOneConfig is `same`

-/

set_option maxRecDepth 20000 in
lemma quantaBarFiveMatter_of_card_three
    (𝓜 : MatterContent .same)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) : (𝓜.qHu, 𝓜.Q10, 𝓜.Q5) ∈ ({
  (-2, {-1}, {-3, -1, 0}), (-2, {-1}, {-3, -1, 1}), (-2, {-1}, {-3, 0, 2}), (-2, {-1}, {-3, 1, 2}),
  (0, {0}, {-3, -2, -1}), (0, {0}, {-3, -2, 1}), (0, {0}, {-2, -1, 3}), (0, {0}, {-3, -1, 2}),
  (0, {0}, {1, 2, 3}), (0, {0}, {-1, 2, 3}), (0, {0}, {-3, 1, 2}), (0, {0}, {-2, 1, 3}),
  (2, {1}, {-2, -1, 3}), (2, {1}, {-2, 0, 3}), (2, {1}, {-1, 1, 3}), (2, {1}, {0, 1, 3}),
  (-2, {-3, -1}, {-3, -1, 0}), (-2, {-3, -1}, {-3, -1, 1}), (-2, {-3, -1}, {-3, 0, 2}),
  (-1, {-3, 2}, {3, 2, -2}), (-1, {-3, 2}, {3, 1, -2}), (-1, {-3, 2}, {3, 2, -3}),
  (-1, {-3, 2}, {2, 0, -3}), (-1, {-3, 2}, {3, -2, -3}), (-1, {-3, 2}, {2, -2, -3}),
  (1, {-2, 3}, {-3, -2, 2}), (1, {-2, 3}, {-3, -1, 2}), (1, {-2, 3}, {-3, -2, 3}),
  (1, {-2, 3}, {-2, 0, 3}), (1, {-2, 3}, {-3, 2, 3}), (1, {-2, 3}, {-2, 2, 3}),
  (2, {1, 3}, {-2, 0, 3}), (2, {1, 3}, {-1, 1, 3}), (2, {1, 3}, {0, 1, 3})} :
    Finset (ℤ × Multiset ℤ × Multiset ℤ)) := by
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter.2.1
  rw [← 𝓜.Q5_def] at h1
  have hL1 := h.2.1
  have hW1 := h.1
  have hK1 := h.2.2.2
  have hmem := 𝓜.Q5_mem_powerset_filter_card hcard
  rw [𝓜.Q5_eq_toFinset] at hW1 hK1 hL1 h1 ⊢
  generalize 𝓜.Q5.toFinset = F at hmem hW1 hK1 hL1 h1 ⊢
  revert F
  have hr := qHu_quantaTen_q_mem_of_card_three_config_same 𝓜 hcard h hTop hSpec
  generalize 𝓜.qHu = qHu at hr ⊢
  generalize 𝓜.Q10 = qTen at hr ⊢
  generalize ha : (qHu, qTen) = a at hr
  have ha1 :qHu = a.1 := by rw [← ha]
  have ha2 :qTen = a.2 := by rw [← ha]
  subst ha1 ha2
  revert a
  decide

set_option maxRecDepth 20000 in
lemma quantaBarFiveMatter_of_card_three_with_qHd
    (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) : (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5) ∈ ({
        (1, -2, {-1}, {-3, -1, 0}), (2, -2, {-1}, {-3, -1, 0}), (0, -2, {-1}, {-3, -1, 1}),
        (2, -2, {-1}, {-3, -1, 1}), (1, -2, {-1}, {-3, 0, 2}), (0, -2, {-1}, {-3, 1, 2}),
        (0, 2, {1}, {-2, -1, 3}), (-1, 2, {1}, {-2, 0, 3}), (-2, 2, {1}, {-1, 1, 3}),
        (0, 2, {1}, {-1, 1, 3}), (-2, 2, {1}, {0, 1, 3}), (-1, 2, {1}, {0, 1, 3}),
        (1, -2, {-3, -1}, {-3, -1, 0}), (2, -2, {-3, -1}, {-3, -1, 0}),
        (0, -2, {-3, -1}, {-3, -1, 1}), (2, -2, {-3, -1}, {-3, -1, 1}),
        (1, -2, {-3, -1}, {-3, 0, 2}), (-3, -1, {-3, 2}, {3, 2, -2}), (1, -1, {-3, 2}, {3, 2, -2}),
        (2, -1, {-3, 2}, {3, 1, -2}), (-2, -1, {-3, 2}, {3, 2, -3}), (0, -1, {-3, 2}, {3, 2, -3}),
        (3, -1, {-3, 2}, {2, 0, -3}), (2, -1, {-3, 2}, {3, -2, -3}), (3, -1, {-3, 2}, {2, -2, -3}),
        (-1, 1, {-2, 3}, {-3, -2, 2}), (3, 1, {-2, 3}, {-3, -2, 2}), (-2, 1, {-2, 3}, {-3, -1, 2}),
        (0, 1, {-2, 3}, {-3, -2, 3}), (2, 1, {-2, 3}, {-3, -2, 3}), (-3, 1, {-2, 3}, {-2, 0, 3}),
        (-2, 1, {-2, 3}, {-3, 2, 3}), (-3, 1, {-2, 3}, {-2, 2, 3}), (-1, 2, {1, 3}, {-2, 0, 3}),
        (-2, 2, {1, 3}, {-1, 1, 3}), (0, 2, {1, 3}, {-1, 1, 3}), (-2, 2, {1, 3}, {0, 1, 3}),
        (-1, 2, {1, 3}, {0, 1, 3})} : Finset (ℤ × ℤ × Multiset ℤ × Multiset ℤ)) := by
  rw [MuTermU1Constrained] at hμ
  rw [RParityU1Constrained] at hx
  rw [ProtonDecayU1Constrained] at h
  have hd := 𝓜.distinctly_charged_quantaBarFiveMatter.2.2.1 -- qHd not in quantaBarFiveMatter
  rw [← 𝓜.Q5_def] at hd
  have hMem := 𝓜.quantaBarFiveMatter_of_card_three h hTop hSpec hcard
  generalize 𝓜.qHu = qHu at hMem h hx hμ ⊢
  generalize 𝓜.Q10 = qTen at hMem h hx hμ ⊢
  generalize 𝓜.Q5 = qBarFive at hMem h hx hμ hd ⊢
  generalize ha : (qHu, qTen, qBarFive) = a at hMem
  have ha1 : qHu = a.1 := by rw [← ha]
  have ha2 : qTen = a.2.1 := by rw [← ha]
  have ha3 : qBarFive = a.2.2 := by rw [← ha]
  subst ha1 ha2 ha3
  have hqHd := 𝓜.qHd_mem_allowedBarFiveCharges
  generalize 𝓜.qHd = qHd at hqHd h hx hμ hd ⊢
  revert qHd
  revert a
  intro a hMem _
  intro qHd hqHd
  fin_cases hMem
    <;> fin_cases hqHd
  all_goals
    decide

lemma charges_of_anomalyFree_quantaBarFiveMatter_card_three_quantaTen_card_one
    (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hU1 : 𝓜.GaugeAnomalyU1MSSM)
    (hU1U1 : 𝓜.GaugeAnomalyU1YU1U1)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3)
    (hcardTen : 𝓜.quantaTen.card = 1) : (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5) ∈ ({
      (2, -2, {-1}, {-3, -1, 1}), (-2, 2, {1}, {-1, 1, 3}), (2, -2, {-3, -1}, {-3, -1, 1}),
      (3, -1, {-3, 2}, {2, 0, -3}), (-3, 1, {-2, 3}, {-2, 0, 3}), (-2, 2, {1, 3}, {-1, 1, 3})} :
      Finset (ℤ × ℤ × Multiset ℤ × Multiset ℤ)) := by
  have hmem := 𝓜.quantaBarFiveMatter_of_card_three_with_qHd hμ h hx hTop hSpec hcard
  have acc := 𝓜.anomalyFreeCharges_of_anomalyFree he h3 h3L hU1 hU1U1
  have hcardTen : 𝓜.Q10.card = 1 := by simpa using hcardTen
  generalize 𝓜.qHu = qHu at *
  generalize 𝓜.qHd = qHd at *
  generalize 𝓜.Q10 = Q10 at *
  generalize 𝓜.Q5 = Q5 at *
  have hacc : AnomalyFreeCharges .same (qHd, qHu, Q10, Q5).1 (qHd, qHu, Q10, Q5).2.1
    (qHd, qHu, Q10, Q5).2.2.1 (qHd, qHu, Q10, Q5).2.2.2 := acc
  have hcardTen' : (qHd, qHu, Q10, Q5).2.2.1.card = 1 := hcardTen
  generalize (qHd, qHu, Q10, Q5) = a at hmem hacc hcardTen' ⊢
  revert hacc
  revert hcardTen'
  revert a
  decide

lemma charges_of_anomalyFree_quantaBarFiveMatter_card_three_quantaTen_card_two
    (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hU1 : 𝓜.GaugeAnomalyU1MSSM)
    (hU1U1 : 𝓜.GaugeAnomalyU1YU1U1)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3)
    (hcardTen : 𝓜.quantaTen.card = 2) : (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5) ∈ ({
      (2, -2, {-1}, {-3, -1, 1}), (-2, 2, {1}, {-1, 1, 3}), (2, -2, {-3, -1}, {-3, -1, 1}),
      (3, -1, {-3, 2}, {2, 0, -3}), (-3, 1, {-2, 3}, {-2, 0, 3}), (-2, 2, {1, 3}, {-1, 1, 3})} :
      Finset (ℤ × ℤ × Multiset ℤ × Multiset ℤ)) := by
  have hmem := 𝓜.quantaBarFiveMatter_of_card_three_with_qHd hμ h hx hTop hSpec hcard
  have acc := 𝓜.anomalyFreeCharges_of_anomalyFree he h3 h3L hU1 hU1U1
  have hcardTen : 𝓜.Q10.card = 2 := by simpa using hcardTen
  generalize 𝓜.qHu = qHu at *
  generalize 𝓜.qHd = qHd at *
  generalize 𝓜.Q10 = Q10 at *
  generalize 𝓜.Q5 = Q5 at *
  have hacc : AnomalyFreeCharges .same (qHd, qHu, Q10, Q5).1 (qHd, qHu, Q10, Q5).2.1
    (qHd, qHu, Q10, Q5).2.2.1 (qHd, qHu, Q10, Q5).2.2.2 := acc
  have hcardTen' : (qHd, qHu, Q10, Q5).2.2.1.card = 2 := hcardTen
  generalize (qHd, qHu, Q10, Q5) = a at hmem hacc hcardTen' ⊢
  revert hacc
  revert hcardTen'
  revert a
  decide

lemma charges_of_anomalyFree_quantaBarFiveMatter_card_three
    (𝓜 : MatterContent .same)
    (hμ : 𝓜.MuTermU1Constrained)
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hU1 : 𝓜.GaugeAnomalyU1MSSM)
    (hU1U1 : 𝓜.GaugeAnomalyU1YU1U1)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5) ∈ ({
      (2, -2, {-1}, {-3, -1, 1}), (-2, 2, {1}, {-1, 1, 3}), (2, -2, {-3, -1}, {-3, -1, 1}),
      (3, -1, {-3, 2}, {2, 0, -3}), (-3, 1, {-2, 3}, {-2, 0, 3}), (-2, 2, {1, 3}, {-1, 1, 3})} :
      Finset (ℤ × ℤ × Multiset ℤ × Multiset ℤ)) := by
  by_cases hcardTenOne : 𝓜.quantaTen.card = 1
  · exact charges_of_anomalyFree_quantaBarFiveMatter_card_three_quantaTen_card_one
      𝓜 hμ h hx hTop hSpec he h3 h3L hU1 hU1U1 hcard hcardTenOne
  by_cases hcardTenTwo : 𝓜.quantaTen.card = 2
  · exact charges_of_anomalyFree_quantaBarFiveMatter_card_three_quantaTen_card_two
      𝓜 hμ h hx hTop hSpec he h3 h3L hU1 hU1U1 hcard hcardTenTwo
  have hmem := 𝓜.quantaBarFiveMatter_of_card_three_with_qHd hμ h hx hTop hSpec hcard
  have hcardTenOne : ¬ (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5).2.2.1.card = 1 := by simpa using hcardTenOne
  have hcardTenTwo : ¬ (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5).2.2.1.card = 2 := by simpa using hcardTenTwo
  generalize (𝓜.qHd, 𝓜.qHu, 𝓜.Q10, 𝓜.Q5) = a at *
  apply False.elim
  revert a
  decide

end MatterContent

end SU5U1
end FTheory
