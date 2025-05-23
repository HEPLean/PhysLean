/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.FiveBarSeven
/-!

# Phenomenological constraints on the ten-dimension charges

The phenomenological constraints restrict the possible values
of the ten-dimensional charges of the matter content in
conjunction with the charge of the up-type quark through the
needed existence of a top Yukawa-term.

## Important results

The important results in this file are lemmas of the form:

`qHu_quantaTen_q_mem_of_card_..._config_...`

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

instance (T : Finset ℤ) (F : Finset (Multiset ℤ)) :
    Decidable (∀ s ∈ F, ¬ s ⊆ T.val) := by
  haveI x : (a : Multiset ℤ) → a ∈ F → Decidable ¬a ⊆ T.val := by
    intro a ha
    rw [Multiset.subset_iff]
    infer_instance
  apply Finset.decidableDforallFinset (_hp := x)

/-!

## Cardinialty of quantaBarFiveMatter equal to 2

-/

lemma quantaTen_q_not_mem_of_card_two_config_nearestNeighbor (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-12, -2}, {-12, 13}, {-7, -2}, {-7, 3}, {-7, 8}, {-2, 3},
      {-2, 8}, {-2, 13}, {3, 8}, {-12, -7, 13},
      {-12, 3, 13}, {-12, 8, 13}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.Q10 := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

/-!

## card = three,

-/

-- {-12, -7, -2, 3, 8, 13}
lemma quantaTen_q_not_mem_of_card_three_config_nearestNeighbor (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-2}, {3}, {-12, 13}, {-7, 8}, {-7, 13}, {-12, -7, 13}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.Q10 := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

set_option maxRecDepth 2000 in
lemma quantaTen_q_not_mem_of_card_three_config_same (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-3, 0}, {-3, 1}, {-3, 3}, {-2, -1}, {-2, 0}, {-2, 1}, {-2, 2},
    {-1, 0}, {-1, 1}, {-1, 2}, {-1, 3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.Q10 := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

lemma quantaTen_q_not_mem_of_card_three_config_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-4}, {1}, {6}, {-9, 11}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.Q10 := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

set_option maxRecDepth 20000 in
lemma qHu_quantaTen_q_mem_of_card_three_config_same
    (𝓜 : MatterContent .same) (hcard : 𝓜.quantaBarFiveMatter.card = 3)
    (h : 𝓜.ProtonDecayU1Constrained) (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    (𝓜.qHu, 𝓜.Q10) ∈ ({(-2, {-3, -1}), (-2, {-1}), (-1, {-3, 2}),
    (0, {0}), (2, {1}), (1, {-2, 3}), (2, {1, 3})} : Finset (ℤ × Multiset ℤ)) := by
  have hmem := 𝓜.Q10_mem_powerset_filter_card_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := quantaTen_q_not_mem_of_card_three_config_same 𝓜 hcard h
  rw [Q10_eq_toFinset] at hTop hN0 ⊢
  generalize 𝓜.Q10.toFinset = T at hmem hTop hN0 ⊢
  revert T
  have hqHu := 𝓜.qHu_mem_allowedBarFiveCharges
  generalize 𝓜.qHu = Q at hqHu ⊢
  revert Q
  decide

end MatterContent

end SU5U1
end FTheory
