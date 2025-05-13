/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

## Conditions on matter content to no exotics

https://arxiv.org/pdf/1401.5084
- Condition (26) for the requirement of three chiral familes.
- Condition (27) and (28) for no exotics in the spectrum.
- Condition (29) for the three lepton doublets with exactly one pair of Higges.

## References

see also: https://arxiv.org/pdf/1011.2212

-/
namespace FTheory

namespace SU5U1
namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-- The condition on the matter content for there to exist three chiral familes.

This corresponds to the conditons that:
- `∑ₐ Mₐ = 3`
- `∑ᵢ Mᵢ = 3`
- `0 ≤ Mₐ`
- `0 ≤ Mᵢ`

Ref: Equation (26) of arXiv:1401.5084.
-/
def ThreeChiralFamiles : Prop :=
  (𝓜.quantaBarFive.map QuantaBarFive.M).sum = 3 ∧
  (𝓜.quantaTen.map QuantaTen.M).sum = 3 ∧
  (∀ a ∈ 𝓜.quantaBarFive, 0 ≤ a.M) ∧
  ∀ a ∈ 𝓜.quantaTen, 0 ≤ a.M

instance : Decidable 𝓜.ThreeChiralFamiles := instDecidableAnd

/-- The condition on the matter content for there to be no exotics in the spectrum.

This corresponds to the conditions that:
- `∑ₐ Nₐ = 0`
- `∑ᵢ Nᵢ = 0`
- `- Mₐ ≤ Nₐ ≤ Mₐ`
- `- Mᵢ - 1 ≤ Nᵢ ≤ 3`

Ref: Equation (27) and (28) of arXiv:1401.5084.
-/
def NoExotics : Prop :=
  (𝓜.quantaTen.map QuantaTen.N).sum = 0 ∧
  (𝓜.quantaBarFive.map QuantaBarFive.N).sum = 0 ∧
  (∀ a ∈ 𝓜.quantaTen, - a.M ≤ a.N ∧ a.N ≤ a.M) ∧
  (∀ a ∈ 𝓜.quantaBarFive, -a.M - 1 ≤ a.N ∧ a.N ≤ 3)

instance : Decidable 𝓜.NoExotics := instDecidableAnd

lemma quantaBarFiveMatter_map_MN_sum_of_noExotics (h : 𝓜.NoExotics) :
    ((𝓜.quantaBarFiveMatter.map QuantaBarFive.MN).map Prod.snd).sum = 0 := by
  have h1 := h.2.1
  simp only [quantaBarFive, Int.reduceNeg, QuantaBarFive.N, Multiset.map_cons, Multiset.sum_cons,
    add_neg_cancel_left] at h1
  rw [← h1]
  simp

lemma quantaBarFiveMatter_map_MN_bound_N_of_noExotics (h : 𝓜.NoExotics) :
    ∀ a ∈ (𝓜.quantaBarFiveMatter.map QuantaBarFive.MN), - a.1 - 1 ≤ a.2 ∧ a.2 ≤ 3 := by
  intro a ha
  rw [@Multiset.mem_map] at ha
  obtain ⟨a', h', rfl⟩ := ha
  refine h.2.2.2 a' ?_
  simp only [quantaBarFive, Int.reduceNeg, Multiset.mem_cons]
  right
  right
  exact h'

lemma quantaTen_map_MN_bound_N_of_noExotics (h : 𝓜.NoExotics) :
    ∀ a ∈ (𝓜.quantaTen.map QuantaTen.MN), - a.1 ≤ a.2 ∧ a.2 ≤ a.1 := by
  intro a ha
  rw [@Multiset.mem_map] at ha
  obtain ⟨a', h', rfl⟩ := ha
  exact h.2.2.1 a' h'

/-- The condition on the matter content for there to be three lepton doublets with
exactly one pair of Higgs.

This corresponds to the conditions that:
- `∑ᵢ |Mᵢ + Nᵢ| = 5`

Ref: Equation (29) of arXiv:1401.5084.
-/
def ThreeLeptonDoublets : Prop :=
  (𝓜.quantaBarFive.map fun a => |a.M + a.N|).sum = 5

instance : Decidable 𝓜.ThreeLeptonDoublets := decEq _ _

lemma quantaBarFiveMatter_map_MN_sum_of_threeLeptonDoublets (h : 𝓜.ThreeLeptonDoublets) :
    ((𝓜.quantaBarFiveMatter.map QuantaBarFive.MN).map fun a => |a.1 + a.2|).sum = 3 := by
  have h1 := h
  simp only [ThreeLeptonDoublets, quantaBarFive, Int.reduceNeg, QuantaBarFive.M, QuantaBarFive.N,
    Multiset.map_cons, zero_add, abs_one, abs_neg, Multiset.sum_cons] at h1
  ring_nf at h1
  rw [← eq_neg_add_iff_add_eq] at h1
  ring_nf at h1
  rw [← h1]
  simp

/-!

## Combined conditions

-/

/-- The condition on the matter content for it to produce a valid spectrum. -/
def ValidMatterSpectrum : Prop :=
  𝓜.ThreeChiralFamiles ∧
  𝓜.NoExotics ∧
  𝓜.ThreeLeptonDoublets

instance : Decidable 𝓜.ValidMatterSpectrum := instDecidableAnd

end MatterContent

end SU5U1

end FTheory
