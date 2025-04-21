/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Bounds on chirality flux

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaBarFive_chiralityFlux_nonneg {a : QuantaBarFive I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFive)  : 0 ≤ a.M := by
  exact h3.2.2.1 a h

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma chiralityFlux_nonneg_of_mem {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ (𝓜.quantaBarFive).map QuantaBarFive.M)  : 0 ≤ a := by
  simp only [Multiset.mem_map] at h
  obtain ⟨a', h',  rfl⟩ := h
  exact h3.2.2.1  a' h'


/-- The chirality flux associated with a 5-bar representation must be
  less then or equal to three. -/
lemma quantaBarFive_chiralityFlux_le_three {a : QuantaBarFive I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFive) : a.M ≤ 3 := by
  rw [← h3.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map, Prod.exists, Subtype.exists] at ha
    obtain ⟨a', b, c, d, h, h2, rfl⟩ := ha
    exact quantaBarFive_chiralityFlux_nonneg h3 h
  · simp only [Multiset.mem_map, Prod.exists, Subtype.exists]
    use a.1, a.2.1, a.2.2, a.2.2.2

/-- The number of 5-bar representations with non-zero cardinality is less than or equal to three. -/
lemma quantaBarFive_chiralityFlux_filter_non_zero_card_le_three {a : QuantaBarFive I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFive) :
    ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card ≤ 3 := by
  have h2 : ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum = 0 := by
    rw [Multiset.sum_eq_zero]
    intro x hx
    rw [Multiset.mem_filter] at hx
    exact hx.2
  have h4 : ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum = 3 := by
    trans ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum +
      ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum
    · rw [h2]
      simp
    rw [Multiset.sum_filter_add_sum_filter_not]
    exact h3.1
  have hl : ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card • 1 ≤
      ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    rw [Multiset.mem_filter] at hx
    have hx' :=  quantaBarFive_chiralityFlux_nonneg h3 hx.1
    omega
  sorry

/-- The chirality flux associated with a 10d representation must be non-negative. -/
lemma quantaTen_chiralityFlux_nonneg {a : QuantaTen I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaTen)  : 0 ≤ a.M := by
  exact h3.2.2.2 a h

/-- The chirality flux associated with a 10d representation must be
  less then or equal to three. -/
lemma quantaTen_chiralityFlux_le_three {a : QuantaTen I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaTen) : a.M ≤ 3 := by
  rw [← h3.2.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map, Prod.exists, Subtype.exists] at ha
    obtain ⟨a', h1, rfl⟩ := ha
    exact quantaTen_chiralityFlux_nonneg h3 h1
  · simp only [Multiset.mem_map, Prod.exists, Subtype.exists]
    use a

end MatterContent

end SU5U1

end FTheory
