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
