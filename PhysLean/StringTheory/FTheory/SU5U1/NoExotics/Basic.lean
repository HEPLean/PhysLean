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


-/
namespace FTheory

namespace SU5U1
namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}


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

/-- The condition on the matter content for there to be three lepton doublets with
exactly one pair of Higgs.

This corresponds to the conditions that:
- `∑ᵢ |Mᵢ + Nᵢ| = 5`

Ref: Equation (29) of arXiv:1401.5084.
-/
def ThreeLeptonDoublets : Prop :=
  (𝓜.quantaBarFive.map fun a => |a.M + a.N|).sum = 5

/-- The condition on the matter content for it to produce a valid spectrum. -/
def ValidMatterSpectrum : Prop :=
  𝓜.ThreeChiralFamiles ∧
  𝓜.NoExotics ∧
  𝓜.ThreeLeptonDoublets

end MatterContent

end SU5U1

end FTheory
