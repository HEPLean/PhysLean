/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Insert
import PhysLean.StringTheory.FTheory.SU5U1.Charges
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Matter

This module contains the data of the matter content of the SU(5) GUT model in F-theory
with an additional U(1) symmetry.

## References

  Krippendorf, Schafer-Nameki and Wong.
  Froggatt-Nielson meets Mordell-Weil: A Phenomenological Survey of Global F-theory GUTs with U(1)s
  <https://arxiv.org/pdf/1507.05961>.

For conditions placed on the matter content, see:
  Krippendorf, Peña, Oehlmann, Ruehle.
  Rational F-theory GUTs without exotics
  <https://arxiv.org/pdf/1401.5084>.

-/
namespace FTheory

namespace SU5U1

/-- A type for the chirality flux of matter. This is induced by G₄-flux.
  This is often denoted `M`. -/
abbrev ChiralityFlux : Type := ℤ

/-- A type for the hypercharge flux associated with matter curves.
  This is often denote `N`. -/
abbrev HyperChargeFlux : Type := ℤ

/-- The type of quanta associated with matter content in the 5-bar representation. -/
abbrev QuantaBarFive (I : CodimensionOneConfig) : Type :=
  ChiralityFlux × HyperChargeFlux × I.allowedBarFiveCharges

/-- The `ChiralityFlux` quanta of a 5-bar representation. -/
abbrev QuantaBarFive.M {I : CodimensionOneConfig} (a : QuantaBarFive I) : ChiralityFlux := a.1

/-- The `HyperChargeFlux` quanta of a 5-bar representation. -/
abbrev QuantaBarFive.N {I : CodimensionOneConfig} (a : QuantaBarFive I) : HyperChargeFlux := a.2.1

/-- The extra `U(1)` charge of a 5-bar representation. -/
abbrev QuantaBarFive.q {I : CodimensionOneConfig} (a : QuantaBarFive I) :
    I.allowedBarFiveCharges := a.2.2

/-- The type of quanta associated with matter content in the 10d representation. -/
def QuantaTen (I : CodimensionOneConfig) : Type :=
  ChiralityFlux × HyperChargeFlux × I.allowedTenCharges

/-- The `ChiralityFlux` quanta of a 10d representation. -/
abbrev QuantaTen.M {I : CodimensionOneConfig} (a : QuantaTen I) : ChiralityFlux := a.1

/-- The `HyperChargeFlux` quanta of a 10d representation. -/
abbrev QuantaTen.N {I : CodimensionOneConfig} (a : QuantaTen I) : HyperChargeFlux := a.2.1

/-- The extra `U(1)` charge of a 10d representation. -/
abbrev QuantaTen.q {I : CodimensionOneConfig} (a : QuantaTen I) :
    I.allowedTenCharges := a.2.2

/-- The matter content, assumed to sit in the 5-bar or 10d representation of
  `SU(5)`. -/
structure MatterContent (I : CodimensionOneConfig) where
  /-- The chirality, charge and hyperChargeFlux associated with the 5-bar representations. -/
  quantaBarFive : Multiset (QuantaBarFive I)
  /-- The chirality, charge and hyperChargeFlux associated with the 10d representations. -/
  quantaTen : Multiset (QuantaTen I)
  /-- There is no matter in the 5-bar representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_bar_five : ∀ a ∈ quantaBarFive, (a.M = 0 → a.N ≠ 0)
  /-- There is no matter in the 10d representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_ten : ∀ a ∈ quantaTen, (a.M = 0 → a.N ≠ 0)

namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-!

## Gauge anomalies

https://arxiv.org/pdf/1401.5084
- Conditions (20) and (21) for the MSSM gauge group only.
- Condition (22) for the mixed anomaly between a single U(1) and the MSSM.
- Condition (23) for the mixed anomaly between two U(1)'s and the MSSM.

See also: arXiv:1209.4421

-/

/-- The gauge anomalies coming from the SM gauge group.

These correspond to the conditions
- `∑ₐ Mₐ - ∑ᵢ Mᵢ = 0`
- `∑ₐ Nₐ = 0`
- `∑ᵢ Nᵢ = 0`

where the sums are over the matter content in the 5-bar and 10d representations.
Ref: See equation (20) and (21) of arXiv:1401.5084. -/
def GaugeAnomalyMSSM : Prop :=
  (𝓜.quantaBarFive.map QuantaBarFive.M).sum - (𝓜.quantaTen.map QuantaTen.M).sum = 0 ∧
  (𝓜.quantaTen.map QuantaTen.N).sum = 0 ∧
  (𝓜.quantaBarFive.map QuantaBarFive.N).sum = 0


/-- The mixed U(1)-MSSM gauge anomaly.

This condition corresponds to

`∑ₐ qₐ Nₐ + ∑ᵢ qᵢ Nᵢ = 0`

Ref: See equation (22) of arXiv:1401.5084. -/
def GaugeAnomalyU1MSSM : Prop :=
  (𝓜.quantaTen.map fun a =>  a.q.1 * a.N) +
  (𝓜.quantaBarFive.map fun a => a.q.1 * a.N) = 0


/-- The mixed U(1)Y-U(1)-U(1) gauge anomaly.

This condition corresponds to

`3 * ∑ₐ qₐ qₐ Nₐ + ∑ᵢ qᵢ qᵢ Nᵢ = 0`

Ref: See equation (23) of arXiv:1401.5084. -/
def GaugeAnomalyU1YU1U1 : Prop :=
  3 * (𝓜.quantaTen.map fun a => a.q.1 * a.q.1 * a.N).sum +
  (𝓜.quantaBarFive.map fun a => a.q.1 * a.q.1 * a.N).sum = 0


/-- The condition on matter content for it to be anomaly free. -/
def AnomalyFree : Prop :=
  𝓜.GaugeAnomalyMSSM  ∧
  𝓜.GaugeAnomalyU1MSSM ∧
  𝓜.GaugeAnomalyU1YU1U1

/-!

## Conditions related to no exotics

https://arxiv.org/pdf/1401.5084
- Condition (26) for the requirement of three chiral familes.
- Condition (27) and (28) for no exotics in the spectrum.
- Condition (29) for the three lepton doublets with exactly one pair of Higges.

-/

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
  (∀ a ∈ 𝓜.quantaTen, -a.M ≤ a.N ∧ a.N ≤ a.M) ∧
  (∀ a ∈ 𝓜.quantaBarFive, -a.M - 1 ≤ a.N ∧ a.N ≤ 3)

/-- The condition on the matter content for there to be three lepton doublets with
exactly one pair of Higgs.

This corresponds to the conditions that:
- `∑ᵢ |Mᵢ + Nᵢ| = 5`
-/
def ThreeLeptonDoublets : Prop :=
  (𝓜.quantaBarFive.map fun a => |a.M + a.N|).sum = 5

end MatterContent

end SU5U1

end FTheory
