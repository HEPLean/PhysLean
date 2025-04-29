/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import PhysLean.StringTheory.FTheory.SU5U1.Charges
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
abbrev QuantaTen (I : CodimensionOneConfig) : Type :=
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
@[ext]
structure MatterContent (I : CodimensionOneConfig) where
  /-- The chirality, charge and hyperChargeFlux associated with the 5-bar representations. -/
  quantaBarFiveMatter : Multiset (QuantaBarFive I)
  /-- The chirality, charge and hyperChargeFlux associated with the 10d representations. -/
  quantaTen : Multiset (QuantaTen I)
  /-- The charge of the up-type Higgs in the 5-bar representation. -/
  qHu : I.allowedBarFiveCharges
  /-- The charge of the down-type Higgs in the 5-bar representation. -/
  qHd : I.allowedBarFiveCharges
  /-- There is no matter in the 5-bar representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_bar_five_matter :
    ∀ a ∈ quantaBarFiveMatter, (a.M = 0 → a.N ≠ 0)
  /-- There is no matter in the 10d representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_ten : ∀ a ∈ quantaTen, (a.M = 0 → a.N ≠ 0)

namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-- The type `MatterContent I` has a decidable equality. -/
instance : DecidableEq (MatterContent I) := fun a b =>
  match decEq (a.qHu) (b.qHu) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.qHd) (b.qHd) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.quantaBarFiveMatter) (b.quantaBarFiveMatter) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.quantaTen) (b.quantaTen) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
    isTrue (by ext1 <;> simp_all)

/-- The `QuantaBarFive` of all 5-bar representations including the up and down Higges.
  The chirality fluxes of the up and down Higges are taken to be zero,
  whilst their hypercharge flux is taken to be -1 and +1 respectively,
  this choice is related to doublet–triplet splitting.
-/
def quantaBarFive : Multiset (QuantaBarFive I) :=
  (0, 1, 𝓜.qHd) ::ₘ (0, -1, 𝓜.qHu) ::ₘ 𝓜.quantaBarFiveMatter

lemma chirality_charge_not_both_zero_bar_five :
    ∀ a ∈ 𝓜.quantaBarFive, (a.M = 0 → a.N ≠ 0) := by
  intro a
  simp [quantaBarFive]
  intro h
  rcases h with rfl | rfl | h
  · simp [QuantaBarFive.N]
  · simp [QuantaBarFive.N]
  · exact 𝓜.chirality_charge_not_both_zero_bar_five_matter a h

lemma quantaBarFive_chiralityFlux_two_le_count_zero :
    2 ≤ (𝓜.quantaBarFive.map (QuantaBarFive.M)).count 0 := by
  simp [quantaBarFive]

lemma quantaBarFive_chiralityFlux_two_le_filter_zero_card :
    2 ≤ ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).card := by
  apply le_of_le_of_eq 𝓜.quantaBarFive_chiralityFlux_two_le_count_zero
  rw [Multiset.count_eq_card_filter_eq]
  congr
  funext x
  exact Lean.Grind.eq_congr' rfl rfl

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

instance : Decidable (GaugeAnomalyMSSM 𝓜) := instDecidableAnd

/-- The mixed U(1)-MSSM gauge anomaly.

This condition corresponds to

`∑ₐ qₐ Nₐ + ∑ᵢ qᵢ Nᵢ = 0`

Ref: See equation (22) of arXiv:1401.5084. -/
def GaugeAnomalyU1MSSM : Prop :=
  (𝓜.quantaTen.map fun a => a.q.1 * a.N).sum +
  (𝓜.quantaBarFive.map fun a => a.q.1 * a.N).sum = 0

instance : Decidable (GaugeAnomalyU1MSSM 𝓜) := decEq _ _

/-- The mixed U(1)Y-U(1)-U(1) gauge anomaly.

This condition corresponds to

`3 * ∑ₐ qₐ qₐ Nₐ + ∑ᵢ qᵢ qᵢ Nᵢ = 0`

Ref: See equation (23) of arXiv:1401.5084. -/
def GaugeAnomalyU1YU1U1 : Prop :=
  3 * (𝓜.quantaTen.map fun a => a.q.1 * a.q.1 * a.N).sum +
  (𝓜.quantaBarFive.map fun a => a.q.1 * a.q.1 * a.N).sum = 0

instance : Decidable (GaugeAnomalyU1YU1U1 𝓜) := decEq _ _

/-- The condition on matter content for it to be anomaly free. -/
def AnomalyFree : Prop :=
  𝓜.GaugeAnomalyMSSM ∧
  𝓜.GaugeAnomalyU1MSSM ∧
  𝓜.GaugeAnomalyU1YU1U1

instance : Decidable (AnomalyFree 𝓜) := instDecidableAnd

end MatterContent

end SU5U1

end FTheory
