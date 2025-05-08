/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Gauge anomalies

https://arxiv.org/pdf/1401.5084
- Conditions (20) and (21) for the MSSM gauge group only.
- Condition (22) for the mixed anomaly between a single U(1) and the MSSM.
- Condition (23) for the mixed anomaly between two U(1)'s and the MSSM.

See also: arXiv:1209.4421

-/
namespace FTheory

namespace SU5U1
namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)


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
  (𝓜.quantaTen.map fun a => a.q * a.N).sum +
  (𝓜.quantaBarFive.map fun a => a.q * a.N).sum = 0

instance : Decidable (GaugeAnomalyU1MSSM 𝓜) := decEq _ _

/-- The mixed U(1)Y-U(1)-U(1) gauge anomaly.

This condition corresponds to

`3 * ∑ₐ qₐ qₐ Nₐ + ∑ᵢ qᵢ qᵢ Nᵢ = 0`

Ref: See equation (23) of arXiv:1401.5084. -/
def GaugeAnomalyU1YU1U1 : Prop :=
  3 * (𝓜.quantaTen.map fun a => a.q * a.q * a.N).sum +
  (𝓜.quantaBarFive.map fun a => a.q * a.q * a.N).sum = 0

instance : Decidable (GaugeAnomalyU1YU1U1 𝓜) := decEq _ _

/-- The condition on matter content for it to be anomaly free. -/
def AnomalyFree : Prop :=
  𝓜.GaugeAnomalyMSSM ∧
  𝓜.GaugeAnomalyU1MSSM ∧
  𝓜.GaugeAnomalyU1YU1U1

instance : Decidable (AnomalyFree 𝓜) := instDecidableAnd

/-- The anomaly coefficents assocaited with matter in the five-bar representation. -/
def fiveAnomalyCoefficient : ℤ × ℤ :=
   ((𝓜.quantaBarFiveMatter.map fun a => a.q * a.N).sum,
    (𝓜.quantaBarFiveMatter.map fun a => a.q * a.q * a.N).sum)

/-- The anomaly coefficents assocaited with matter in the ten-dim representation. -/
def tenAnomalyCoefficient : ℤ × ℤ :=
    ((𝓜.quantaTen.map fun a => a.q * a.N).sum,
      3 * (𝓜.quantaTen.map fun a => a.q * a.q * a.N).sum)

lemma anomalyCoefficent_sum_of_gaugeAnomalyU1YU1U1_gaugeAnomalyU1YU1U1
    (acc1 : 𝓜.GaugeAnomalyU1MSSM) (acc2 : 𝓜.GaugeAnomalyU1YU1U1) :
    𝓜.fiveAnomalyCoefficient + 𝓜.tenAnomalyCoefficient
    - (𝓜.qHu, 𝓜.qHu * 𝓜.qHu) + (𝓜.qHd, 𝓜.qHd * 𝓜.qHd)  = (0, 0) := by
  simp [fiveAnomalyCoefficient, tenAnomalyCoefficient]
  apply And.intro
  · rw [GaugeAnomalyU1MSSM] at acc1
    rw [← acc1]
    simp [quantaBarFive, QuantaBarFive.N, QuantaBarFive.q, QuantaBarFive.M]
    ring
  · rw [GaugeAnomalyU1YU1U1] at acc2
    rw [← acc2]
    simp [quantaBarFive, QuantaBarFive.N, QuantaBarFive.q, QuantaBarFive.M]
    ring

end MatterContent

end SU5U1

end FTheory
