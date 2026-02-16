/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Surfaces.SphericalShell
/-!

## Ring surface in `Space 3`

-/
open SchwartzMap NNReal
noncomputable section
open Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the ring surface

-/

/-- The map embedding the unit ring in `Space d.succ` into `Space d.succ`. -/
def ring : Metric.sphere (0 : Space 2) 1 → Space 3 := fun x =>
  (slice 2).symm (0, sphericalShell 1 x)

lemma ring_injective : Function.Injective ring := by
  intro x y h
  simp [ring] at h
  exact sphericalShell_injective _ h

@[fun_prop]
lemma ring_continuous : Continuous ring := by
  apply Continuous.comp
  · fun_prop
  · fun_prop

lemma ring_measurableEmbedding : MeasurableEmbedding ring := by
  apply Continuous.measurableEmbedding
  · exact ring_continuous
  · exact ring_injective

/-!

## B. The measure associated with the ring

-/

/-- The measure on `Space 3` corresponding to integration around a ring. -/
def ringMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map ring (MeasureTheory.Measure.toSphere volume)

instance ringMeasure_hasTemperateGrowth :
    ringMeasure.HasTemperateGrowth := by
  rw [ringMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp


/-!

## C. The distribution associated with the ring

-/

/-- The distribution on `Space 3` corresponding to integration around a ring. -/
def ringDist : (Space 3) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ ringMeasure

lemma ringDist_apply_eq_integral_ringMeasure (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ x, f x ∂ringMeasure := by
  rw [ringDist, SchwartzMap.integralCLM_apply]

end Space
