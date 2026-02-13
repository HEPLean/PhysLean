/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.ConstantSliceDist
/-!


-/
open SchwartzMap NNReal
noncomputable section
open Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-- The map embedding the unit sphere in `Space d.succ` into `Space d.succ`. -/
def sphericalShell (d : ℕ) : Metric.sphere (0 : Space d.succ) 1 → Space d.succ := fun x => x.1

lemma sphericalShell_injective (d : ℕ) : Function.Injective (sphericalShell d) := by
  intro x y h
  simp [sphericalShell] at h
  grind

lemma sphericalShell_continuous (d : ℕ) : Continuous (sphericalShell d) := continuous_subtype_val

lemma sphericalShell_measurableEmbedding (d : ℕ) : MeasurableEmbedding (sphericalShell d) := by
  apply Continuous.measurableEmbedding
  · exact sphericalShell_continuous d
  · exact sphericalShell_injective d

/-- The measure on `Space d.succ` corresponding to integration around a spherical shell. -/
def sphericalShellMeasure (d : ℕ) : Measure (Space d.succ) :=
  MeasureTheory.Measure.map (sphericalShell d) (MeasureTheory.Measure.toSphere volume)

instance sphericalShellMeasure_hasTemperateGrowth (d : ℕ) :
    (sphericalShellMeasure d).HasTemperateGrowth := by
  rw [sphericalShellMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

def sphericalShellDist (d : ℕ) : (Space d.succ) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ (sphericalShellMeasure d)

lemma sphericalShellDist_apply_eq_integral_sphericalShellMeasure (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f = ∫ x, f x ∂sphericalShellMeasure d := by
  rw [sphericalShellDist, SchwartzMap.integralCLM_apply]

end Space
