/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
import PhysLean.SpaceAndTime.Space.DistOfFunction
/-!
# Distributions of functions on spacetime

-/

noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open Time
open Space SchwartzMap

def distOfSpaceFunction {d : ℕ} (f : Space d → F) (hf : IsDistBounded f) :
    (Time × Space d) →d[ℝ] F := constantTime (distOfFunction f hf)

lemma distOfSpaceFunction_apply_eq_distOfFunction {d : ℕ} (f : Space d → F) (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    distOfSpaceFunction f hf η  = distOfFunction f hf (timeIntegralSchwartz η) := by rfl

lemma distOfSpaceFunction_apply_eq_space_integral_time_integral {d : ℕ} [CompleteSpace F]
    (f : Space d → F) (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    distOfSpaceFunction f hf η = ∫ x : Space d, ∫ t : Time, η (t, x) • f x := by
  rw [distOfSpaceFunction_apply_eq_distOfFunction, distOfFunction_apply]
  simp [timeIntegralSchwartz_apply]
  congr
  funext x
  rw [integral_smul_const]

lemma distOfSpaceFunction_apply_eq_time_integral_space_integral {d : ℕ} [CompleteSpace F]
    (f : Space d → F) (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    distOfSpaceFunction f hf η = ∫ t : Time, ∫ x : Space d,  η (t, x) • f x := by
  rw [distOfSpaceFunction_apply_eq_space_integral_time_integral]
  let f' : Time × Space d → F := fun p => η p • f p.snd
  change _ = ∫ t : Time, ∫ x : Space d, f' (t, x)
  rw [← MeasureTheory.integral_prod, ← MeasureTheory.integral_prod_swap,
    MeasureTheory.integral_prod]
  rfl
  · exact (hf.integrable_time_space η).swap
  · exact hf.integrable_time_space η


lemma distOfSpaceFunction_apply_eq_time_space_integral {d : ℕ} [CompleteSpace F]
    (f : Space d → F) (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    distOfSpaceFunction f hf η = ∫ x : Time × Space d, η x • f x.2 := by
  rw [distOfSpaceFunction_apply_eq_time_integral_space_integral]
  let f' : Time × Space d → F := fun p => η p • f p.snd
  change ∫ t : Time, ∫ x : Space d, f' (t, x) = _
  rw [← MeasureTheory.integral_prod]
  rfl
  · exact hf.integrable_time_space η




end Space

end
