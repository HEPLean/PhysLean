/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Mathematics.FDerivCurry
/-!
# Time slice

Time slicing functions on spacetime, turning them into a function
`Time → Space d → M`.

This is useful when going from relativistic physics (defined using `SpaceTime`)
to non-relativistic physics (defined using `Space` and `Time`).

-/

noncomputable section

namespace SpaceTime

open Time
open Space

/-- The timeslice of a function `SpaceTime d → M` forming a function
  `Time → Space d → M`. -/
def timeSlice {d : ℕ} {M : Type} (c : SpeedOfLight := 1) :
    (SpaceTime d → M) ≃ (Time → Space d → M) where
  toFun f := Function.curry (f ∘ (toTimeAndSpace c).symm)
  invFun f := Function.uncurry f ∘ toTimeAndSpace c
  left_inv f := by
    funext x
    simp
  right_inv f := by
    funext x t
    simp

lemma timeSlice_contDiff {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {n} (c : SpeedOfLight) (f : SpaceTime d → M) (h : ContDiff ℝ n f) :
    ContDiff ℝ n ↿(timeSlice c f) := by
  change ContDiff ℝ n (f ∘ (toTimeAndSpace c).symm)
  apply ContDiff.comp
  · exact h
  · exact ContinuousLinearEquiv.contDiff (toTimeAndSpace c).symm

lemma timeSlice_differentiable {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (c : SpeedOfLight)
    (f : SpaceTime d → M) (h : Differentiable ℝ f) :
    Differentiable ℝ ↿(timeSlice c f) := by
  change Differentiable ℝ (f ∘ (toTimeAndSpace c).symm)
  apply Differentiable.comp
  · exact h
  · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm

/-- The timeslice of a function `SpaceTime d → M` forming a function
  `Time → Space d → M`, as a linear equivalence. -/
def timeSliceLinearEquiv {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight := 1) :
    (SpaceTime d → M) ≃ₗ[ℝ] (Time → Space d → M) where
  toFun := timeSlice c
  invFun := (timeSlice c).symm
  map_add' f g := by
    ext t x
    simp [timeSlice]
  map_smul' := by
    intros c f
    ext t x
    simp [timeSlice]
  left_inv f := by simp
  right_inv f := by simp

lemma timeSliceLinearEquiv_apply {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight) (f : SpaceTime d → M) : timeSliceLinearEquiv c f = timeSlice c f := by
  simp [timeSliceLinearEquiv, timeSlice]

lemma timeSliceLinearEquiv_symm_apply {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight) (f : Time → Space d → M) :
    (timeSliceLinearEquiv c).symm f = (timeSlice c).symm f := by
  simp [timeSliceLinearEquiv, timeSlice]

end SpaceTime

end
