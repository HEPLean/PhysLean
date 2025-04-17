/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Meta.Informal.SemiFormal
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
def timeSlice {d : ℕ} {M : Type} : (SpaceTime d → M) ≃ (Time → Space d → M) where
  toFun f := Function.curry (f ∘ toTimeAndSpace.symm)
  invFun f := Function.uncurry f ∘ toTimeAndSpace
  left_inv f := by
    funext x
    simp
  right_inv f := by
    funext x t
    simp

def timeSliceLinearEquiv {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M] :
    (SpaceTime d → M) ≃ₗ[ℝ] (Time → Space d → M) where
  toFun := timeSlice
  invFun := timeSlice.symm
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
    (f : SpaceTime d → M) : timeSliceLinearEquiv f = timeSlice f := by
  simp [timeSliceLinearEquiv, timeSlice]

lemma timeSliceLinearEquiv_symm_apply {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (f : Time → Space d → M) : timeSliceLinearEquiv.symm f = timeSlice.symm f := by
  simp [timeSliceLinearEquiv, timeSlice]

/-- The derivative on space commutes with time-slicing. -/
semiformal_result "7Z2GA"  timeSlice_spatial_deriv {M : Type} [AddCommGroup M]
    [Module ℝ M] [TopologicalSpace M] {d : ℕ} (f : SpaceTime d → M) (i : Fin d) :
    timeSlice (∂_ (finSumFinEquiv (Sum.inr i)) f) = fun t => ∂[i] (timeSlice f t)

/-- The derivative on time commutes with time-slicing. -/
semiformal_result "7Z2LF" timeSlice_time_deriv {M : Type} [AddCommGroup M]
    [Module ℝ M] [TopologicalSpace M] {d : ℕ} (f : SpaceTime d → M) :
  timeSlice (∂_ (finSumFinEquiv (Sum.inl 0)) f) = ∂ₜ (timeSlice f)

end SpaceTime

end
