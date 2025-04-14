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
  toFun f := fun t x => f (Lorentz.Vector.toCoord.symm (fun i =>
    match i with
    | Sum.inl _ => t
    | Sum.inr i => x i))
  invFun f := fun x => f (Lorentz.Vector.toCoord x (Sum.inl 0))
    (fun i => (Lorentz.Vector.toCoord x (Sum.inr i)))
  left_inv f := by
    funext x
    simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
    congr
    refine (LinearEquiv.symm_apply_eq Lorentz.Vector.toCoord).mpr ?_
    generalize Lorentz.Vector.toCoord x = y
    funext i
    match i with
    | Sum.inl 0 => rfl
    | Sum.inr i => rfl
  right_inv f := by
    funext t x
    simp

/-- The derivative on space commutes with time-slicing. -/
semiformal_result "7Z2GA" timeSlice_spatial_deriv {M : Type} [AddCommGroup M]
    [Module ℝ M] [TopologicalSpace M] {d : ℕ} (f : SpaceTime d → M) (i : Fin d) :
  timeSlice (∂_ (finSumFinEquiv (Sum.inr i)) f) = fun t => ∂[i] (timeSlice f t)

/-- The derivative on time commutes with time-slicing. -/
semiformal_result "7Z2LF" timeSlice_time_deriv {M : Type} [AddCommGroup M]
    [Module ℝ M] [TopologicalSpace M] {d : ℕ} (f : SpaceTime d → M) :
  timeSlice (∂_ (finSumFinEquiv (Sum.inl 0)) f) = ∂ₜ (timeSlice f)

end SpaceTime

end
