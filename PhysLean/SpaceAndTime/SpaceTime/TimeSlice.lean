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
def timeSlice {d : ℕ} {M : Type} : (SpaceTime d → M) ≃ (Time → Space d → M) where
  toFun f := Function.curry (f ∘ toTimeAndSpace.symm)
  invFun f := Function.uncurry f ∘ toTimeAndSpace
  left_inv f := by
    funext x
    simp
  right_inv f := by
    funext x t
    simp

/-- The timeslice of a function `SpaceTime d → M` forming a function
  `Time → Space d → M`, as a linear equivalence. -/
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
lemma timeSlice_spatial_deriv {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} {f : SpaceTime d → M}
    {t : Time} {x : Space d}
    (hdiff : DifferentiableAt ℝ f (toTimeAndSpace.symm (t, x))) (i : Fin d) :
    timeSlice (∂_ (Fin.natAdd 1 i) f) t x = ∂[i] (timeSlice f t) x := by
  have hf : f = (f ∘ toTimeAndSpace.symm) ∘ toTimeAndSpace := by
    ext x
    simp
  conv_lhs =>
    rw [hf]
    simp only [timeSlice, realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      Equiv.coe_fn_mk, Function.curry_apply, Function.comp_apply]
    rw [deriv_comp_toTimeAndSpace_natAdd i (f ∘ ⇑toTimeAndSpace.symm)]
  conv_rhs =>
    rw [timeSlice]
    simp [Space.deriv]
  simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [fderiv_curry_snd]
  · simp [basis]
  · fun_prop

/-- The derivative on time commutes with time-slicing. -/
lemma timeSlice_time_deriv {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} (f : SpaceTime d → M)
    {t : Time} {x : Space d}
    (hdiff : DifferentiableAt ℝ f (toTimeAndSpace.symm (t, x))) :
    timeSlice (∂_ (finSumFinEquiv (Sum.inl 0)) f) t x = ∂ₜ (fun t => timeSlice f t x) t := by
  have hf : f = (f ∘ toTimeAndSpace.symm) ∘ toTimeAndSpace := by
    ext x
    simp
  conv_lhs =>
    rw [hf]
    simp only [timeSlice, realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.isValue, finSumFinEquiv_apply_left, Equiv.coe_fn_mk, Function.curry_apply,
      Function.comp_apply]
    rw [deriv_comp_toTimeAndSpace_castAdd (f ∘ ⇑toTimeAndSpace.symm)]
  conv_rhs =>
    rw [timeSlice]
    simp only [Time.deriv, realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      Equiv.coe_fn_mk, Function.comp_apply]
  simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [fderiv_curry_fst]
  fun_prop

end SpaceTime

end
