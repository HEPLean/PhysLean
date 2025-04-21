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


variable {k : Type} [NontriviallyNormedField k]
    {N W M : Type} [NormedAddCommGroup M] [NormedSpace k M]
    [NormedAddCommGroup N] [NormedSpace k N]
    [NormedAddCommGroup W] [NormedSpace k W]

private lemma fderiv_uncurry  (f : N → W → M) (y : N × W) (w : W)
    (h : DifferentiableAt k (Function.uncurry f) y)  :
    fderiv k (Function.uncurry f) y (0, w) =
    fderiv k (fun x => f y.1 x) y.2 w := by
  rw [show (fun x => f y.1 x) =
    (Function.uncurry f) ∘ (fun x => (y.1, x)) by {ext w; rfl}]
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  rw [(hasFDerivAt_prodMk_right (𝕜 := k) y.1 y.2).fderiv]
  rfl

private lemma fderiv_uncurry'  (f : N → W → M) (y : N × W) (n : N)
    (h : DifferentiableAt k (Function.uncurry f) y)  :
    fderiv k (Function.uncurry f) y (n, 0) =
    fderiv k (fun x => f x y.2) y.1 n := by
  rw [show (fun x => f x y.2) =
    (Function.uncurry f) ∘ (fun x => (x, y.2)) by {ext w; rfl}]
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  rw [(hasFDerivAt_prodMk_left (𝕜 := k) y.1 y.2).fderiv]
  rfl

private lemma fderiv_curry (f : N × W → M) (n : N) (w : W)
    (h : DifferentiableAt k f (n, w)) (dw : W):
    fderiv k (Function.curry f n) w dw = fderiv k (f) (n, w) (0, dw) := by
  have h1 : f = Function.uncurry (Function.curry f) := by
    ext x
    simp
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  rw [Function.uncurry_curry]
  exact h

private lemma fderiv_curry' (f : N × W → M) (n : N) (w : W)
    (h : DifferentiableAt k f (n, w)) (dn : N):
    fderiv k (fun n => Function.curry f n w) n dn = fderiv k f (n, w) (dn, 0) := by
  have h1 : f = Function.uncurry (Function.curry f) := by
    ext x
    simp
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry']
  rw [Function.uncurry_curry]
  exact h

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
  rw [fderiv_curry]
  · simp [basis]
  · fun_prop

/-- The derivative on time commutes with time-slicing. -/
lemma timeSlice_time_deriv {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} (f : SpaceTime d → M)
    {t : Time} {x : Space d}
    (hdiff : DifferentiableAt ℝ f (toTimeAndSpace.symm (t, x))):
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
      Equiv.coe_fn_mk,  Function.comp_apply]
  simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [fderiv_curry']
  fun_prop

end SpaceTime

end
