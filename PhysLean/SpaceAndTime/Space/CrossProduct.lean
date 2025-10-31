/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.CrossProduct
import PhysLean.SpaceAndTime.Time.Derivatives
/-!

# Cross product on 3D space

-/

namespace Space
open Time Matrix

set_option quotPrecheck false in
/-- Cross product in `EuclideanSpace ℝ (Fin 3)`. Uses `⨯` which is typed using `\X` or
`\vectorproduct` or `\crossproduct`. -/
infixl:70 " ⨯ₑ₃ " => fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b)

/-- Cross product and fderiv commute. -/
lemma fderiv_cross_commute {u : Time} {s : Space} {f : Time → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) :
    s ⨯ₑ₃ (fderiv ℝ (fun u => f u) u) 1
    =
    fderiv ℝ (fun u => s ⨯ₑ₃ (f u)) u 1 := by
  have h (i j : Fin 3) : s i * (fderiv ℝ (fun u => f u) u) 1 j -
      s j * (fderiv ℝ (fun u => f u) u) 1 i
      =
      (fderiv ℝ (fun t => s i * f t j - s j * f t i) u) 1:= by
    rw [fderiv_fun_sub, fderiv_const_mul, fderiv_const_mul]
    rw [fderiv_pi]
    rfl
    intro i
    repeat fun_prop
  rw [crossProduct]
  ext i
  fin_cases i <;>
  · simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
      LinearMap.mk₂_apply, PiLp.ofLp_apply, Fin.reduceFinMk, WithLp.equiv_symm_apply,
      PiLp.toLp_apply, cons_val]
    rw [h]
    simp only [Fin.isValue]
    rw [fderiv_pi]
    simp only [Fin.isValue, PiLp.toLp_apply]
    rfl
    · intro i
      fin_cases i <;>
      · simp
        fun_prop

/-- Cross product and time derivative commute. -/
lemma time_deriv_cross_commute {s : Space} {f : Time → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) :
    s ⨯ₑ₃ (∂ₜ (fun t => f t) t)
    =
    ∂ₜ (fun t => s ⨯ₑ₃ (f t)) t := by
  repeat rw [Time.deriv]
  rw [fderiv_cross_commute]
  fun_prop

lemma inner_cross_self (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (w ⨯ₑ₃ v) = 0 := by
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  simp only [WithLp.equiv_apply, WithLp.ofLp_toLp, WithLp.equiv_symm_apply]
  change (crossProduct w) v ⬝ᵥ v = _
  rw [dotProduct_comm, dot_cross_self]

lemma inner_self_cross (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (v ⨯ₑ₃ w) = 0 := by
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  simp only [WithLp.equiv_apply, WithLp.ofLp_toLp, WithLp.equiv_symm_apply, PiLp.inner_apply,
    PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
  change (crossProduct v) w ⬝ᵥ v = _
  rw [dotProduct_comm, dot_self_cross]

end Space
