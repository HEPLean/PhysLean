/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.FDerivCurry
import PhysLean.ClassicalMechanics.Time.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FunProp.Differentiable
import PhysLean.ClassicalMechanics.Space.Basic
/-!
# Classical vector calculus properties

Vector calculus properties under classical space and time derivatives.

-/
namespace ClassicalMechanics

open Space
open Time

lemma dt_distrib (f : Time → Space → EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x u) x) dx1) t -
    fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x v) x) dx2) t) 1
    =
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x u) x) dx1) t) 1 -
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x v) x) dx2) t) 1 := by
  rfl

lemma fderiv_coord_dt (f : Time → Space → EuclideanSpace ℝ (Fin 3)) (t dt : Time)
    (hf : Differentiable ℝ (↿f)) :
    (fun x => (fderiv ℝ (fun t => f t x i) t) dt)
    =
    (fun x => (fderiv ℝ (fun t => f t x) t) dt i) := by
  ext x
  rw [fderiv_pi]
  rfl
  · fun_prop

/-- Derivatives along space coordinates and time commute. -/
lemma fderiv_swap_time_space_coord
    (f : Time → Space → EuclideanSpace ℝ (Fin 3)) (t dt : Time) (x dx : Space)
    (hf : ContDiff ℝ 2 ↿f) :
    fderiv ℝ (fun t' => fderiv ℝ (fun x' => f t' x' i) x dx) t dt
    =
    fderiv ℝ (fun x' => fderiv ℝ (fun t' => f t' x' i) t dt) x dx := by
  have h' := fderiv_swap (𝕜 := ℝ) f t dt x dx
  change (fderiv ℝ
      (fun t' => (fderiv ℝ ((EuclideanSpace.proj i) ∘
      (fun x' => f t' x')) x) dx) t) dt = _
  trans (fderiv ℝ
      (fun t' => ((fderiv ℝ (⇑(EuclideanSpace.proj i)) (f t' x)).comp
      (fderiv ℝ (fun x' => f t' x') x)) dx) t) dt
  · congr
    funext t'
    rw [fderiv_comp]
    · fun_prop
    · apply function_differentiableAt_snd
      exact hf.two_differentiable
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  rw [fderiv_comp']
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  rw [h']
  change _ =
      (fderiv ℝ (fun x' => (fderiv ℝ ((EuclideanSpace.proj i) ∘
      (fun t' => f t' x')) t) dt) x) dx
  trans (fderiv ℝ
      (fun x' => ((fderiv ℝ (⇑(EuclideanSpace.proj i)) (f t x')).comp
      (fderiv ℝ (fun t' => f t' x') t)) dt) x) dx
  swap
  · congr
    funext x'
    rw [fderiv_comp]
    · fun_prop
    · apply function_differentiableAt_fst
      exact hf.two_differentiable
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  rw [fderiv_comp']
  simp only [PiLp.proj_apply, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  /- Start of differentiablity conditions. -/
  · fun_prop
  · apply fderiv_curry_differentiableAt_fst_comp_snd
    exact hf
  · fun_prop
  · fun_prop
  · apply fderiv_curry_differentiableAt_snd_comp_fst
    exact hf

lemma differentiableAt_fderiv_coord_single
    (ft : Time → Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 ↿ft) :
    DifferentiableAt ℝ (fun t =>
    (fderiv ℝ (fun x => ft t x u) x) (EuclideanSpace.single v 1)) t := by
  apply Differentiable.clm_apply
  · let ftt : Time → Space → ℝ := fun t x => ft t x u
    have hd : ContDiff ℝ 2 (↿ftt) := by
      change ContDiff ℝ 2 (fun x => (↿ft) x u)
      change ContDiff ℝ 2 ((EuclideanSpace.proj u) ∘ (↿ft))
      apply ContDiff.comp
      · exact ContinuousLinearMap.contDiff (EuclideanSpace.proj u) (𝕜 := ℝ)
      · exact hf
    have hdd : Differentiable ℝ (↿ftt) := hd.two_differentiable
    have h1 (t : Time) : fderiv ℝ (fun x => ftt t x) x
      = fderiv ℝ (↿ftt) (t, x) ∘L (ContinuousLinearMap.inr ℝ Time Space) := by
      ext w
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
      rw [fderiv_uncurry]
      simp only [fderiv_eq_smul_deriv, smul_eq_mul, zero_mul, zero_add]
      fun_prop
    conv =>
      enter [2, y]
      change fderiv ℝ (fun x => ftt y x) x
      rw [h1]
    fun_prop
  · fun_prop

/-- Curl and time derivative commute. -/
lemma time_deriv_curl_commute (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : Space) (hf : ContDiff ℝ 2 ↿fₜ) :
    ∂ₜ (fun t => (∇ × fₜ t) x) t = (∇ × fun x => (∂ₜ (fun t => fₜ t x) t)) x:= by
  funext i
  unfold Time.deriv
  rw [fderiv_pi]
  · change (fderiv ℝ (fun t => curl (fₜ t) x i) t) 1 = _
    unfold curl Space.deriv Space.coord Space.basis
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
      EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [fderiv_sub]
      rw [dt_distrib]
      rw [fderiv_swap_time_space_coord, fderiv_swap_time_space_coord]
      rw [fderiv_coord_dt, fderiv_coord_dt]
      repeat exact hf.two_differentiable
      repeat fun_prop
      repeat
        apply differentiableAt_fderiv_coord_single
        exact hf
  · intro i
    unfold curl Space.deriv Space.coord Space.basis
    fin_cases i <;>
    · simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
        EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      apply DifferentiableAt.sub
      repeat
        apply differentiableAt_fderiv_coord_single
        exact hf

open Matrix

set_option quotPrecheck false in
/-- Cross product in `EuclideanSpace ℝ (Fin 3)`. Uses `⨯` which is typed using `\X` or
`\vectorproduct` or `\crossproduct`. -/
infixl:70 " ⨯ₑ₃ " => fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv 2 (Fin 3 → ℝ) a ×₃ WithLp.equiv 2 (Fin 3 → ℝ) b)

/-- Cross product and fderiv commute. -/
lemma fderiv_cross_commute {u : ℝ} {s : Space} {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) :
    s ⨯ₑ₃ (fderiv ℝ (fun u => f u) u) 1
    =
    fderiv ℝ (fun u => s ⨯ₑ₃ (f u)) u 1 := by
  have h (i j : Fin 3) : s i * (fderiv ℝ (fun u => f u) u) 1 j -
      s j * (fderiv ℝ (fun u => f u) u) 1 i
      =
      (fderiv ℝ (fun t => s i * f t j - s j * f t i) u) 1:= by
    rw [fderiv_sub, fderiv_const_mul, fderiv_const_mul]
    rw [fderiv_pi]
    rfl
    intro i
    repeat fun_prop
  rw [crossProduct]
  ext i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, LinearMap.mk₂_apply,
      WithLp.equiv_pi_apply, Fin.reduceFinMk, WithLp.equiv_symm_pi_apply, cons_val]
    rw [h]
    simp only [Fin.isValue, fderiv_eq_smul_deriv, smul_eq_mul, one_mul, PiLp.smul_apply]
    rw [deriv_pi]
    simp only [Fin.isValue, WithLp.equiv_symm_pi_apply, cons_val]
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
  simp only [Equiv.apply_symm_apply, EuclideanSpace.inner_piLp_equiv_symm, star_trivial]
  rw [dotProduct_comm, dot_cross_self]

lemma inner_self_cross (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (v ⨯ₑ₃ w) = 0 := by
  cases v using WithLp.rec with | _ v =>
  cases w using WithLp.rec with | _ w =>
  simp only [Equiv.apply_symm_apply, EuclideanSpace.inner_piLp_equiv_symm, star_trivial]
  rw [dotProduct_comm, dot_self_cross]

end ClassicalMechanics
