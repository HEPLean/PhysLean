/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.FDerivCurry
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import PhysLean.ClassicalMechanics.Time.Basic
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
  · rfl
  · intro i
    fun_prop

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
  · exact hf
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
    refine Differentiable.clm_comp ?_ ?_
    · have hn (t : Time) : fderiv ℝ (↿ftt) (t, x)=
        fderiv ℝ (↿ftt) ((t, ·) x) := rfl
      conv =>
        enter [2, y]
        rw [hn]
      refine Differentiable.comp' ?_ ?_
      · exact hd.two_fderiv_differentiable
      · fun_prop
    · fun_prop
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
      repeat exact hf
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
