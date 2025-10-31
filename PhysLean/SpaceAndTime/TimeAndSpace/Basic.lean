/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.Derivatives
import PhysLean.Mathematics.Distribution.Function.OfFunction
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PhysLean.SpaceAndTime.Space.Derivatives.Curl
/-!

# Functions and distributions on Time and Space d

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions and
distributions on both `Time` and `Space d`.

We put these results in the namespace `Space` by convention.

## ii. Key results

- `distTimeDeriv` : The derivative of a distribution on `Time × Space d` along the
  temporal coordinate.
- `distSpaceDeriv` : The derivative of a distribution on `Time × Space d` along the
  spatial `i` coordinate.
- `distSpaceGrad` : The spatial gradient of a distribution on `Time × Space d`.
- `distSpaceDiv` : The spatial divergence of a distribution on `Time × Space d`.
- `distSpaceCurl` : The spatial curl of a distribution on `Time × Space 3`.

## iii. Table of contents

- A. Derivatives involving time and space
  - A.1. Space and time derivatives in terms of curried functions
  - A.2. Commuting time and space derivatives
  - A.3. Differentiablity conditions
  - A.4. Time derivative commute with curl
- B. Derivatives of distributions on Time × Space d
  - B.1. Time derivatives
  - B.2. Space derivatives
    - B.2.1. Space derivatives commute
  - B.3. Time and space derivatives commute
  - B.4. The spatial gradient
  - B.5. The spatial divergence
  - B.6. The spatial curl

## iv. References

-/
namespace Space

/-!

## A. Derivatives involving time and space

-/

/-!

### A.1. Space and time derivatives in terms of curried functions

-/

lemma fderiv_space_eq_fderiv_curry {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t : Time) (x dx : Space d)
    (hf : Differentiable ℝ ↿f) :
    fderiv ℝ (fun x' => f t x') x dx = fderiv ℝ ↿f (t, x) (0, dx) := by
  change fderiv ℝ (↿f ∘ fun x' => (t, x')) x dx = _
  rw [fderiv_comp]
  simp
  rw [DifferentiableAt.fderiv_prodMk]
  simp
  repeat' fun_prop

lemma fderiv_time_eq_fderiv_curry {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t dt : Time) (x : Space d)
    (hf : Differentiable ℝ ↿f) :
    fderiv ℝ (fun t' => f t' x) t dt = fderiv ℝ ↿f (t, x) (dt, 0) := by
  change fderiv ℝ (↿f ∘ fun t' => (t', x)) t dt = _
  rw [fderiv_comp]
  simp
  rw [DifferentiableAt.fderiv_prodMk]
  simp
  repeat' fun_prop

/-!

### A.2. Commuting time and space derivatives

-/

/-- Derivatives along space coordinates and time commute. -/
lemma fderiv_time_commute_fderiv_space {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t dt : Time) (x dx : Space d)
    (hf : ContDiff ℝ 2 ↿f) :
    fderiv ℝ (fun t' => fderiv ℝ (fun x' => f t' x') x dx) t dt
    = fderiv ℝ (fun x' => fderiv ℝ (fun t' => f t' x') t dt) x dx := by
  trans fderiv ℝ (fun t' => (fderiv ℝ (↿f) (t', x) (0, dx))) t dt
  · congr
    funext t'
    apply fderiv_space_eq_fderiv_curry
    exact hf.differentiable (by simp)
  trans fderiv ℝ (fun x => (fderiv ℝ (↿f) x (0, dx))) (t, x) (dt, 0)
  · let f' : Time → Space d → M := fun t x => fderiv ℝ (↿f) (t, x) (0, dx)
    change (fderiv ℝ (fun t' => f' t' x) t) dt = _
    rw [fderiv_time_eq_fderiv_curry]
    rfl
    fun_prop
  symm
  trans fderiv ℝ (fun x' => (fderiv ℝ (↿f) (t, x') (dt, 0))) x dx
  · congr
    funext x'
    apply fderiv_time_eq_fderiv_curry
    exact hf.differentiable (by simp)
  trans fderiv ℝ (fun t => (fderiv ℝ (↿f) t (dt, 0))) (t, x) (0, dx)
  · let f'' : Time → Space d → M := fun t x => fderiv ℝ (↿f) (t, x) (dt, 0)
    change (fderiv ℝ (fun x' => f'' t x') x) dx = _
    rw [fderiv_space_eq_fderiv_curry]
    rfl
    fun_prop
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact hf
    simp
  repeat' fun_prop

lemma time_deriv_comm_space_deriv {d i} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (t : Time) (x : Space d) :
    Time.deriv (fun t' => Space.deriv i (f t') x) t
    = Space.deriv i (fun x' => Time.deriv (fun t' => f t' x') t) x := by
  simp only [Time.deriv_eq, Space.deriv_eq_fderiv_basis]
  exact fderiv_time_commute_fderiv_space f t 1 x (Space.basis i) hf

/-!

### A.3. Differentiablity conditions

-/

@[fun_prop]
lemma space_deriv_differentiable_time {d i} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (x : Space d) :
    Differentiable ℝ (fun t => Space.deriv i (f t) x) := by
  conv =>
    enter [2, t];
    rw [Space.deriv_eq_fderiv_basis]
  apply Differentiable.clm_apply
  · have hdd : Differentiable ℝ ↿f := hf.differentiable (by simp)
    have h1 (t : Time) : fderiv ℝ (fun x => f t x) x
      = fderiv ℝ (↿f) (t, x) ∘L (ContinuousLinearMap.inr ℝ Time (Space d)) := by
      ext w
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
      rw [← fderiv_space_eq_fderiv_curry f t x w hdd]
    conv =>
      enter [2, y]
      change fderiv ℝ (fun x => f y x) x
      rw [h1]
    fun_prop
  · fun_prop

@[fun_prop]
lemma time_deriv_differentiable_space {d } {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (t : Time) :
    Differentiable ℝ (fun x => Time.deriv (f · x) t) := by
  conv =>
    enter [2, x];
    rw [Time.deriv_eq]
  apply Differentiable.clm_apply
  · have hdd : Differentiable ℝ ↿f := hf.differentiable (by simp)
    have h1 (x : Space d) : fderiv ℝ (fun t => f t x) t
      = fderiv ℝ (↿f) (t, x) ∘L (ContinuousLinearMap.inl ℝ Time (Space d)) := by
      ext w
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply]
      rw [← fderiv_time_eq_fderiv_curry f t w x hdd]
    conv =>
      enter [2, t']
      change fderiv ℝ (fun x => f x t') t
      rw [h1]
    fun_prop
  · fun_prop

@[fun_prop]
lemma curl_differentiable_time
    (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3))
    (hf : ContDiff ℝ 2 ↿fₜ) (x : Space) :
    Differentiable ℝ (fun t => (∇ × fₜ t) x) := by
  rw [differentiable_euclidean]
  intro i
  fin_cases i
  all_goals
    simp [curl, Space.coord_apply]
    fun_prop

/-!

### A.4. Time derivative commute with curl

-/
open Time

/-- Curl and time derivative commute. -/
lemma time_deriv_curl_commute (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : Space) (hf : ContDiff ℝ 2 ↿fₜ) :
    ∂ₜ (fun t => (∇ × fₜ t) x) t = (∇ × fun x => (∂ₜ (fun t => fₜ t x) t)) x:= by
  funext i
  rw [← Time.deriv_euclid]
  · fin_cases i
    all_goals
    simp [curl, Space.coord_apply]
    rw [Time.deriv_eq]
    rw [fderiv_fun_sub]
    simp [← Time.deriv_eq]
    rw [time_deriv_comm_space_deriv, time_deriv_comm_space_deriv]
    congr
    · funext x'
      rw [Time.deriv_euclid]
      have h1 := hf.differentiable (by simp)
      fun_prop
    · funext x'
      rw [Time.deriv_euclid]
      have h1 := hf.differentiable (by simp)
      fun_prop
    repeat' fun_prop
    · apply Differentiable.differentiableAt
      fun_prop
    · apply Differentiable.differentiableAt
      fun_prop
  · fun_prop

/-!

## B. Derivatives of distributions on Time × Space d

-/

open Distribution SchwartzMap

/-!

### B.1. Time derivatives

-/

/-- The time derivative of a distribution dependent on time and space. -/
noncomputable def distTimeDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : ((Time × Space d) →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (1, 0)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distTimeDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distTimeDeriv f) ε = fderivD ℝ f ε (1, 0) := by
  simp [distTimeDeriv]

/-!

### B.2. Space derivatives

-/

/-- The space derivative of a distribution dependent on time and space. -/
noncomputable def distSpaceDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) : ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Time × Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (0, basis i)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distSpaceDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distSpaceDeriv i f) ε = fderivD ℝ f ε (0, basis i) := by
  simp [distSpaceDeriv]

/-!

#### B.2.1. Space derivatives commute

-/

lemma distSpaceDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i j : Fin d) (f : (Time × Space d) →d[ℝ] M) :
    distSpaceDeriv i (distSpaceDeriv j f) = distSpaceDeriv j (distSpaceDeriv i f) := by
  ext κ
  rw [distSpaceDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  rw [distSpaceDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  simp
  congr 1
  ext x
  change fderiv ℝ (fun x => fderiv ℝ κ x (0, basis i)) x (0, basis j) =
    fderiv ℝ (fun x => fderiv ℝ κ x (0, basis j)) x (0, basis i)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact smooth κ ⊤
    simp
    exact ENat.LEInfty.out
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop

/-!

### B.3. Time and space derivatives commute

-/

lemma distTimeDeriv_commute_distSpaceDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) :
    distTimeDeriv (distSpaceDeriv i f) = distSpaceDeriv i (distTimeDeriv f) := by
  ext κ
  rw [distTimeDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  rw [distTimeDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  simp
  congr 1
  ext x
  change fderiv ℝ (fun x => fderiv ℝ κ x (1, 0)) x (0, basis i) =
    fderiv ℝ (fun x => fderiv ℝ κ x (0, basis i)) x (1, 0)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact smooth κ ⊤
    simp
    exact ENat.LEInfty.out
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop

/-!

### B.4. The spatial gradient

-/

/-- The spatial gradient of a distribution dependent on time and space. -/
noncomputable def distSpaceGrad {d} :
    ((Time × Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f := {
      toFun := fun ε i => distSpaceDeriv i f ε
      map_add' ε1 ε2 := by funext i; simp
      map_smul' a ε := by funext i; simp
      cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma distSpaceGrad_apply {d} (f : (Time × Space d) →d[ℝ] ℝ) (ε : 𝓢(Time × Space d, ℝ)) :
    distSpaceGrad f ε = fun i => distSpaceDeriv i f ε := by
  rfl

/-!

### B.5. The spatial divergence

-/

/-- The spatial divergence of a distribution dependent on time and space. -/
noncomputable def distSpaceDiv {d} :
    ((Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] (Time × Space d) →d[ℝ] ℝ where
  toFun f := {
    toFun ε := ∑ i, distSpaceDeriv i f ε i
    map_add' ε1 ε2 := by simp [Finset.sum_add_distrib]
    map_smul' a ε := by simp [Finset.mul_sum]
    cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' a f := by
    ext x
    simp [Finset.mul_sum]

lemma distSpaceDiv_apply_eq_sum_distSpaceDeriv {d}
    (f : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Time ×Space d, ℝ)) :
    distSpaceDiv f η = ∑ i, distSpaceDeriv i f η i := by rfl

/-!

### B.6. The spatial curl

-/

/-- The curl of a distribution dependent on time and space. -/
noncomputable def distSpaceCurl : ((Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :={
    toFun ε := fun i =>
      match i with
      | 0 => distSpaceDeriv 2 f ε 1 - distSpaceDeriv 1 f ε 2
      | 1 => distSpaceDeriv 0 f ε 2 - distSpaceDeriv 2 f ε 0
      | 2 => distSpaceDeriv 1 f ε 0 - distSpaceDeriv 0 f ε 1
    map_add' ε1 ε2 := by
      funext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_add, PiLp.add_apply, Fin.reduceFinMk]
        ring
    map_smul' a ε := by
      funext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          Fin.zero_eta]
        ring
    cont := by
      rw [continuous_pi_iff]
      intro i
      fin_cases i <;> fun_prop
      }
  map_add' f1 f2 := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_add, ContinuousLinearMap.add_apply, PiLp.add_apply, Fin.zero_eta,
        ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      ring
  map_smul' a f := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
      ring

end Space
