/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Function.IsDistBounded
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Space.Distributions
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
/-!

# Distributions from bounded functions

In this module we define distributions from functions `f : EuclideanSpace ℝ (Fin d.succ) → F`
whose norm is bounded by `c1 * ‖x‖ ^ (-d : ℝ) + c2 * ‖x‖ ^ n`
for some constants `c1`, `c2` and `n`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## Key definition

- `ofFunction`: Creates a distribution from a `f` satisfying `IsDistBounded f`.

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory
open Distribution

instance  {D1 D2 : Type}
    [NormedAddCommGroup D1] [MeasurableSpace D1] (μ1 : MeasureTheory.Measure D1)
    [μ1.HasTemperateGrowth]
    [NormedAddCommGroup D2] [MeasurableSpace D2] (μ2 : MeasureTheory.Measure D2)
    [μ2.HasTemperateGrowth] [OpensMeasurableSpace (D1 × D2)] :
    (μ1.prod μ2).HasTemperateGrowth where
  exists_integrable := by
    obtain ⟨n1, hn1⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ1)
    obtain ⟨n2, hn2⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ2)
    have h0 (n : ℕ) (x : D1 × D2): (1 + ‖x‖) ^ (-  ↑n : ℝ) ≤ (1 + ‖x.1‖) ^ (- ↑n : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      refine inv_anti₀ (by positivity) ?_
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      simp
      exact norm_fst_le x
    have h2 (n : ℕ) (x : D1 × D2): (1 + ‖x‖) ^ (-  ↑n : ℝ) ≤ (1 + ‖x.2‖) ^ (- ↑n : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      refine inv_anti₀ (by positivity) ?_
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      simp
      exact norm_snd_le x
    have h1 (n : ℕ) (x : D1 × D2) : (1 + ‖x‖) ^ (- ↑n : ℝ) * (1 + ‖x‖) ^ (- ↑n : ℝ) ≤
        (1 + ‖x.1‖) ^ (- ↑n : ℝ) * (1 + ‖x.2‖) ^ (- ↑n : ℝ) := by
      refine mul_le_mul_of_nonneg (h0 n x) (h2 n x) (by positivity)  (by positivity)
    have h2 (n : ℕ) (x : D1 × D2) : (1 + ‖x‖) ^ (- 2 * ↑n : ℝ)  ≤
        (1 + ‖x.1‖) ^ (- ↑n : ℝ) * (1 + ‖x.2‖) ^ (- ↑n : ℝ) := by
      refine le_trans (le_of_eq ?_) (h1 n x)
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    have h3 (n1 n2 : ℕ) (x : D1 × D2) : (1 + ‖x‖) ^ (- 2 * (max n1 n2) : ℝ) ≤
        (1 + ‖x.1‖) ^ (- (n1 : ℝ)) * (1 + ‖x.2‖) ^ (- (n2 : ℝ)) := by
      apply le_trans (h2 (max n1 n2) x)
      apply mul_le_mul_of_nonneg _ _ (by positivity) (by positivity)
      · refine Real.rpow_le_rpow_of_exponent_le (by simp) ?_
        simp
      · refine Real.rpow_le_rpow_of_exponent_le (by simp) ?_
        simp

    have hx := MeasureTheory.Integrable.mul_prod hn1 hn2
    use 2 * max n1 n2
    apply hx.mono
    · simp
      apply Continuous.aestronglyMeasurable
      refine Continuous.rpow_const ?_ ?_
      · fun_prop
      intro x
      left
      positivity
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    convert (h3 n1 n2 x) using 1
    · simp

/-!


### Time integrals

-/
lemma continuous_time_integral  {d} (η : 𝓢(Time × Space d, ℝ)):
    Continuous (fun x : Space d => ∫ t : Time, η (t, x)) := by
  obtain ⟨rt, hrt⟩ : ∃ r,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
    obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
    use  r
    convert h using 1
    funext x
    simp
    rw [abs_of_nonneg (by positivity)]
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt, 0))
      (k := rt) (n := 0) le_rfl le_rfl η
  generalize hk : 2 ^ (rt, 0).1 * ((Finset.Iic (rt, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  simp at h0
  have h1 : ∀ x : Space d, ∀ t : Time, ‖η (t, x)‖ ≤ k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
    intro x t
    trans k * ‖(1 + ‖(t, x)‖) ^ (rt)‖⁻¹; swap
    · refine mul_le_mul_of_nonneg (by rfl) ?_ (by rw [← hk]; positivity) (by positivity)
      by_cases rt = 0
      · subst rt
        simp
      refine inv_anti₀ ?_ ?_
      · simp
        rw [abs_of_nonneg (by positivity)]
        positivity
      simp
      refine pow_le_pow_left₀ (by positivity) ?_ rt
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp
    have h0' := h0 t x
    refine (le_mul_inv_iff₀ ?_).mpr ?_
    · simp
      by_cases hr : rt = 0
      · subst rt
        simp
      positivity
    convert h0' using 1
    rw [mul_comm]
    congr
    simp
    rw [abs_of_nonneg (by positivity)]
  apply MeasureTheory.continuous_of_dominated (bound := fun t => k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ )
  · intro x
    fun_prop
  · intro x
    filter_upwards with t
    exact h1 x t
  · apply Integrable.const_mul
    convert hrt using 1
    funext t
    simp
  · filter_upwards with t
    fun_prop

lemma time_integral_hasFDerivAt  {d : ℕ} (η : 𝓢(Time × Space d.succ, ℝ)) (x₀ : Space d.succ):
    HasFDerivAt (fun x => ∫ (t : Time), η (t, x)) (∫ (t : Time), fderiv ℝ (fun x : Space d.succ => η (t, x)) x₀) x₀  := by
  let F : Space d.succ → Time → ℝ := fun x t => η (t, x)
  let F' : Space d.succ → Time → Space d.succ →L[ℝ] ℝ := fun x₀ t => fderiv ℝ (fun x : Space d.succ => η (t, x)) x₀
  have hF : ∀ t, ∀ x, HasFDerivAt (F · t) (F' x t) x := by
    intro t x
    dsimp [F, F']
    refine DifferentiableAt.hasFDerivAt ?_
    have hf := η.smooth'
    apply Differentiable.differentiableAt
    apply Differentiable.comp
    · exact hf.differentiable (by simp)
    · fun_prop
  obtain ⟨rt, hrt⟩ : ∃ r,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
    obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
    use  r
    convert h using 1
    funext x
    simp
    rw [abs_of_nonneg (by positivity)]
  /- Getting bound. -/
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt, 1))
      (k := rt) (n := 1) le_rfl (le_rfl) η
  generalize hk : 2 ^ (rt, 1).1 * ((Finset.Iic (rt, 1)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  simp at h0
  have h1 : ∀ x : Space d.succ, ∀ t : Time, ‖iteratedFDeriv ℝ 1 ⇑η (t, x)‖ ≤ k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
    intro x t
    trans k * ‖(1 + ‖(t, x)‖) ^ (rt)‖⁻¹; swap
    · refine mul_le_mul_of_nonneg (by rfl) ?_ (by rw [← hk]; positivity) (by positivity)
      by_cases rt = 0
      · subst rt
        simp
      refine inv_anti₀ ?_ ?_
      · simp
        rw [abs_of_nonneg (by positivity)]
        positivity
      simp
      refine pow_le_pow_left₀ (by positivity) ?_ rt
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp
    have h0' := h0 t x
    refine (le_mul_inv_iff₀ ?_).mpr ?_
    · simp
      by_cases hr : rt = 0
      · subst rt
        simp
      positivity
    convert h0' using 1
    rw [mul_comm]
    congr
    simp
    rw [abs_of_nonneg (by positivity)]
  have h1 : HasFDerivAt (fun x => ∫ (a : Time), F x a) (∫ (a : Time), F' x₀ a) x₀ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun t => (k * ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ)))‖) * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ ) (ε := 1)
    · simp
    · filter_upwards with x
      fun_prop
    · simp [F]
      have hf : Integrable η (volume.prod volume) := by
        exact η.integrable
      apply MeasureTheory.Integrable.comp_measurable
      . haveI :  (Measure.map (fun t => (t, x₀)) (volume (α := Time))).HasTemperateGrowth := by
          refine { exists_integrable := ?_ }
          obtain ⟨r, hr⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
          use r
          simp
          rw [MeasurableEmbedding.integrable_map_iff]
          change  Integrable ((fun t => ((1 + ‖(t, x₀)‖) ^ r)⁻¹)) volume
          apply hr.mono
          · apply Continuous.aestronglyMeasurable
            apply Continuous.inv₀
            apply Continuous.pow
            fun_prop
            intro x
            positivity
          filter_upwards with t
          simp
          apply inv_anti₀ (by positivity)
          refine pow_le_pow_left₀ (by positivity) ?_ r
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          simp
          exact measurableEmbedding_prod_mk_right x₀
        exact η.integrable
      · fun_prop
    · simp [F']
      apply Continuous.aestronglyMeasurable
      refine Continuous.fderiv_one ?_ ?_
      · change ContDiff ℝ 1 η
        apply η.smooth'.of_le (by simp)
      · fun_prop
    · filter_upwards with t
      intro x _
      simp [F']
      rw [fderiv_comp', DifferentiableAt.fderiv_prodMk ]
      simp
      trans  ‖(fderiv ℝ ⇑η (t, x))‖ * ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ)))‖
      · exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ⇑η (t, x))
          (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ (Space d.succ)))
      trans ‖iteratedFDeriv ℝ 1 (⇑η) (t, x)‖ * ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ)))‖
      · apply le_of_eq
        congr 1
        simp
        rw [← iteratedFDerivWithin_univ]
        rw [norm_iteratedFDerivWithin_one]
        rw [fderivWithin_univ]
        exact uniqueDiffWithinAt_univ
      have h0 : ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ))‖ ≠ 0 := by
        rw [@norm_ne_zero_iff]
        simp
        rw [@ContinuousLinearMap.ext_iff]
        simp
        use Space.basis 0
        by_contra hn
        have ht : (basis 0 : Space d.succ) 0 = 0 := by
          rw [hn]
          simp
        rw [basis_apply] at ht
        simp at ht
      trans  k * (|1 + ‖t‖| ^ rt)⁻¹ *  ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ))‖
      swap
      · apply le_of_eq
        ring
      refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
      · convert h1 x t
        simp
      · rfl
      fun_prop
      fun_prop

      · apply Differentiable.differentiableAt
        exact η.smooth'.differentiable (by simp)
      fun_prop
    · apply Integrable.const_mul
      convert hrt using 1
      funext t
      simp
    · filter_upwards with t
      intro x _
      exact hF t x
  exact h1

lemma time_integral_differentiable  {d : ℕ} (η : 𝓢(Time × Space d.succ, ℝ)) :
    Differentiable ℝ (fun x => ∫ (t : Time), η (t, x)) :=
  fun x =>  (time_integral_hasFDerivAt η x).differentiableAt


lemma iteratedFDeriv_norm_le {n} {d : ℕ} (η  : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
   ∃ rt,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
   ∀ t,
   ‖iteratedFDeriv ℝ n ⇑η (t, x)‖ ≤
      (2 ^ (rt, n).1 * ((Finset.Iic (rt, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) *
      ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
  obtain ⟨rt, hrt⟩ : ∃ r,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
      obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
      use  r
      convert h using 1
      funext x
      simp
      rw [abs_of_nonneg (by positivity)]
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt, n))
      (k := rt) (n := n) le_rfl (le_rfl) η
  generalize hk : 2 ^ (rt, n).1 * ((Finset.Iic (rt, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  simp at h0
  have h1 : ∀ x : Space d.succ, ∀ t : Time, ‖iteratedFDeriv ℝ n ⇑η (t, x)‖ ≤
      (2 ^ (rt, n).1 * ((Finset.Iic (rt, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
    intro x t
    let k := 2 ^ (rt, n).1 * ((Finset.Iic (rt, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η
    trans k * ‖(1 + ‖(t, x)‖) ^ (rt)‖⁻¹; swap
    · refine mul_le_mul_of_nonneg (by rfl) ?_ (by positivity) (by positivity)
      by_cases rt = 0
      · subst rt
        simp
      refine inv_anti₀ ?_ ?_
      · simp
        rw [abs_of_nonneg (by positivity)]
        positivity
      simp
      refine pow_le_pow_left₀ (by positivity) ?_ rt
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp
    have h0' := h0 t x
    refine (le_mul_inv_iff₀ ?_).mpr ?_
    · simp
      by_cases hr : rt = 0
      · subst rt
        simp
      positivity
    convert h0' using 1
    rw [mul_comm]
    congr
    simp
    rw [abs_of_nonneg (by positivity)]
  use rt
  exact ⟨hrt, fun t => h1 x t⟩

lemma pow_mul_iteratedFDeriv_norm_le {n m} {d : ℕ}  :
   ∃ rt,   ∀ (η  : 𝓢(Time × Space d.succ, ℝ)), ∀ (x : Space d.succ) ,
   Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
   ∀ t,
    ‖(t, x)‖ ^m * ‖iteratedFDeriv ℝ n ⇑η (t, x)‖ ≤
      (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) *
      ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
  obtain ⟨rt, hrt⟩ : ∃ r,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
      obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
      use  r
      convert h using 1
      funext x
      simp
      rw [abs_of_nonneg (by positivity)]
  use rt
  intro η x
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt + m, n))
      (k := rt + m) (n := n) le_rfl (le_rfl) η
  generalize hk : 2 ^ (rt, n).1 * ((Finset.Iic (rt, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  simp at h0
  have h1 : ∀ x : Space d.succ, ∀ t : Time, ‖(t,x)‖ ^ m * ‖iteratedFDeriv ℝ n ⇑η (t, x)‖ ≤
      (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
    intro x t
    let k := 2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η
    trans k * ‖(1 + ‖(t, x)‖) ^ (rt)‖⁻¹; swap
    · refine mul_le_mul_of_nonneg (by rfl) ?_ (by positivity) (by positivity)
      by_cases rt = 0
      · subst rt
        simp
      refine inv_anti₀ ?_ ?_
      · simp
        rw [abs_of_nonneg (by positivity)]
        positivity
      simp
      refine pow_le_pow_left₀ (by positivity) ?_ rt
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp
    have h0' := h0 t x
    refine (le_mul_inv_iff₀ ?_).mpr ?_
    · simp
      by_cases hr : rt = 0
      · subst rt
        simp
      positivity
    apply le_trans _ h0'
    trans (‖(t, x)‖ ^ m * ‖(1 + ‖(t, x)‖) ^ rt‖) * ‖iteratedFDeriv ℝ n ⇑η (t, x)‖
    · apply le_of_eq
      ring
    apply mul_le_mul_of_nonneg _ (by rfl) (by positivity) (by positivity)
    trans  (1 + ‖(t, x)‖) ^ m * (1 + ‖(t, x)‖) ^ rt
    · refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
      · apply pow_le_pow_left₀ (by positivity) ?_ m
        simp
      · simp
        rw [abs_of_nonneg (by positivity)]
    apply le_of_eq
    ring_nf
    simp

  exact ⟨hrt, fun t => h1 x t⟩


@[fun_prop]
lemma integrable_fderiv_space {d : ℕ} (η  : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    Integrable (fun t => fderiv ℝ (fun x => η (t, x)) x) volume := by
  obtain ⟨rt, hrt⟩ : ∃ r,  Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
      obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
      use  r
      convert h using 1
      funext x
      simp
      rw [abs_of_nonneg (by positivity)]
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt, 1))
      (k := rt) (n := 1) le_rfl (le_rfl) η
  generalize hk : 2 ^ (rt, 1).1 * ((Finset.Iic (rt, 1)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  simp at h0
  have h1 : ∀ x : Space d.succ, ∀ t : Time, ‖iteratedFDeriv ℝ 1 ⇑η (t, x)‖ ≤ k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ := by
    intro x t
    trans k * ‖(1 + ‖(t, x)‖) ^ (rt)‖⁻¹; swap
    · refine mul_le_mul_of_nonneg (by rfl) ?_ (by rw [← hk]; positivity) (by positivity)
      by_cases rt = 0
      · subst rt
        simp
      refine inv_anti₀ ?_ ?_
      · simp
        rw [abs_of_nonneg (by positivity)]
        positivity
      simp
      refine pow_le_pow_left₀ (by positivity) ?_ rt
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp
    have h0' := h0 t x
    refine (le_mul_inv_iff₀ ?_).mpr ?_
    · simp
      by_cases hr : rt = 0
      · subst rt
        simp
      positivity
    convert h0' using 1
    rw [mul_comm]
    congr
    simp
    rw [abs_of_nonneg (by positivity)]
  have h2 : ∀ x : Space d.succ, ∀ t : Time,  ‖fderiv ℝ (fun x => η (t, x)) x‖ ≤
      k * ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space (d + 1)))‖ * (|1 + ‖t‖| ^ rt)⁻¹ := by
    intro x t
    rw [fderiv_comp', DifferentiableAt.fderiv_prodMk ]
    simp
    trans  ‖(fderiv ℝ ⇑η (t, x))‖ * ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ)))‖
    · exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ⇑η (t, x))
        (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ (Space d.succ)))
    trans ‖iteratedFDeriv ℝ 1 (⇑η) (t, x)‖ * ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ)))‖
    · apply le_of_eq
      congr 1
      simp
      rw [← iteratedFDerivWithin_univ]
      rw [norm_iteratedFDerivWithin_one]
      rw [fderivWithin_univ]
      exact uniqueDiffWithinAt_univ
    have h0 : ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ))‖ ≠ 0 := by
      rw [@norm_ne_zero_iff]
      simp
      rw [@ContinuousLinearMap.ext_iff]
      simp
      use Space.basis 0
      by_contra hn
      have ht : (basis 0 : Space d.succ) 0 = 0 := by
        rw [hn]
        simp
      rw [basis_apply] at ht
      simp at ht
    trans  k * (|1 + ‖t‖| ^ rt)⁻¹ *  ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space d.succ))‖
    swap
    · apply le_of_eq
      ring
    refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
    · convert h1 x t
      simp
    · rfl
    fun_prop
    fun_prop
    · apply Differentiable.differentiableAt
      exact η.smooth'.differentiable (by simp)
    fun_prop
  rw [← MeasureTheory.integrable_norm_iff]
  apply Integrable.mono' (g := fun t =>  k * ‖ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time) (ContinuousLinearMap.id ℝ (Space (d + 1)))‖ * (|1 + ‖t‖| ^ rt)⁻¹ )
  · apply Integrable.const_mul
    convert hrt using 1
    funext x
    simp
  · apply Continuous.aestronglyMeasurable
    apply Continuous.comp
    · fun_prop
    · refine Continuous.fderiv_one ?_ ?_
      have hη := η.smooth'
      change ContDiff ℝ 1 η
      apply hη.of_le (by simp)
      · fun_prop
  · filter_upwards with t
    convert h2 x t using 1
    simp
  · apply Continuous.aestronglyMeasurable
    refine Continuous.fderiv_one ?_ ?_
    have hη := η.smooth'
    change ContDiff ℝ 1 η
    apply hη.of_le (by simp)
    · fun_prop

@[fun_prop]
lemma iteratedFDeriv_norm_mul_pow_integrable {d : ℕ} (n m : ℕ) (η  : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    Integrable (fun t => ‖(t, x)‖ ^ m * ‖iteratedFDeriv ℝ n ⇑η (t, x)‖) volume := by
  obtain ⟨rt, hrt⟩ := pow_mul_iteratedFDeriv_norm_le (m := m) (d := d)
  have hbound := (hrt η x).2
  have hrt := (hrt η x).1
  apply Integrable.mono' (g := fun t => (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) * ‖(1 + ‖t‖) ^ (rt)‖⁻¹ )
  · apply Integrable.const_mul
    convert hrt using 1
    simp
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop
    apply Continuous.norm
    apply Continuous.comp'
    apply ContDiff.continuous_iteratedFDeriv (n := (n + 1 : ℕ))
    refine GCongr.natCast_le_natCast (by omega)
    have hη := η.smooth'
    apply hη.of_le (ENat.LEInfty.out)
    fun_prop
  · filter_upwards with t
    apply le_trans _ (hbound t)
    apply le_of_eq
    simp
    rw [abs_of_nonneg (by positivity)]
    simp

@[fun_prop]
lemma iteratedFDeriv_norm_integrable {n} {d : ℕ} (η  : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    Integrable (fun t => ‖iteratedFDeriv ℝ n ⇑η (t, x)‖) volume := by
  convert iteratedFDeriv_norm_mul_pow_integrable n 0 η x using 1
  funext t
  simp

@[fun_prop]
lemma iteratedFDeriv_integrable {n} {d : ℕ} (η  : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    Integrable (fun t => iteratedFDeriv ℝ n ⇑η (t, x)) volume := by
  rw [← MeasureTheory.integrable_norm_iff]
  apply iteratedFDeriv_norm_integrable η x
  apply Continuous.aestronglyMeasurable
  apply Continuous.comp'
  apply ContDiff.continuous_iteratedFDeriv (n := (n + 1 : ℕ))
  refine GCongr.natCast_le_natCast (by omega)
  have hη := η.smooth'
  apply hη.of_le (ENat.LEInfty.out)
  fun_prop


lemma time_integral_contDiff {d : ℕ} (n : ℕ) (η : 𝓢(Time × Space d.succ, ℝ)) :
    ContDiff ℝ n (fun x => ∫ (t : Time), η (t, x)) := by
  revert η
  induction n with
  | zero =>
    intro η
    simp
    exact continuous_time_integral η
  | succ n ih =>
    intro η
    simp
    rw [contDiff_succ_iff_hasFDerivAt]
    use fun x₀ => (∫ (t : Time), fderiv ℝ (fun x : Space d.succ => η (t, x)) x₀)
    apply And.intro
    · rw [contDiff_clm_apply_iff ]
      intro y

      have hl : (fun x => (∫ (t : Time), fderiv ℝ (fun x => η (t, x)) x) y) =
         fun x => (∫ (t : Time), fderiv ℝ (fun x => η (t, x)) x y) := by
        funext x
        simp
        rw [ContinuousLinearMap.integral_apply]
        exact integrable_fderiv_space η x
      rw [hl]
      have hl2 : (fun x => ∫ (t : Time), (fderiv ℝ (fun x => η (t, x)) x) y)=
          fun x => ∫ (t : Time), SchwartzMap.pderivCLM ℝ (0, y) η (t, x) := by
        funext x
        congr
        funext t
        simp
        rw [fderiv_comp', DifferentiableAt.fderiv_prodMk ]
        simp
        fun_prop
        fun_prop
        · apply Differentiable.differentiableAt
          exact η.smooth'.differentiable (by simp)
        fun_prop
      rw [hl2]
      apply ih
    · exact fun x => time_integral_hasFDerivAt η x

lemma time_integral_iteratedFDeriv_apply {d : ℕ} (n : ℕ) (η : 𝓢(Time × Space d.succ, ℝ)) :
    ∀ x, ∀ y, iteratedFDeriv ℝ n (fun x => ∫ (t : Time), η (t, x)) x y =
      ∫ (t : Time), (iteratedFDeriv ℝ n η (t, x)) (fun i => (0, y i)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    intro x y
    rw [iteratedFDeriv_succ_apply_left]
    trans ((fderiv ℝ (fun x => iteratedFDeriv ℝ n (fun x => ∫ (t : Time), η (t, x)) x (Fin.tail y)) x) (y 0))
    · refine Eq.symm (fderiv_continuousMultilinear_apply_const_apply ?_ (Fin.tail y) (y 0))
      apply Differentiable.differentiableAt
      apply (time_integral_contDiff (n + 1) η).differentiable_iteratedFDeriv
      refine Nat.cast_lt.mpr ?_
      omega
    conv_lhs =>
      enter [1, 2, x]
      rw [ih]
    have h0 (t : Time): ∀ x, ∀ y, (iteratedFDeriv ℝ n (fun x => η (t, x)) x) y
        = (iteratedFDeriv ℝ n η (t, x)) (fun i => (0, y i)) := by
      clear x y
      clear ih
      induction n with
      | zero => simp
      | succ n ih2 =>
        intro x y
        rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
        simp
        trans ((fderiv ℝ (fun x => iteratedFDeriv ℝ n (fun x => η (t, x)) x (Fin.tail y)) x) (y 0))
        · rw [fderiv_continuousMultilinear_apply_const_apply]
          apply Differentiable.differentiableAt
          apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
          refine Nat.cast_lt.mpr ?_
          simp
          have hη := η.smooth'
          apply ContDiff.comp
          · exact hη.of_le (by exact ENat.LEInfty.out)
          · fun_prop
        conv_lhs =>
          enter [1, 2, x]
          rw [ih2]
        rw [fderiv_continuousMultilinear_apply_const_apply]
        congr 1
        trans (fderiv ℝ (iteratedFDeriv ℝ n ⇑η ∘ fun x =>  (t, x)) x) (y 0)
        · rfl
        rw [fderiv_comp, DifferentiableAt.fderiv_prodMk ]
        simp
        fun_prop
        fun_prop
        · apply Differentiable.differentiableAt
          apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
          refine Nat.cast_lt.mpr ?_
          simp
          have hη := η.smooth'
          apply ContDiff.comp
          · exact hη.of_le (by exact ENat.LEInfty.out)
          · fun_prop
        · fun_prop
        · apply Differentiable.differentiableAt
          refine Differentiable.fun_comp ?_ ?_
          apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
          refine Nat.cast_lt.mpr ?_
          simp
          have hη := η.smooth'
          apply ContDiff.comp
          · exact hη.of_le (by exact ENat.LEInfty.out)
          · fun_prop
          fun_prop
    trans (fderiv ℝ (fun x => ∫ (t : Time),
        (SchwartzMap.iteratedPDeriv ℝ (fun i => (0, Fin.tail y i)) η (t, x)) )) x (y 0)
    · congr
      funext x
      congr
      funext t
      rw [iteratedPDeriv_eq_iteratedFDeriv]
    have h1 := time_integral_hasFDerivAt
      (SchwartzMap.iteratedPDeriv ℝ (fun i => (0, Fin.tail y i)) η) x
    rw [h1.fderiv]
    rw [ContinuousLinearMap.integral_apply]
    congr
    funext t
    rw [iteratedFDeriv_succ_apply_left]
    conv_lhs =>
      enter [1 ,2, t]
      rw [iteratedPDeriv_eq_iteratedFDeriv]
    rw [fderiv_continuousMultilinear_apply_const_apply]
    change (((fderiv ℝ (iteratedFDeriv ℝ n ⇑η ∘ fun x => (t, x)) x) (y 0)) fun i => (0, Fin.tail y i)) = _
    rw [fderiv_comp, DifferentiableAt.fderiv_prodMk]
    simp
    rfl
    fun_prop
    fun_prop
    · apply Differentiable.differentiableAt
      apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
      refine Nat.cast_lt.mpr ?_
      simp
      have hη := η.smooth'
      apply ContDiff.comp
      · exact hη.of_le (by exact ENat.LEInfty.out)
      · fun_prop
    · fun_prop
    · apply Differentiable.differentiableAt
      refine Differentiable.fun_comp ?_ ?_
      apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
      refine Nat.cast_lt.mpr ?_
      simp
      have hη := η.smooth'
      apply ContDiff.comp
      · exact hη.of_le (by exact ENat.LEInfty.out)
      · fun_prop
      fun_prop
    exact integrable_fderiv_space _ x

lemma time_integral_iteratedFDeriv_eq {d : ℕ} (n : ℕ) (η : 𝓢(Time × Space d.succ, ℝ))
    (x : Space d.succ) :
    iteratedFDeriv ℝ n (fun x => ∫ (t : Time), η (t, x)) x =
       ((∫ (t : Time), iteratedFDeriv ℝ n η (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time)
        (ContinuousLinearMap.id ℝ (Space d.succ)))) := by
  ext y
  rw [time_integral_iteratedFDeriv_apply]
  rw [← ContinuousMultilinearMap.integral_apply]
  rfl
  simp
  exact iteratedFDeriv_integrable η x


lemma time_integral_iteratedFDeriv_norm_le {d : ℕ} (n : ℕ) (η : 𝓢(Time × Space d.succ, ℝ))
    (x : Space d.succ) :
    ‖iteratedFDeriv ℝ n (fun x => ∫ (t : Time), η (t, x)) x‖ ≤
       (∫ (t : Time), ‖iteratedFDeriv ℝ n η (t, x)‖) *
        ‖(ContinuousLinearMap.prod (0 : Space d.succ →L[ℝ] Time)
        (ContinuousLinearMap.id ℝ (Space d.succ)))‖  ^ n  := by
  rw [time_integral_iteratedFDeriv_eq]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp
  refine mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
  exact norm_integral_le_integral_norm fun a => iteratedFDeriv ℝ n ⇑η (a, x)

lemma time_integral_mul_pow_iteratedFDeriv_norm_le {d : ℕ} (n m: ℕ)
    :
    ∃ rt, ∀ (η : 𝓢(Time × Space d.succ, ℝ)),∀ (x : Space d.succ),
     Integrable (fun x : Time =>  ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun x => ∫ (t : Time), η (t, x)) x‖ ≤
       ((∫ (t : Time), ‖((1 + ‖t‖) ^ rt)⁻¹‖) *
        ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖  ^ n)
        * (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η)   := by
  obtain ⟨rt, hrt⟩ := pow_mul_iteratedFDeriv_norm_le (n := n) (m := m) (d := d)
  use rt
  intro η x
  have hbound := (hrt η x).2
  have hrt := (hrt η x).1
  refine ⟨hrt, ?_⟩
  generalize hk : 2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k at *
  have hk' : 0 ≤ k := by rw [← hk]; positivity
  calc _
      _ ≤  ‖x‖ ^ m * ((∫ (t : Time), ‖iteratedFDeriv ℝ n η (t, x)‖) *
          ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖ ^ n)  := by
        refine mul_le_mul_of_nonneg (by rfl) ?_ (by positivity) (by positivity)
        exact time_integral_iteratedFDeriv_norm_le n η x
      _ ≤  (∫ (t : Time), ‖x‖ ^ m * ‖iteratedFDeriv ℝ n η (t, x)‖) *
          ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖ ^ n := by
        apply le_of_eq
        rw [← mul_assoc, MeasureTheory.integral_const_mul]
      _ ≤  (∫ (t : Time), ‖(t, x)‖ ^ m * ‖iteratedFDeriv ℝ n η (t, x)‖) *
          ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖ ^ n := by
        refine mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
        refine integral_mono ?_ ?_ ?_
        · apply Integrable.const_mul
          exact iteratedFDeriv_norm_integrable η x
        · exact iteratedFDeriv_norm_mul_pow_integrable n m η x
        · refine Pi.le_def.mpr ?_
          intro t
          apply mul_le_mul_of_nonneg _ (by rfl) (by positivity) (by positivity)
          refine pow_le_pow_left₀ (by positivity) ?_ m
          simp
      _ ≤  ((∫ (t : Time), k * ‖((1 + ‖t‖) ^ rt)⁻¹‖)) *
          ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖ ^ n := by
        refine mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
        refine integral_mono ?_ ?_ ?_
        · exact iteratedFDeriv_norm_mul_pow_integrable n m η x
        · apply Integrable.const_mul
          exact hrt
        · refine Pi.le_def.mpr ?_
          intro t
          convert hbound t using 1
          simp
  apply le_of_eq
  rw [MeasureTheory.integral_const_mul]
  ring

@[fun_prop]
lemma integrable_time_integral {d : ℕ} (η : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    Integrable (fun t => η (t, x)) volume := by
  haveI : Measure.HasTemperateGrowth ( (Measure.map (fun t => (t, x)) (volume (α := Time)))) := by
      refine { exists_integrable := ?_ }
      obtain ⟨r, hr⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := Time))
      use r
      rw [MeasurableEmbedding.integrable_map_iff]
      · simp
        apply Integrable.mono' hr
        · apply Continuous.aestronglyMeasurable
          apply Continuous.comp
          · apply Continuous.inv₀
            · fun_prop
            · intro x
              positivity
          · fun_prop
        · filter_upwards with t
          simp
          by_cases hr : r = 0
          · subst hr
            simp
          refine inv_anti₀ (by positivity) ?_
          apply pow_le_pow_left₀ (by positivity) ?_ r
          rw [abs_of_nonneg (by positivity)]
          simp
      · exact measurableEmbedding_prod_mk_right x
  apply Integrable.comp_aemeasurable
  · exact integrable η
  · fun_prop

def timeIntegralSchwartz {d : ℕ} :
     𝓢(Time × Space d.succ, ℝ) →L[ℝ] 𝓢(Space d.succ, ℝ) := by
  refine SchwartzMap.mkCLM (fun η x => ∫ (t : Time), η (t, x)) ?_ ?_ ?_ ?_
  · intro η1 η2 x
    simp
    rw [integral_add]
    · exact integrable_time_integral η1 x
    · exact integrable_time_integral η2 x
  · intro a η x
    simp
    rw [integral_const_mul]

  · intro η
    simp
    refine contDiff_infty.mpr ?_
    intro n
    exact time_integral_contDiff n η
  · simp
    intro m n
    obtain ⟨rt, hrt⟩ := time_integral_mul_pow_iteratedFDeriv_norm_le (d := d) (n := n) (m := m)
    use (Finset.Iic (rt + m, n))
    use  2 ^ (rt + m, n).1 * (∫ (t : Time), ‖((1 + ‖t‖) ^ rt)⁻¹‖) *
          ‖((0 : Space d.succ →L[ℝ] Time).prod (.id ℝ (Space d.succ)))‖  ^ n
    apply And.intro
    · positivity
    intro η x
    specialize hrt η x
    obtain ⟨hrt1, hbound⟩ := hrt
    apply le_trans hbound
    apply le_of_eq
    ring_nf
    rfl

lemma timeIntegralSchwartz_apply {d : ℕ} (η : 𝓢(Time × Space d.succ, ℝ)) (x : Space d.succ) :
    timeIntegralSchwartz η x = ∫ (t : Time), η (t, x) := by rfl

def constantTime {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} :
    ((Space d.succ) →d[ℝ] M) →ₗ[ℝ] (Time × Space d.succ) →d[ℝ] M where
  toFun f := f ∘L timeIntegralSchwartz
  map_add' f g := by
    ext η
    simp
  map_smul' c f := by
    ext η
    simp


lemma constantTime_apply  {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} (f : (Space d.succ) →d[ℝ] M)
  (η : 𝓢(Time × Space d.succ, ℝ)) :
    constantTime f η  = f (timeIntegralSchwartz η) := by rfl


lemma constantTime_spaceDerivD {M : Type} {d : ℕ} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d.succ) (f : (Space d.succ) →d[ℝ] M) :
    Space.spaceDerivD i (constantTime f) = constantTime (Space.derivD i f) := by
  ext η
  simp [constantTime_apply]
  rw [Space.derivD_apply, Space.spaceDerivD_apply]
  rw [fderivD_apply, fderivD_apply, constantTime_apply]
  congr 2
  ext x
  simp [timeIntegralSchwartz_apply]
  symm
  change fderiv ℝ (timeIntegralSchwartz η) x (basis i) = _
  calc _
      _ = fderiv ℝ (fun x => ∫ t, η (t, x) ∂volume) x (basis i) := by rfl
      _ = (∫ t, fderiv ℝ (fun x => η (t, x)) x) (basis i):= by
        have h1 := time_integral_hasFDerivAt (η) x
        rw [h1.fderiv]
      _ = (∫ t, fderiv ℝ (fun x => η (t, x)) x (basis i)) := by
        rw [ContinuousLinearMap.integral_apply]
        exact integrable_fderiv_space η x
  congr
  funext t
  change (fderiv ℝ (η ∘ fun x =>  (t, x)) x) (basis i) = _
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk ]
  simp
  rfl
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact η.smooth'.differentiable (by simp)
  · fun_prop


lemma constantTime_spaceGradD {d : ℕ} (f : (Space d.succ) →d[ℝ] ℝ) :
    Space.spaceGradD (constantTime f)  = constantTime (Space.gradD f)  := by
  ext η i
  simp [constantTime_apply]
  rw [Space.spaceGradD_apply, Space.gradD_apply]
  simp
  rw [constantTime_spaceDerivD, constantTime_apply]

lemma constantTime_spaceDivD {d : ℕ} (f : (Space d.succ) →d[ℝ] EuclideanSpace ℝ (Fin d.succ)) :
    Space.spaceDivD (constantTime f)  = constantTime (Space.divD f)  := by
  ext η
  simp [constantTime_apply]
  rw [Space.spaceDivD_apply_eq_sum_spaceDerivD, Space.divD_apply_eq_sum_derivD]
  congr
  funext i
  rw [constantTime_spaceDerivD]
  rfl


lemma constantTime_spaceCurlD (f : (Space 3) →d[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Space.spaceCurlD (constantTime f)  = constantTime (Space.curlD f)  := by
  ext η i
  rw [constantTime_apply]
  fin_cases i
  all_goals
    simp [Space.spaceCurlD, Space.curlD, constantTime_spaceDerivD, constantTime_apply]
    rfl

@[simp]
lemma constantTime_timeDerivD {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (f : (Space d.succ) →d[ℝ] M) :
    Space.timeDerivD (constantTime f) = 0 := by
  ext η
  rw [Space.timeDerivD_apply]
  rw [fderivD_apply]
  simp [constantTime_apply]
  suffices h : (timeIntegralSchwartz ((SchwartzMap.evalCLM (1, 0)) ((fderivCLM ℝ) η))) = 0 by
    rw [h]
    simp
  ext x
  rw [timeIntegralSchwartz_apply]
  calc _
    _ =  ∫ (t : Time), fderiv ℝ η (t, x) (1, 0) := by rfl
    _ = ∫ (t : Time), fderiv ℝ (fun t => η (t, x)) t 1 := by
      congr
      funext t
      change _ = (fderiv ℝ (η ∘ fun t => (t, x)) t) 1
      rw [fderiv_comp, DifferentiableAt.fderiv_prodMk ]
      simp
      · fun_prop
      · fun_prop
      · apply Differentiable.differentiableAt
        exact η.smooth'.differentiable (by simp)
      · fun_prop
    _ = ∫ (t : Time), (fun t => 1) t *  fderiv ℝ (fun t => η (t, x)) t 1 := by simp
    _ =  - ∫ (t : Time),  fderiv ℝ (fun t => 1) t 1 *  (fun t => η (t, x)) t  := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · simp
      · conv_lhs =>
          enter [t]
          simp
          change  (fderiv ℝ (η ∘ fun t => (t, x)) t) 1
          rw [fderiv_comp _ (by
            apply Differentiable.differentiableAt
            exact η.smooth'.differentiable (by simp))
            (by fun_prop), DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop) ]
          simp
          change SchwartzMap.pderivCLM ℝ (1, 0) η (t, x)
        exact integrable_time_integral ((pderivCLM ℝ (1, 0)) η) x
      · simp
        exact integrable_time_integral η x
      · fun_prop
      · apply Differentiable.comp
        · exact η.smooth'.differentiable (by simp)
        · fun_prop
  simp


end Space
