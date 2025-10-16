/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Function.IsDistBounded
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
import Mathlib.Tactic.Cases

open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

namespace Distribution

variable [NormedSpace ℝ E]

open MeasureTheory
/-!

## A. Product of tempered measures

-/

instance {D1 : Type} [NormedAddCommGroup D1] [MeasurableSpace D1]
    {D2 : Type} [NormedAddCommGroup D2] [MeasurableSpace D2]
    (μ1 : Measure D1) (μ2 : Measure D2)
    [Measure.HasTemperateGrowth μ1] [Measure.HasTemperateGrowth μ2]
    [OpensMeasurableSpace (D1 × D2)] :
    Measure.HasTemperateGrowth (μ1.prod μ2) where
  exists_integrable := by
    obtain ⟨rt1, h1⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ1)
    obtain ⟨rt2, h2⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ2)
    use rt1 + rt2
    apply Integrable.mono' (h1.mul_prod h2)
    · generalize rt1 + rt2 = r
      apply Continuous.aestronglyMeasurable
      simp
      apply Continuous.inv₀
      apply Continuous.pow
      fun_prop
      intro x
      positivity
    filter_upwards with x
    simp
    calc _
      _ = |(1 + ‖x‖) ^ (-(rt1 : ℝ))  * (1 + ‖x‖) ^ (-(rt2 : ℝ))| := by
        rw [Real.rpow_add (by positivity), mul_comm]
      _ = (1 + ‖x‖) ^ (-(rt1 : ℝ))  * (1 + ‖x‖) ^ (-(rt2 : ℝ)) := by
        rw [abs_of_nonneg (by positivity)]
    simp
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ rt1)
      match x with
      | (x1, x2) =>
        simp
    · refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ rt2)
      match x with
      | (x1, x2) =>
        simp

namespace IsDistBounded

@[fun_prop]
lemma time_schwartzMap_mul_aestronglyMeasurable  {dm1 : ℕ}
    {η : 𝓢(Time × Space dm1.succ, ℝ)}
    {f : Space dm1.succ → F}
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    AEStronglyMeasurable (fun x => ‖η x‖ * ‖f x.2‖) (volume.prod volume) := by
  refine Continuous.comp_aestronglyMeasurable₂ (by fun_prop) ?_ ?_
  · fun_prop
  · apply MeasureTheory.AEStronglyMeasurable.norm
    apply MeasureTheory.AEStronglyMeasurable.comp_snd
    fun_prop

@[fun_prop]
lemma time_schwartzMap_smul_aestronglyMeasurable  {dm1 : ℕ}
    {η : 𝓢(Time × Space dm1.succ, ℝ)}
    {f : Space dm1.succ → F} [NormedSpace ℝ F]
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    AEStronglyMeasurable (fun x => η x • f x.2) (volume.prod volume) := by
  apply AEStronglyMeasurable.smul
  · fun_prop
  · apply MeasureTheory.AEStronglyMeasurable.comp_snd
    fun_prop

lemma time_schwartzMap_mul_pow_integrable {dm1 : ℕ}
    (η : 𝓢(Time × Space dm1.succ, ℝ))
    (p : ℤ) (hp : - (dm1 : ℤ) ≤ p) :
    Integrable (fun x => ‖η x‖ * ‖x.2‖ ^ p) (volume.prod volume) := by
  by_cases hp : p = 0
  · subst hp
    simp only [Nat.succ_eq_add_one, zpow_zero, mul_one]
    apply Integrable.norm
    exact η.integrable
  suffices h1 : Integrable (fun x => ‖η x‖ * ‖x.2‖ ^ (p + dm1)) (
      volume.prod (invPowMeasure (dm1 := dm1))) by
    rw [invPowMeasure, MeasureTheory.prod_withDensity_right] at h1
    erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)] at h1
    convert h1 using 1
    funext x
    simp only [Nat.succ_eq_add_one, Real.norm_eq_abs, one_div]
    rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
    simp only [inv_nonneg, norm_nonneg, pow_nonneg, coe_mk, smul_eq_mul]
    ring_nf
    rw [mul_assoc]
    congr
    have hx : 0 ≤ ‖x.2‖ := norm_nonneg x.2
    generalize ‖x.2‖ = r at *
    by_cases hr : r = 0
    · subst hr
      simp only [inv_zero]
      rw [zero_pow_eq, zero_zpow_eq, zero_zpow_eq]
      split_ifs <;> simp
      any_goals omega
    · simp only [inv_pow]
      field_simp
      rw [zpow_add₀ hr]
      simp
    · simp
    · fun_prop
  apply Integrable.mono' (integrable_pow_mul_iteratedFDeriv _ η (p + dm1).toNat 0)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact η.continuous.norm
    · apply Continuous.zpow₀
      · fun_prop
      · intro x
        right
        omega
  filter_upwards with x
  simp only [Nat.succ_eq_add_one, Real.norm_eq_abs, norm_iteratedFDeriv_zero]
  rw [mul_comm]
  rw [← zpow_natCast]
  rw [abs_of_nonneg (by positivity)]
  apply mul_le_mul _ (by rfl) (by positivity) (by positivity)
  rw [zpow_natCast]
  trans ‖x.2‖ ^ ((p + dm1).toNat : ℤ)
  · apply le_of_eq
    congr
    refine Int.eq_natCast_toNat.mpr (by omega)
  rw [zpow_natCast]
  simp
  apply pow_le_pow_left₀ (by positivity) _ ((p + ↑dm1).toNat)
  match x with
  | (x1, x2) =>
    simp


lemma time_schwartzMap_mul_integrable_norm {dm1 : ℕ}
    {η : 𝓢(Time × Space dm1.succ, ℝ)}
    {f : Space dm1.succ → F}
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    Integrable (fun x => ‖η x‖ * ‖f x.2‖) (volume.prod volume) := by
  rcases hf with ⟨n, c, g, p, c_nonneg, p_bound, hbound⟩
  apply Integrable.mono' (g := fun x => ∑ i, ‖η x‖ * (c i * ‖x.2 + g i‖ ^ p i)) _
  · fun_prop
  · filter_upwards with x
    rw [← Finset.mul_sum]
    simp
    exact mul_le_mul (by rfl) (hbound x.2) (norm_nonneg _) (abs_nonneg _)
  · apply MeasureTheory.integrable_finset_sum
    intro i _
    conv =>
      enter [1, x]
      rw [← mul_assoc, mul_comm _ (c i), mul_assoc]
    apply Integrable.const_mul
    suffices h1 : Integrable (fun x => ‖η ((x + (0,g i)) - (0,g i))‖ * ‖x.2+ g i‖ ^ p i) (volume.prod volume) by
      convert h1 using 1
      simp
    apply MeasureTheory.Integrable.comp_add_right (g := (0,g i))
      (f := fun x => ‖η (x - (0,g i))‖ * ‖x.2‖ ^ p i)
    let η' := SchwartzMap.compCLM (𝕜 := ℝ)
      (g := fun x => x - (0,g i))
      (by
        apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖g i‖)
        · have hx : (fderiv ℝ (fun x : Time × Space dm1.succ => x - (0,g i))) =
              fun _ => ContinuousLinearMap.id ℝ (Time × Space dm1.succ) := by
            funext x
            simp only [Nat.succ_eq_add_one]
            erw [fderiv_sub]
            simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, sub_zero]
            fun_prop
            fun_prop
          rw [hx]
          exact Function.HasTemperateGrowth.const _
        · fun_prop
        · intro x
          simp only [Nat.succ_eq_add_one, pow_one]
          trans ‖x‖ + ‖((0, g i) : Time × Space dm1.succ)‖
          · apply norm_sub_le
          simp [mul_add, add_mul]
          trans 1 + (‖x‖ + ‖g i‖)
          · simp
          trans (1 + (‖x‖ + ‖g i‖)) + ‖x‖ * ‖g i‖
          · simp
            positivity
          ring_nf
          rfl) (by
          simp only [Nat.succ_eq_add_one]
          use 1, (1 + ‖((0, g i) : Time × Space dm1.succ)‖)
          intro x
          simp only [Nat.succ_eq_add_one, pow_one]
          apply (norm_le_norm_add_norm_sub' x (0, g i)).trans
          trans 1 + (‖((0, g i) : Time × Space dm1.succ)‖ + ‖x - (0, g i)‖)
          · simp
          trans (1 + (‖((0, g i) : Time × Space dm1.succ)‖ + ‖x - (0, g i)‖)) + ‖((0, g i) : Time × Space dm1.succ)‖ * ‖x - (0, g i)‖
          · simp
            positivity
          ring_nf
          rfl) η
    exact time_schwartzMap_mul_pow_integrable η' (p i) (p_bound i)

lemma time_schwartzMap_smul_integrable {dm1 : ℕ}
    {η : 𝓢(Time × Space dm1.succ, ℝ)}
    {f : Space dm1.succ → F}
    (hf : IsDistBounded f) [NormedSpace ℝ F]
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    Integrable (fun x => η x • f x.2) (volume.prod volume) := by
  rw [← MeasureTheory.integrable_norm_iff]
  convert hf.time_schwartzMap_mul_integrable_norm (η := η) hae using 1
  funext x
  simp [norm_smul]
  fun_prop


end IsDistBounded

end Distribution
