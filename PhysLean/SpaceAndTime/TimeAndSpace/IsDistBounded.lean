/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.RadialAngularMeasure
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
import Mathlib.Tactic.Cases
/-!

# Bounded functions for distributions

In this module we define the property `IsDistBounded f` for a function `f`.
It says that `f` is bounded by a finite sum of terms of the form `c * ‖x + g‖ ^ p` for
constants `c`, `g` and `-d ≤ p ` where `d` is the dimension of the space minus 1.

We prove a number of properties of these functions, in particular that they
are integrable when multiplied by a Schwartz map. This allows us to define distributions
from such functions.

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F] [NormedSpace ℝ F']

namespace Space

variable [NormedSpace ℝ E]

open MeasureTheory Distribution

/-!

## IsBounded

-/


/-- The boundedness condition on a function ` EuclideanSpace ℝ (Fin dm1.succ) → F`
  for it to form a distribution. -/
@[fun_prop]
structure IsDistBounded {d : ℕ} (f : Space d → F) : Prop where
  integrable_space' : ∀ (η : 𝓢(Space d, ℝ)), Integrable (fun x => η x • f x)
  integrable_time_space' : ∀ (η : 𝓢(Time × Space d, ℝ)), Integrable (fun x => η x • f x.2)
  aeStronglyMeasurable' : AEStronglyMeasurable f volume

namespace IsDistBounded

/-!

## A. Integrability and measurability properties

-/

@[fun_prop]
lemma aeStronglyMeasurable {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) : AEStronglyMeasurable f volume :=
  hf.aeStronglyMeasurable'

lemma aeStronglyMeasurable_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x) := by
  fun_prop

@[fun_prop]
lemma aeStronglyMeasurable_time_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Time × Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x.2) := by
  apply AEStronglyMeasurable.smul
  · fun_prop
  · apply MeasureTheory.AEStronglyMeasurable.comp_snd
    fun_prop

@[fun_prop]
lemma integrable_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) : Integrable (fun x => η x • f x) := by
  exact hf.integrable_space' η

@[fun_prop]
lemma integrable_time_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) : Integrable (fun x => η x • f x.2) := by
  exact hf.integrable_time_space' η

/-!

## B. Powers of norms are bounded

In this section we will prove that `‖x + v‖ ^ p` is `IsDistBounded`
when `- (d - 1) ≤ p` where `d` is the dimension of the space. This will form
the basis for proving that many functions are `IsDistBounded`.

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
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
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
      rcases x
      simp
    · refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ rt2)
      rcases x
      simp

lemma zpow {d : ℕ} (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) :
    IsDistBounded (fun (x : Space d) => ‖x‖ ^ p) := by
  have h1 :  AEStronglyMeasurable (fun (x : Space d) => ‖x‖ ^ p) volume :=
    AEMeasurable.aestronglyMeasurable <| by fun_prop
  constructor
  · /- Integrability for Schwartz maps on space. -/
    intro η
    rw [← MeasureTheory.integrable_norm_iff (by fun_prop)]
    simp only [smul_eq_mul, norm_mul, norm_zpow, norm_norm]
    match d with
    | 0 => simp only [Real.norm_eq_abs, Integrable.of_finite]
    | d + 1 =>
    by_cases hp' : p = 0
    · subst hp'
      simp only [zpow_zero, mul_one]
      apply Integrable.norm
      exact η.integrable
    suffices h1 : Integrable (fun x => ‖η x‖ * ‖x‖ ^ (p + d)) (radialAngularMeasure (d := (d + 1))) by
      rw [integrable_radialAngularMeasure_iff] at h1
      convert h1 using 1
      funext x
      have hx : 0 ≤ ‖x‖ := norm_nonneg x
      generalize ‖x‖ = r at *
      simp
      trans |η x| * ((r ^ d)⁻¹ *r ^ (p + d)); swap
      · ring
      congr
      by_cases hr : r = 0
      · subst hr
        simp [zero_pow_eq, zero_zpow_eq, hp']
        omega
      field_simp
      rw [zpow_add₀ hr]
      rfl
    convert integrable_pow_mul_iteratedFDeriv invPowMeasure η (p + d).toNat 0 using 1
    funext x
    simp only [Nat.succ_eq_add_one, Real.norm_eq_abs, norm_iteratedFDeriv_zero]
    rw [mul_comm]
    congr 1
    rw [← zpow_natCast]
    congr
    refine Int.eq_natCast_toNat.mpr ?_
    omega
  · /- Integrability for Schwartz maps on time and space. -/
    intro η
    rw [← MeasureTheory.integrable_norm_iff (AEMeasurable.aestronglyMeasurable (by fun_prop))]
    simp only [smul_eq_mul, norm_mul, norm_zpow, norm_norm]
    by_cases hp : p = 0
    · subst hp
      simp only [zpow_zero, mul_one]
      apply Integrable.norm
      change Integrable (⇑η) (volume.prod volume)
      exact η.integrable
    suffices h1 : Integrable (fun x => ‖η x‖ * ‖x.2‖ ^ (p + (d - 1 : ℕ))) (
        volume.prod (radialAngularMeasure (d := d))) by
      match d with
      | 0 => simpa using h1
      | d + 1 =>
      rw [radialAngularMeasure, MeasureTheory.prod_withDensity_right] at h1
      erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)] at h1
      convert h1 using 1
      funext x
      simp only [ Real.norm_eq_abs, one_div]
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
    apply Integrable.mono' (integrable_pow_mul_iteratedFDeriv _ η (p + (d - 1 : ℕ)).toNat 0)
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
    rw [mul_comm]
    rw [← zpow_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply mul_le_mul _ (by rfl) (by positivity) (by positivity)
    rw [zpow_natCast]
    trans ‖x.2‖ ^ ((p + (d - 1 : ℕ)).toNat : ℤ)
    · apply le_of_eq
      congr
      refine Int.eq_natCast_toNat.mpr (by omega)
    rw [zpow_natCast]
    ring_nf
    apply pow_le_pow_left₀ (by positivity) _ (p + (d - 1 : ℕ)).toNat
    rcases x
    simp
  · fun_prop

/-!

## C. Basic properties

-/

lemma mono {d : ℕ} {f : Space d → F}
    {g : Space d → F'} (hf : IsDistBounded f) (hg : AEStronglyMeasurable g volume)
    (hfg : ∀ x, ‖g x‖ ≤ ‖f x‖) : IsDistBounded g where
  integrable_space' η := by
    apply (hf.integrable_space' η).mono
    · fun_prop
    · filter_upwards with x
      simpa [norm_smul] using mul_le_mul_of_nonneg_left (hfg x) (by positivity)
  integrable_time_space' η := by
    apply (hf.integrable_time_space' η).mono
    · apply AEStronglyMeasurable.smul
      · fun_prop
      · apply MeasureTheory.AEStronglyMeasurable.comp_snd
        fun_prop
    · filter_upwards with x
      simpa [norm_smul] using mul_le_mul_of_nonneg_left (hfg x.2) (by positivity)
  aeStronglyMeasurable' := hg

@[fun_prop]
lemma add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) where
  integrable_space' η := by
    simp
    apply Integrable.add (hf.integrable_space' η) (hg.integrable_space' η)
  integrable_time_space' η := by
    simp
    apply Integrable.add (hf.integrable_time_space' η) (hg.integrable_time_space' η)
  aeStronglyMeasurable' := by
    fun_prop

@[fun_prop]
lemma fun_add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (fun x => f x + g x) := by
  exact hf.add hg

lemma comp_add_right {d} {f : Space d → F} (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x + c)) where
  integrable_space' η := by
    suffices h1 : Integrable (fun x => η ((x + c) - c) • f (x + c)) volume by
      simpa using h1
    apply MeasureTheory.Integrable.comp_add_right (g := c) (f := fun x => η (x - c) • f x)
    apply hf.integrable_space' (η.compCLM (𝕜 := ℝ)  ?_ ?_)
    · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖c‖)
      · convert Function.HasTemperateGrowth.const  (ContinuousLinearMap.id ℝ (Space d))
        simp [fderiv_sub_const]
      · fun_prop
      · refine fun x => (norm_sub_le _ _).trans (le_of_sub_nonneg ?_)
        ring_nf
        positivity
    · refine ⟨1, (1 + ‖c‖), fun x => (norm_le_norm_add_norm_sub' x c).trans (le_of_sub_nonneg ?_)⟩
      ring_nf
      positivity
  integrable_time_space' η := by
    suffices h1 : Integrable (fun (x : Time × Space d) =>
        η ((x + (0, c)) - (0, c)) • f (x + (0, c)).2) (volume.prod volume) by
      simpa using h1
    apply MeasureTheory.Integrable.comp_add_right (g := (0, c))
      (f := fun x => η (x - (0, c)) • f x.2)
    apply hf.integrable_time_space' (η.compCLM (𝕜 := ℝ)  ?_ ?_)
    · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖c‖)
      · convert Function.HasTemperateGrowth.const  (ContinuousLinearMap.id ℝ (Time × Space d))
        simp [fderiv_sub_const]
      · fun_prop
      · refine fun x => (norm_sub_le _ _).trans (le_of_sub_nonneg ?_)
        ring_nf
        simp only [Prod.norm_mk, norm_zero, norm_nonneg, sup_of_le_right,
          add_add_sub_cancel]
        positivity
    · refine ⟨1, (1 + ‖((0, c) : Time × Space d)‖), fun x => (norm_le_norm_add_norm_sub' x (0,c)).trans (le_of_sub_nonneg ?_)⟩
      ring_nf
      positivity
  aeStronglyMeasurable' := by
    have h1 := hf.aeStronglyMeasurable'
    apply MeasureTheory.AEStronglyMeasurable.comp_aemeasurable
    · rw [Measure.IsAddRightInvariant.map_add_right_eq_self c]
      fun_prop
    · fun_prop

lemma const_smul {d} {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (c • f) where
  integrable_space' η := by
    simp
    conv_lhs =>
      enter [x]
      rw [smul_comm]
    exact (hf.integrable_space' η).smul c
  integrable_time_space' η := by
    simp
    conv_lhs =>
      enter [x]
      rw [smul_comm]
    exact (hf.integrable_time_space' η).smul c
  aeStronglyMeasurable' := by
    apply MeasureTheory.AEStronglyMeasurable.smul
    · fun_prop
    · fun_prop

lemma const_mul_fun {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c * f x) := by
  convert hf.const_smul c using 1

lemma mul_const_fun {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => f x * c) := by
  convert hf.const_smul c using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma congr_norm {d : ℕ} {f : Space d → F} {g : Space d → F'}
    (hf : IsDistBounded f) (hg : AEStronglyMeasurable g) (hfg : ∀ x, ‖g x‖ = ‖f x‖) :
    IsDistBounded g where
  integrable_space' η := by
    apply (hf.integrable_space' η).congr'
    · fun_prop
    · filter_upwards with x
      simp [norm_smul, hfg]
  integrable_time_space' η := by
    apply (hf.integrable_time_space' η).congr'
    · apply AEStronglyMeasurable.smul
      · fun_prop
      · apply MeasureTheory.AEStronglyMeasurable.comp_snd
        fun_prop
    · filter_upwards with x
      simp [norm_smul, hfg]
  aeStronglyMeasurable' := hg

open InnerProductSpace

lemma inner_left {d n} {f : Space d → EuclideanSpace ℝ (Fin n) }
    (hf : IsDistBounded f) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ) where
  integrable_space' η := by
    have h1 : (fun x => η x • ⟪f x, y⟫_ℝ)  = (fun x => ⟪η x • f x, y⟫_ℝ) := by
      simp [inner_smul_left]
    rw [h1]
    exact (hf.integrable_space' η).inner_const y
  integrable_time_space' η := by
    have h1 : (fun x : Time × Space d => η x • ⟪f x.2, y⟫_ℝ) =
        (fun x : Time × Space d => ⟪η x • f x.2, y⟫_ℝ) := by
      simp [inner_smul_left]
    rw [h1]
    exact (hf.integrable_time_space' η).inner_const y
  aeStronglyMeasurable' := by
    apply MeasureTheory.AEStronglyMeasurable.inner_const
    fun_prop

@[fun_prop]
lemma zero {d}  : IsDistBounded (0 : Space d → F) where
  integrable_space' η := by
    simp
  integrable_time_space' η := by
    simp
  aeStronglyMeasurable' := by
    fun_prop

lemma sum {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (∑ i ∈ s, f i) := by
  classical
  induction' s using Finset.induction with i s hi ih
  · simp
    fun_prop
  rw [Finset.sum_insert]
  apply IsDistBounded.add
  · exact hf i (s.mem_insert_self i)
  · exact ih (fun j hj => hf j (s.mem_insert_of_mem hj))
  exact hi

lemma sum_fun {ι : Type*} {s : Finset ι} {d : ℕ}
    {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (fun x => ∑ i ∈ s, f i x) := by
  convert IsDistBounded.sum hf using 1
  funext x
  simp

/-!

## D. Special functions

-/

lemma nat_pow {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) := zpow (d := d) (n : ℤ) (by omega)

lemma add_const_zpow {d : ℕ} (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (v : Space d) :
    IsDistBounded (fun (x : Space d) => ‖x + v‖ ^ p) := (zpow p hp).comp_add_right v

lemma nat_pow_add_const {d : ℕ} (n : ℕ) (a : ℝ) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) := by
  conv =>
    enter [1, x]
    rw [add_pow]
  apply IsDistBounded.sum_fun
  intro i _
  apply IsDistBounded.mul_const_fun
  apply IsDistBounded.mul_const_fun
  exact nat_pow i

@[fun_prop]
lemma inv {d : ℕ}  : IsDistBounded (d := d.succ.succ) (fun x => ‖x‖⁻¹) := by
  convert zpow (d := d.succ.succ) (-1) (by simp) using 2
  simp

@[fun_prop]
lemma norm {d : ℕ} :
    IsDistBounded (d := d) (fun x => ‖x‖) := by
  convert zpow (d := d) 1 (by omega) using 2
  simp

lemma log_norm {d : ℕ} :
    IsDistBounded (d := d.succ.succ) (fun x => Real.log ‖x‖) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖⁻¹ + ‖x‖)
  · fun_prop
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    have h1 := Real.neg_inv_le_log (x := ‖x‖) (by positivity)
    have h2 := Real.log_le_rpow_div (x := ‖x‖) (by positivity) (ε := 1) (by positivity)
    simp_all
    rw [abs_le']
    generalize  Real.log ‖x‖ = r at *
    apply And.intro
    · apply h2.trans
      simp
    · rw [neg_le]
      apply le_trans _ h1
      simp

/-!

## E. Integrability with respect to powers
-/

lemma norm_inv_mul_exists_pow_integrable {d : ℕ}
    (f : Space d → F) (hf : IsDistBounded f) :
    ∃ r, Integrable (fun x => ‖f x‖ * ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
  sorry
end IsDistBounded
end Space
