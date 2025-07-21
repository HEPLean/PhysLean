/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
/-!

# Distributions from bounded functions

In this module we define distributions from functions `f : EuclideanSpace ℝ (Fin 3) → F`
whose norm is bounded by `c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖ ^ n`
for some constants `c1`, `c2` and `n`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## Key definition

- `ofBounded`: Creates a distribution from a bounded function `f`.

## Method of definition

The `ofBounded` function is defined through two measures `invSqMeasure` and `powMeasure n`,
the first is the measure with density `1/‖x‖²` and the second is the measure with density `‖x‖^n`.
Both these measures are proven to have temperate growth, and can be used to define a distribution
by intergration.

We also define a `boundMeasure` which is a linear combination of these two measures.

-/

TODO "H4EWQ" "The creation of distributions from bounded functions is defined only for
  `EuclideanSpace ℝ (Fin 3)`. This should be generalized to any `EuclideanSpace ℝ (Fin n)`,
  and possibly even more generalized then this. This should be fairly easy following the method
  given for `EuclideanSpace ℝ (Fin 3)`."

open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace Distribution


variable [NormedSpace ℝ E]

open MeasureTheory

/-!

## The measures.

-/

/-- The measure on `EuclideanSpace ℝ (Fin 3)` weighted by `1 / ‖x‖ ^ 2`. -/
def invSqMeasure : Measure (EuclideanSpace ℝ (Fin 3)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (1 / ‖x‖ ^ 2))

/-- The measure on `EuclideanSpace ℝ (Fin 3)` weighted by `‖x‖ ^ n`. -/
def powMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin 3) =>
    ENNReal.ofReal (‖x‖ ^ n))

/-- The measure on  `EuclideanSpace ℝ (Fin 3)` given by `C1 • invSqMeasure + C2 • powMeasure n`,
  for constants `C1` and `C2`. -/
def boundMeasure (n : ℕ) (C1 C2 : ℝ)  :
    Measure (EuclideanSpace ℝ (Fin 3)) :=
  (ENNReal.ofReal C1) • invSqMeasure +
  (ENNReal.ofReal C2) • powMeasure n

/-!

## Integrable conditions for the measures.

-/

variable [NormedSpace ℝ F]

lemma integrable_boundMeasure (n : ℕ) (C1 C2 : ℝ) (C1_nonneg : 0 ≤ C1) (C2_nonneg : 0 ≤ C2)
    (f : EuclideanSpace ℝ (Fin 3) → F) (h : Integrable f (boundMeasure n C1 C2)):
    Integrable (fun x => (C1 * (1/‖x‖^2) + C2 * ‖x‖^n) • f x)  := by
  conv =>
    enter [1, x]
    rw [add_smul]
    rw [← smul_smul, ← smul_smul]
  simp [boundMeasure] at h
  apply Integrable.add
  · by_cases hC1 : C1 = 0
    · subst hC1
      simp
    refine Integrable.essSup_smul ?_ ?_ ?_
    · have h1 := h.1
      rw [integrable_smul_measure] at h1
      erw [integrable_withDensity_iff_integrable_smul₀] at h1
      refine (integrable_congr ?_).mp h1
      filter_upwards with x
      refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
      simp
      fun_prop
      simp
      positivity
      simp
    · fun_prop
    · simp
  · by_cases hC2 : C2 = 0
    · subst hC2
      simp
    refine Integrable.essSup_smul ?_ ?_ ?_
    · have h1 := h.2
      rw [integrable_smul_measure] at h1
      erw [integrable_withDensity_iff_integrable_smul₀] at h1
      refine (integrable_congr ?_).mp h1
      filter_upwards with x
      refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ ( f x))
      simp
      fun_prop
      simp
      positivity
      simp
    · fun_prop
    · simp

/-!

## Integrals with respect to the measures.

-/

lemma integral_invSqMeasure (f : EuclideanSpace ℝ (Fin 3) → F) :
    ∫ x, f x ∂invSqMeasure = ∫ x, (1 / ‖x‖^2) • f x := by
  dsimp [invSqMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  simp
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

lemma integral_powMeasure (n : ℕ) (f : EuclideanSpace ℝ (Fin 3) → F) :
    ∫ x, f x ∂(powMeasure n) = ∫ x, (‖x‖ ^ n) • f x := by
  dsimp [powMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

lemma integral_boundMeasure (n : ℕ) (C1 C2 : ℝ) (C1_nonneg : 0 ≤ C1) (C2_nonneg : 0 ≤ C2)
    (f : EuclideanSpace ℝ (Fin 3) → F)
    (hf : Integrable f (boundMeasure n C1 C2)) :
    ∫ x, f x ∂(boundMeasure n C1 C2) = ∫ x,  (C1 * 1/‖x‖^2 + C2 * ‖x‖^n) • f x := by
  dsimp [boundMeasure] at ⊢ hf
  rw [integrable_add_measure] at hf
  rw [MeasureTheory.integral_add_measure hf.1 hf.2]
  rw [integral_smul_measure, ← integral_smul, integral_smul_measure, ← integral_smul]
  rw [integral_invSqMeasure, integral_powMeasure]
  rw [← integral_add]
  · congr
    funext x
    rw [ENNReal.toReal_ofReal C1_nonneg, ENNReal.toReal_ofReal C2_nonneg]
    rw [add_smul, smul_smul, smul_smul]
    ring_nf
  · conv =>
      enter [1, x]
      rw [smul_comm]
    by_cases hc : C1 = 0
    · subst hc
      simp
    apply Integrable.smul
    have h1 := hf.1
    dsimp [invSqMeasure] at h1
    rw [integrable_smul_measure] at h1
    erw [integrable_withDensity_iff_integrable_smul₀] at h1
    refine (integrable_congr ?_).mp h1
    filter_upwards with x
    simp
    refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
    simp
    fun_prop
    simp
    positivity
    simp
  · conv =>
      enter [1, x]
      rw [smul_comm]
    by_cases hc : C2 = 0
    · subst hc
      simp
    apply Integrable.smul
    have h1 := hf.2
    dsimp [powMeasure] at h1
    rw [integrable_smul_measure] at h1
    erw [integrable_withDensity_iff_integrable_smul₀] at h1
    refine (integrable_congr ?_).mp h1
    filter_upwards with x
    refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
    simp
    fun_prop
    simp
    positivity
    simp

/-!

## HasTemperateGrowth of measures

-/

lemma invSqMeasure_integrable_pow_neg_two :
    Integrable (fun x => (1 + ‖x‖) ^ (-2 : ℝ)) invSqMeasure := by
  simp [invSqMeasure]
  rw [MeasureTheory.integrable_withDensity_iff]
  swap
  · fun_prop
  swap
  · rw [@ae_iff]
    simp
  conv =>
    enter [1, i]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have h1 := (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := EuclideanSpace ℝ (Fin 3))))
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 3) =>  ((1 + ‖x‖) ^ 2)⁻¹ * (‖x‖ ^ 2)⁻¹) {0}ᶜ := by
    rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
    swap
    · refine MeasurableSet.compl_iff.mpr ?_
      simp
    let f := (fun x : EuclideanSpace ℝ (Fin 3) => ((1 + ‖x‖) ^ 2)⁻¹ * (‖x‖ ^ 2)⁻¹)
      ∘ @Subtype.val (EuclideanSpace ℝ (Fin 3)) fun x => (
        @Membership.mem (EuclideanSpace ℝ (Fin 3)) (Set (EuclideanSpace ℝ (Fin 3))) Set.instMembership {0}ᶜ x)
    have hf : (f ∘ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).symm)∘
      (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))) = f := by
      funext x
      simp
    change Integrable f _
    rw [← hf]
    refine (h1.integrable_comp_emb ?_).mpr ?_
    · exact Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)))
    haveI sfinite : SFinite (@Measure.comap ↑(Set.Ioi 0) ℝ Subtype.instMeasurableSpace
        Real.measureSpace.toMeasurableSpace Subtype.val volume) := by
      refine { out' := ?_ }
      have h1 := SFinite.out' (μ := volume (α := ℝ))
      obtain ⟨m, h⟩ := h1
      use fun n => Measure.comap Subtype.val (m n)
      apply And.intro
      · intro n
        refine (isFiniteMeasure_iff (Measure.comap Subtype.val (m n))).mpr ?_
        rw [MeasurableEmbedding.comap_apply]
        simp
        have hm := h.1 n
        exact measure_lt_top (m n) {x | 0 < x}
        exact MeasurableEmbedding.subtype_coe measurableSet_Ioi
      · ext s hs
        rw [MeasurableEmbedding.comap_apply, Measure.sum_apply]
        conv_rhs =>
          enter [1, i]
          rw [MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe measurableSet_Ioi)]
        have h2 := h.2
        rw [Measure.ext_iff'] at h2
        rw [← Measure.sum_apply]
        exact h2 (Subtype.val '' s)
        refine MeasurableSet.subtype_image measurableSet_Ioi hs
        exact hs
        exact MeasurableEmbedding.subtype_coe measurableSet_Ioi
    have hf' :  (f ∘ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).symm) =
      fun x =>((1 + x.2.val) ^ 2)⁻¹ * (x.2.val ^ 2)⁻¹  := by
      funext x
      simp only [Function.comp_apply, homeomorphUnitSphereProd_symm_apply_coe, f]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one, sq_abs, mul_eq_mul_right_iff,
        inv_inj, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, f]
      rw [abs_of_nonneg (le_of_lt x.2.2)]
      simp only [true_or, f]
    rw [hf']
    simp [Measure.volumeIoiPow]
    rw [MeasureTheory.prod_withDensity_right]
    swap
    · fun_prop
    rw [MeasureTheory.integrable_withDensity_iff ]
    swap
    · refine Measurable.ennreal_ofReal ?_
      refine Measurable.pow_const ?_ 2
      apply Measurable.comp
      · exact measurable_subtype_coe
      · exact measurable_snd
    swap
    · apply Filter.Eventually.of_forall
      intro x
      exact ENNReal.ofReal_lt_top
    have hf'' : (fun (x : ↑(Metric.sphere (α := (EuclideanSpace ℝ (Fin 3))) 0 1) × ↑(Set.Ioi (α := ℝ) 0)) => ( ((1 + x.2.val) ^ 2)⁻¹ * (x.2.val ^ 2)⁻¹ * (ENNReal.ofReal (↑x.2.val ^ 2)).toReal))
        = fun x =>  ((1 + x.2.val) ^ 2)⁻¹:= by
      funext x
      rw [ENNReal.toReal_ofReal]
      generalize (1 + ↑x.2.val) ^ 2 = l
      ring_nf
      have h2 : x.2.val ≠ 0 := by
        have h' := x.2.2
        simp  [- Subtype.coe_prop, f] at h'
        linarith
      field_simp
      ring_nf
      field_simp
      exact sq_nonneg _
    rw [hf'']
    apply (MeasureTheory.integrable_prod_iff' ?_).mpr ?_
    · refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
      fun_prop
    · simp
      apply Integrable.const_mul
      rw [← @Measure.Subtype.volume_def]
      apply MeasureTheory.integrable_of_integral_eq_one
      trans ∫ (x : ℝ ) in Set.Ioi 0, ((1 + x) ^ 2)⁻¹ ∂volume
      · rw [← MeasureTheory.integral_subtype_comap]
        rfl
        exact measurableSet_Ioi
      trans  ∫ (x : ℝ ) in Set.Ioi 1, (x ^ 2)⁻¹ ∂volume
      · let f := fun x : ℝ => (x ^ 2)⁻¹
        change ∫ (x : ℝ ) in Set.Ioi 0, f (1 + x) ∂volume   = ∫ (x : ℝ ) in Set.Ioi 1, f x ∂volume
        let fa := fun x : ℝ => 1 + x
        change  ∫ (x : ℝ ) in Set.Ioi 0, f (fa x) ∂volume  =  _
        rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb (ν := volume)]
        simp [fa]
        simp [fa]
        exact measurePreserving_add_left volume 1
        simp [fa]
        exact measurableEmbedding_addLeft 1
      · trans ∫ (x : ℝ) in Set.Ioi 1, (x ^ (-2 : ℝ)) ∂volume
        · simp
          rfl
        rw [integral_Ioi_rpow_of_lt ]
        field_simp
        norm_num
        linarith
        linarith
  rw [← MeasureTheory.integrableOn_univ]
  apply MeasureTheory.IntegrableOn.congr_set_ae h2
  rw [← MeasureTheory.ae_eq_set_compl]
  trans (∅  : Set (EuclideanSpace ℝ (Fin 3)))
  · apply Filter.EventuallyEq.of_eq
    rw [← Set.compl_empty]
    exact compl_compl _
  · symm
    simp

instance : Measure.HasTemperateGrowth invSqMeasure where
  exists_integrable := by
    use 2
    exact invSqMeasure_integrable_pow_neg_two

instance (n : ℕ) : Measure.HasTemperateGrowth (powMeasure n) where
  exists_integrable := by
    let m := (volume (α :=  EuclideanSpace ℝ (Fin 3))).integrablePower
    use (m + n)
    simp only [powMeasure]
    rw [MeasureTheory.integrable_withDensity_iff]
    have h1 : (fun x :  EuclideanSpace ℝ (Fin 3) => (1 + ‖x‖) ^ (- (m + n : ℝ)) * (ENNReal.ofReal (‖x‖ ^ n)).toReal)
      = fun x => ‖x‖ ^ n * ‖(1 + ‖x‖) ^ (-(m + n : ℝ))‖ := by
      funext x
      simp
      rw [abs_of_nonneg (by positivity)]
      ring
    simp
    conv_lhs at h1 =>
      simp only [neg_add_rev, norm_nonneg, pow_nonneg, ENNReal.toReal_ofReal]
    rw [h1]
    apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ := 1)
    · intro x
      simp
      rw [abs_of_nonneg (by positivity)]
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
      · rw [@le_add_iff_nonneg_right]
        exact norm_nonneg x
      · refine neg_add_nonpos_iff.mpr ?_
        refine neg_le_iff_add_nonneg.mpr ?_
        positivity
    · intro x
      simp  [- neg_add_rev, Real.norm_eq_abs]
      have h1 : (1 + ‖x‖) ^ (-((m : ℝ) + ↑n)) = ((1 + ‖x‖) ^ (m + n))⁻¹ := by
        have h0 : (1 + ‖x‖) ^ (m + n) = (1 + ‖x‖) ^ (m + n : ℝ) := by
          rw [← Real.rpow_natCast]
          simp
        rw [h0]
        rw [← Real.inv_rpow]
        rw [← Real.rpow_neg_one, ← Real.rpow_mul]
        simp
        positivity
        positivity
      rw [h1]
      rw [abs_of_nonneg (by positivity)]
      refine mul_inv_le_one_of_le₀ ?_ ?_
      simp [m]
      rw [add_comm]
      by_cases hm : m + n = 0
      · erw [hm]
        simp
      refine (pow_le_pow_iff_left₀ ?_ ?_ hm).mpr ?_
      · exact norm_nonneg x
      · positivity
      · refine le_add_of_nonneg_left ?_
        exact zero_le_one' ℝ
      · positivity
    · refine Continuous.aestronglyMeasurable ?_
      apply Continuous.rpow_const
      · fun_prop
      · intro x
        left
        simp
        have h1 : 0 < 1 + ‖x‖ := by
          positivity
        by_contra hn
        rw [hn] at h1
        simp at h1
    · fun_prop
    · filter_upwards with x
      simp

instance  (n : ℕ) (C1 C2 : ℝ)  : Measure.HasTemperateGrowth (boundMeasure n C1 C2) where
  exists_integrable := by
    let m1 := invSqMeasure.integrablePower
    let m2 := (powMeasure n).integrablePower
    use max m1 m2
    simp [boundMeasure]
    have h1 : (fun x : EuclideanSpace ℝ (Fin 3) => (1 + ‖x‖) ^ (- max m1 m2 : ℝ)) =
        fun x => ‖x‖ ^ 0 * ‖(1 + ‖x‖) ^ (-max m1 m2 : ℝ)‖ := by
      funext x
      simp only [Real.norm_eq_abs, norm_smul]
      rw [abs_of_nonneg (by positivity)]
      rw [Real.rpow_neg]
      ring
      positivity
    have h0 (x : EuclideanSpace ℝ (Fin 3) ): (1 + ‖x‖) ^ (-max ↑m1 ↑m2 : ℝ) = ((1 + ‖x‖) ^ (max m1 m2))⁻¹ := by
      rw [← Real.rpow_natCast]
      simp
      rw [← Real.inv_rpow]
      rw [← Real.rpow_neg_one, ← Real.rpow_mul]
      simp
      positivity
      positivity
    apply And.intro
    · refine Integrable.smul_measure ?_ ?_
      swap
      · simp
      conv_lhs at h1=>
        simp only [Nat.cast_max, Real.norm_eq_abs, one_mul]
      rw [h1]
      apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ := 1)
      · intro x
        simp only [Real.norm_eq_abs, norm_smul]
        rw [abs_of_nonneg (by positivity)]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        refine le_add_of_le_of_nonneg ?_ ?_
        · rfl
        · positivity
        simp
      · intro x
        simp
        rw [abs_of_nonneg (by positivity)]
        rw [h0]
        refine mul_inv_le_one_of_le₀ ?_ ?_
        · trans (1 + ‖x‖) ^ invSqMeasure.integrablePower
          · by_cases hm : invSqMeasure.integrablePower = 0
            · rw [hm]
              simp
            refine (pow_le_pow_iff_left₀ ?_ ?_ hm).mpr ?_
            · exact norm_nonneg x
            · positivity
            · refine le_add_of_nonneg_left ?_
              exact zero_le_one' ℝ
          · refine (Real.pow_le_iff_le_log ?_ ?_).mpr ?_
            · positivity
            · positivity
            simp
            refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
            · simp [m1, m2]
            · rfl
            · positivity
            · refine Real.log_nonneg ?_
              refine le_add_of_le_of_nonneg ?_ ?_
              · rfl
              · positivity
        · positivity
      refine Continuous.aestronglyMeasurable ?_
      apply Continuous.rpow_const
      · fun_prop
      · intro x
        left
        have h1 : 0 < 1 + ‖x‖ := by
          positivity
        by_contra hn
        rw [hn] at h1
        simp at h1
    · refine Integrable.smul_measure ?_ ?_
      swap
      · simp
      conv_lhs at h1=>
        simp only [Nat.cast_max, Real.norm_eq_abs, one_mul]
      rw [h1]
      apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ := 1)
      · intro x
        simp only [Real.norm_eq_abs, norm_smul]
        rw [abs_of_nonneg (by positivity)]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        refine le_add_of_le_of_nonneg ?_ ?_
        · rfl
        · positivity
        simp
      · intro x
        simp
        rw [abs_of_nonneg (by positivity)]
        rw [h0]
        refine mul_inv_le_one_of_le₀ ?_ ?_
        · trans (1 + ‖x‖) ^ (powMeasure n).integrablePower
          · by_cases hm : (powMeasure n).integrablePower = 0
            · rw [hm]
              simp
            refine (pow_le_pow_iff_left₀ ?_ ?_ hm).mpr ?_
            · exact norm_nonneg x
            · positivity
            · refine le_add_of_nonneg_left ?_
              exact zero_le_one' ℝ
          · refine (Real.pow_le_iff_le_log ?_ ?_).mpr ?_
            · positivity
            · positivity
            simp
            refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
            · simp [m1, m2]
            · rfl
            · positivity
            · refine Real.log_nonneg ?_
              refine le_add_of_le_of_nonneg ?_ ?_
              · rfl
              · positivity
        · positivity
      refine Continuous.aestronglyMeasurable ?_
      apply Continuous.rpow_const
      · fun_prop
      · intro x
        left
        have h1 : 0 < 1 + ‖x‖ := by
          positivity
        by_contra hn
        rw [hn] at h1
        simp at h1

/-!

## Bounded functions as distributions

-/

lemma bounded_integrable (f : EuclideanSpace ℝ (Fin 3) → F)
     (hf :  ∃ c1 c2 n, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ x, ‖f x‖ ≤ c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖^n)
     (hae: AEStronglyMeasurable (fun x => f x) volume)
    (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => η x • f x) := by
  rw [← MeasureTheory.integrable_norm_iff]
  · conv =>
      enter [1, a]
      rw [norm_smul]
    obtain ⟨c1, c2, n, c1_nonneg, c2_nonneg, hbound⟩ := hf
    apply Integrable.mono (g := fun x => ‖η x‖ * (c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖^n))
    conv =>
      enter [1, a]
      rw [mul_add]
    apply MeasureTheory.Integrable.add
    · have h2 : (fun a => ‖η a‖ * (c1 * ‖a‖ ^ (-2 : ℝ))) = (fun a => c1 * (‖a‖ ^ (-2 : ℝ) * ‖η a‖ )) := by
        funext a
        ring
      rw [h2]
      apply Integrable.const_mul
      have h3 : Integrable (fun x => η x) invSqMeasure := by
        exact integrable η
      rw [← MeasureTheory.integrable_norm_iff (by fun_prop)] at h3
      simp only [invSqMeasure] at h3
      erw [MeasureTheory.integrable_withDensity_iff_integrable_coe_smul₀] at h3
      simpa using h3
      · fun_prop
    · have h2 : (fun a => ‖η a‖ * (c2 * ‖a‖ ^ n)) = (fun a => c2 * (‖a‖ ^ n * ‖η a‖)) := by
        funext a
        ring
      rw [h2]
      apply Integrable.const_mul
      exact integrable_pow_mul volume η n
    · fun_prop
    · filter_upwards with x
      simp
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · rfl
      · apply (hbound x).trans
        apply le_of_eq
        rw [abs_of_nonneg]
        simp
        apply add_nonneg
        · apply mul_nonneg
          · exact c1_nonneg
          · refine inv_nonneg_of_nonneg ?_
            exact zpow_two_nonneg ‖x‖
        apply mul_nonneg
        · exact c2_nonneg
        · refine pow_nonneg ?_ n
          exact norm_nonneg x
      · exact abs_nonneg (η x)
      · exact abs_nonneg (c1 * (‖x‖ ^ 2)⁻¹ + c2 * ‖x‖ ^ n)
  · fun_prop

/-- A distribution `(EuclideanSpace ℝ (Fin 3)) →d[ℝ] F` from a function
  `f : EuclideanSpace ℝ (Fin 3) → F` bounded by `c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖ ^ n`.
-/
def ofBounded (f : EuclideanSpace ℝ (Fin 3) → F)
    (hf :  ∃ c1 c2 n, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ x, ‖f x‖ ≤ c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖ ^ n)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    (EuclideanSpace ℝ (Fin 3)) →d[ℝ] F := by
  refine mkCLMtoNormedSpace (fun η => ∫ x, η x • f x) ?_ ?_ ?_
  · intro η κ
    simp
    conv_lhs =>
      enter [2, a]
      rw [add_smul]
    rw [integral_add]
    · exact bounded_integrable f hf hae η
    · exact bounded_integrable f hf hae κ
  · intro a η
    simp
    conv_lhs =>
      enter [2, a]
      rw [← smul_smul]
    rw [integral_smul]
  obtain ⟨c1, c2, r, c1_nonneg, c2_nonneg, hbound⟩ := hf
  haveI hμ : (boundMeasure r c1 c2).HasTemperateGrowth := by infer_instance
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(boundMeasure r c1 c2)
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  trans ∫ x, ‖η x‖ ∂(boundMeasure r c1 c2)
  · have h1 : Integrable (fun x => η x) (boundMeasure r c1 c2) := by
        exact integrable η
    have h2 : Integrable (fun x => ‖η x‖) (boundMeasure r c1 c2) := by
        exact Integrable.norm h1
    rw [integral_boundMeasure]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      positivity
    · dsimp
      apply (integrable_congr ?_).mp
        (integrable_boundMeasure r c1 c2 c1_nonneg c2_nonneg (fun x => ‖η x‖) h2)
      filter_upwards with x
      simp
      left
      exact rfl
    · filter_upwards with x
      rw [norm_smul, mul_comm]
      simp
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · apply (hbound x).trans
        apply le_of_eq
        simp
        rfl
      · rfl
      · positivity
      · positivity
    · exact c1_nonneg
    · exact c2_nonneg
    · exact h2
  have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) η)) := by
    intro x
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
  apply (integral_mono (by simpa using η.integrable_pow_mul ((boundMeasure r c1 c2)) 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

end Distribution
