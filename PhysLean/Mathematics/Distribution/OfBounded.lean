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

In this module we define distributions from functions `f : EuclideanSpace ℝ (Fin d.succ) → F`
whose norm is bounded by `c1 * ‖x‖ ^ (-d : ℝ) + c2 * ‖x‖ ^ n`
for some constants `c1`, `c2` and `n`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## Key definition

- `ofBounded`: Creates a distribution from a bounded function `f`.

## Method of definition

The `ofBounded` function is defined through two measures `invPowMeasure` and `powMeasure n`,
the first is the measure with density `1/‖x‖ᵈ` and the second is the measure with density `‖x‖^n`.
Both these measures are proven to have temperate growth, and can be used to define a distribution
by intergration.

We also define a `boundMeasure` which is a linear combination of these two measures.

-/
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
def invPowMeasure {dm1 : ℕ} : Measure (EuclideanSpace ℝ (Fin dm1.succ)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin dm1.succ) => ENNReal.ofReal (1 / ‖x‖ ^ dm1))

/-- The measure on `EuclideanSpace ℝ (Fin 3)` weighted by `‖x‖ ^ n`. -/
def powMeasure {dm1 : ℕ} (n : ℕ) : Measure (EuclideanSpace ℝ (Fin dm1.succ)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin dm1.succ) =>
    ENNReal.ofReal (‖x‖ ^ n))

/-- The measure on `EuclideanSpace ℝ (Fin 3)` given by `C1 • invPowMeasure + C2 • powMeasure n`,
  for constants `C1` and `C2`. -/
def boundMeasure {dm1 : ℕ} (n : ℕ) (C1 C2 : ℝ) :
    Measure (EuclideanSpace ℝ (Fin dm1.succ)) :=
  (ENNReal.ofReal C1) • invPowMeasure +
  (ENNReal.ofReal C2) • powMeasure n

/-!

## Integrable conditions for the measures.

-/

variable [NormedSpace ℝ F]

lemma integrable_boundMeasure {dm1 : ℕ} (n : ℕ) (C1 C2 : ℝ) (C1_nonneg : 0 ≤ C1)
    (C2_nonneg : 0 ≤ C2)
    (f : EuclideanSpace ℝ (Fin dm1.succ) → F) (h : Integrable f (boundMeasure n C1 C2)) :
    Integrable (fun x => (C1 * (1/‖x‖^dm1) + C2 * ‖x‖^n) • f x) := by
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
      simp only [one_div, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_toRealHom,
        Real.coe_toNNReal', inv_nonneg, norm_nonneg, pow_nonneg, sup_of_le_left]
      fun_prop
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
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
      refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_toRealHom, Real.coe_toNNReal',
        norm_nonneg, pow_nonneg, sup_of_le_left]
      fun_prop
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
      simp
    · fun_prop
    · simp

/-!

## Integrals with respect to the measures.

-/

lemma integral_invPowMeasure {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F) :
    ∫ x, f x ∂invPowMeasure = ∫ x, (1 / ‖x‖^dm1) • f x := by
  dsimp [invPowMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  simp only [one_div]
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

lemma integral_powMeasure {dm1 : ℕ} (n : ℕ) (f : EuclideanSpace ℝ (Fin dm1.succ) → F) :
    ∫ x, f x ∂(powMeasure n) = ∫ x, (‖x‖ ^ n) • f x := by
  dsimp [powMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

lemma integral_boundMeasure {dm1 : ℕ} (n : ℕ) (C1 C2 : ℝ) (C1_nonneg : 0 ≤ C1) (C2_nonneg : 0 ≤ C2)
    (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : Integrable f (boundMeasure n C1 C2)) :
    ∫ x, f x ∂(boundMeasure n C1 C2) = ∫ x, (C1 * 1/‖x‖^dm1 + C2 * ‖x‖^n) • f x := by
  dsimp [boundMeasure] at ⊢ hf
  rw [integrable_add_measure] at hf
  rw [MeasureTheory.integral_add_measure hf.1 hf.2]
  rw [integral_smul_measure, ← integral_smul, integral_smul_measure, ← integral_smul]
  rw [integral_invPowMeasure, integral_powMeasure]
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
    dsimp [invPowMeasure] at h1
    rw [integrable_smul_measure] at h1
    erw [integrable_withDensity_iff_integrable_smul₀] at h1
    refine (integrable_congr ?_).mp h1
    filter_upwards with x
    simp only [one_div]
    refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_toRealHom, Real.coe_toNNReal',
      inv_nonneg, norm_nonneg, pow_nonneg, sup_of_le_left]
    fun_prop
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
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
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_toRealHom, Real.coe_toNNReal',
      norm_nonneg, pow_nonneg, sup_of_le_left]
    fun_prop
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
    simp

/-!

## HasTemperateGrowth of measures

-/

private lemma integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
  rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
  rw [← MeasureTheory.integrable_smul_measure (c := n + 1)]
  apply MeasureTheory.integrable_of_integral_eq_one
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (- (n + 2) : ℝ)) ∂volume
  · rw [← MeasureTheory.integral_subtype_comap]
    simp only [neg_add_rev, Function.comp_apply, integral_smul_measure, smul_eq_mul]
    congr
    funext x
    simp only [abs_eq_self]
    apply Real.rpow_nonneg
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt x.2
    exact measurableSet_Ioi
  have h0 (x : ℝ) (hx : x ∈ Set.Ioi 0) : ((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ) =
      ((1 + x) ^ ((n + 2)))⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.inv_rpow]
    rw [← Real.rpow_neg_one, ← Real.rpow_mul]
    simp only [neg_mul, one_mul]
    simp only [neg_add_rev, Nat.cast_add, Nat.cast_ofNat]
    have hx : 0 < x := hx
    positivity
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt hx
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (n + 2))⁻¹ ∂volume
  · congr 1
    refine setIntegral_congr_ae₀ ?_ ?_
    · simp
    filter_upwards with x hx
    rw [h0 x hx]
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (n + 2))⁻¹ ∂volume
  · congr 1
    let f := fun x : ℝ => (x ^ (n + 2))⁻¹
    change ∫ (x : ℝ) in Set.Ioi 0, f (1 + x) ∂volume = ∫ (x : ℝ) in Set.Ioi 1, f x ∂volume
    let fa := fun x : ℝ => 1 + x
    change ∫ (x : ℝ) in Set.Ioi 0, f (fa x) ∂volume = _
    rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb (ν := volume)]
    simp [fa]
    simp [fa]
    exact measurePreserving_add_left volume 1
    simp [fa]
    exact measurableEmbedding_addLeft 1
  · trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (- (n + 2) : ℝ)) ∂volume
    · congr 1
      refine setIntegral_congr_ae₀ ?_ ?_
      · simp
      filter_upwards with x hx
      have hx : 1 < x := hx
      rw [← Real.rpow_natCast]
      rw [← Real.inv_rpow]
      rw [← Real.rpow_neg_one, ← Real.rpow_mul]
      simp only [neg_mul, one_mul]
      simp only [Nat.cast_add, Nat.cast_ofNat, neg_add_rev]
      positivity
      positivity

    rw [integral_Ioi_rpow_of_lt]
    field_simp
    have h0 : (-2 + -(n : ℝ) + 1) ≠ 0 := by
      by_contra h
      have h1 : (1 : ℝ) - 0 = 2 + n := by
        rw [← h]
        ring
      simp at h1
      linarith
    field_simp
    ring
    linarith
    linarith
  · simp
  · simp
  · simp

lemma invPowMeasure_integrable_pow_neg_two {dm1 : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin dm1.succ) => (1 + ‖x‖) ^ (- (dm1 + 2) : ℝ))
      invPowMeasure := by
  simp [invPowMeasure]
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
    (volume (α := EuclideanSpace ℝ (Fin dm1.succ))))
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin dm1.succ) =>
      ((1 + ‖x‖) ^ (- (dm1 + 2) : ℝ)) * (‖x‖ ^ dm1)⁻¹) {0}ᶜ := by
    rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
    swap
    · refine MeasurableSet.compl_iff.mpr ?_
      simp
    let f := (fun x : EuclideanSpace ℝ (Fin dm1.succ) =>
        ((1 + ‖x‖) ^ (- (dm1 + 2) : ℝ)) * (‖x‖ ^ dm1)⁻¹)
      ∘ @Subtype.val (EuclideanSpace ℝ (Fin dm1.succ)) fun x =>
        (@Membership.mem (EuclideanSpace ℝ (Fin dm1.succ))
          (Set (EuclideanSpace ℝ (Fin dm1.succ))) Set.instMembership {0}ᶜ x)
    have hf : (f ∘ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin dm1.succ))).symm)∘
      (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin dm1.succ))) = f := by
      funext x
      simp
    change Integrable f _
    rw [← hf]
    refine (h1.integrable_comp_emb ?_).mpr ?_
    · exact Homeomorph.measurableEmbedding
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin dm1.succ)))
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
        simp only [Set.image_univ, Subtype.range_coe_subtype, Set.mem_Ioi]
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
    have hf' : (f ∘ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin dm1.succ))).symm) =
      fun x =>((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) * (x.2.val ^ dm1)⁻¹ := by
      funext x
      simp only [Function.comp_apply, homeomorphUnitSphereProd_symm_apply_coe, f]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
      rw [abs_of_nonneg (le_of_lt x.2.2)]
    rw [hf']
    simp [Measure.volumeIoiPow]
    rw [MeasureTheory.prod_withDensity_right]
    swap
    · fun_prop
    rw [MeasureTheory.integrable_withDensity_iff]
    swap
    · refine Measurable.ennreal_ofReal ?_
      refine Measurable.pow_const ?_ dm1
      apply Measurable.comp
      · exact measurable_subtype_coe
      · exact measurable_snd
    swap
    · apply Filter.Eventually.of_forall
      intro x
      exact ENNReal.ofReal_lt_top
    have hf'' : (fun (x : ↑(Metric.sphere (α := (EuclideanSpace ℝ (Fin dm1.succ))) 0 1) ×
        ↑(Set.Ioi (α := ℝ) 0)) =>
        (((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) * (x.2.val ^ dm1)⁻¹ *
          (ENNReal.ofReal (↑x.2.val ^ dm1)).toReal))
        = fun x => ((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) := by
      funext x
      rw [ENNReal.toReal_ofReal]
      generalize (1 + ↑x.2.val)= l
      ring_nf
      have h2 : x.2.val ≠ 0 := by
        have h' := x.2.2
        simp [- Subtype.coe_prop] at h'
        linarith
      field_simp
      ring_nf
      field_simp
      exact pow_nonneg (le_of_lt x.2.2) dm1
    simp at hf''
    rw [hf'']
    apply (MeasureTheory.integrable_prod_iff' ?_).mpr ?_
    · refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
      fun_prop
    · simp
      apply Integrable.const_mul
      have h1 := integrable_neg_pow_on_ioi dm1
      rw [MeasureTheory.integrableOn_iff_comap_subtypeVal] at h1
      simpa using h1
      exact measurableSet_Ioi
  rw [← MeasureTheory.integrableOn_univ]
  simp at h2
  apply MeasureTheory.IntegrableOn.congr_set_ae h2
  rw [← MeasureTheory.ae_eq_set_compl]
  trans (∅ : Set (EuclideanSpace ℝ (Fin dm1.succ)))
  · apply Filter.EventuallyEq.of_eq
    rw [← Set.compl_empty]
    exact compl_compl _
  · symm
    simp

instance (dm1 : ℕ) : Measure.HasTemperateGrowth (invPowMeasure (dm1 := dm1)) where
  exists_integrable := by
    use dm1 + 2
    simpa using invPowMeasure_integrable_pow_neg_two (dm1 := dm1)

instance (dm1 : ℕ) (n : ℕ) : Measure.HasTemperateGrowth (powMeasure (dm1 := dm1) n) where
  exists_integrable := by
    let m := (volume (α := EuclideanSpace ℝ (Fin dm1.succ))).integrablePower
    use (m + n)
    simp only [powMeasure]
    rw [MeasureTheory.integrable_withDensity_iff]
    have h1 : (fun x : EuclideanSpace ℝ (Fin dm1.succ) =>
        (1 + ‖x‖) ^ (- (m + n : ℝ)) * (ENNReal.ofReal (‖x‖ ^ n)).toReal)
      = fun x => ‖x‖ ^ n * ‖(1 + ‖x‖) ^ (-(m + n : ℝ))‖ := by
      funext x
      simp only [neg_add_rev, norm_nonneg, pow_nonneg, ENNReal.toReal_ofReal, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      ring
    simp only [Nat.cast_add, neg_add_rev, norm_nonneg, pow_nonneg, ENNReal.toReal_ofReal]
    conv_lhs at h1 =>
      simp only [neg_add_rev, norm_nonneg, pow_nonneg, ENNReal.toReal_ofReal]
    rw [h1]
    apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ := 1)
    · intro x
      simp only [neg_add_rev, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
      · rw [@le_add_iff_nonneg_right]
        exact norm_nonneg x
      · refine neg_add_nonpos_iff.mpr ?_
        refine neg_le_iff_add_nonneg.mpr ?_
        positivity
    · intro x
      simp [- neg_add_rev, Real.norm_eq_abs]
      have h1 : (1 + ‖x‖) ^ (-((m : ℝ) + ↑n)) = ((1 + ‖x‖) ^ (m + n))⁻¹ := by
        have h0 : (1 + ‖x‖) ^ (m + n) = (1 + ‖x‖) ^ (m + n : ℝ) := by
          rw [← Real.rpow_natCast]
          simp
        rw [h0]
        rw [← Real.inv_rpow]
        rw [← Real.rpow_neg_one, ← Real.rpow_mul]
        simp only [neg_add_rev, neg_mul, one_mul]
        positivity
        positivity
      rw [h1]
      rw [abs_of_nonneg (by positivity)]
      refine mul_inv_le_one_of_le₀ ?_ ?_
      simp [m]
      conv_lhs => enter [2]; rw [add_comm]
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
        simp only [ne_eq]
        have h1 : 0 < 1 + ‖x‖ := by
          positivity
        by_contra hn
        rw [hn] at h1
        simp at h1
    · fun_prop
    · filter_upwards with x
      simp

instance (dm1 : ℕ) (n : ℕ) (C1 C2 : ℝ) :
    Measure.HasTemperateGrowth (boundMeasure (dm1 := dm1) n C1 C2) where
  exists_integrable := by
    let m1 := (invPowMeasure (dm1 := dm1)).integrablePower
    let m2 := (powMeasure (dm1 := dm1) n).integrablePower
    use max m1 m2
    simp [boundMeasure]
    have h1 : (fun x : EuclideanSpace ℝ (Fin dm1.succ) => (1 + ‖x‖) ^ (- max m1 m2 : ℝ)) =
        fun x => ‖x‖ ^ 0 * ‖(1 + ‖x‖) ^ (-max m1 m2 : ℝ)‖ := by
      funext x
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      rw [Real.rpow_neg]
      ring
      positivity
    have h0 (x : EuclideanSpace ℝ (Fin dm1.succ)) : (1 + ‖x‖) ^ (-max ↑m1 ↑m2 : ℝ) =
        ((1 + ‖x‖) ^ (max m1 m2))⁻¹ := by
      rw [← Real.rpow_natCast]
      simp only [Nat.cast_max]
      rw [← Real.inv_rpow]
      rw [← Real.rpow_neg_one, ← Real.rpow_mul]
      simp only [neg_mul, one_mul]
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
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        refine le_add_of_le_of_nonneg ?_ ?_
        · rfl
        · positivity
        simp
      · intro x
        simp only [zero_add, Nat.cast_max, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        rw [h0]
        refine mul_inv_le_one_of_le₀ ?_ ?_
        · trans (1 + ‖x‖) ^ (invPowMeasure (dm1 := dm1)).integrablePower
          · by_cases hm : (invPowMeasure (dm1 := dm1)).integrablePower = 0
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
            simp only [Real.log_pow, Nat.cast_max]
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
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        refine le_add_of_le_of_nonneg ?_ ?_
        · rfl
        · positivity
        simp
      · intro x
        simp only [zero_add, Nat.cast_max, Real.norm_eq_abs, m2, m1]
        rw [abs_of_nonneg (by positivity)]
        rw [h0]
        refine mul_inv_le_one_of_le₀ ?_ ?_
        · trans (1 + ‖x‖) ^ (powMeasure (dm1 := dm1) n).integrablePower
          · by_cases hm : (powMeasure (dm1 := dm1) n).integrablePower = 0
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
            simp only [Real.log_pow, Nat.cast_max, m2, m1]
            refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
            · simp
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

lemma bounded_integrable {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : ∃ c1 c2 n, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ x, ‖f x‖ ≤ c1 * ‖x‖ ^ (-dm1 : ℝ) + c2 * ‖x‖^n)
    (hae: AEStronglyMeasurable (fun x => f x) volume)
    (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin dm1.succ) => η x • f x) := by
  rw [← MeasureTheory.integrable_norm_iff]
  · conv =>
      enter [1, a]
      rw [norm_smul]
    obtain ⟨c1, c2, n, c1_nonneg, c2_nonneg, hbound⟩ := hf
    apply Integrable.mono (g := fun x => ‖η x‖ * (c1 * ‖x‖ ^ (-dm1 : ℝ) + c2 * ‖x‖^n))
    conv =>
      enter [1, a]
      rw [mul_add]
    apply MeasureTheory.Integrable.add
    · have h2 : (fun a => ‖η a‖ * (c1 * ‖a‖ ^ (-dm1 : ℝ))) =
          (fun a => c1 * (‖a‖ ^ (-dm1 : ℝ) * ‖η a‖)) := by
        funext a
        ring
      rw [h2]
      apply Integrable.const_mul
      have h3 : Integrable (fun x => η x) invPowMeasure := by
        exact integrable η
      rw [← MeasureTheory.integrable_norm_iff (by fun_prop)] at h3
      simp only [invPowMeasure] at h3
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
      simp only [Real.norm_eq_abs, norm_mul, abs_abs]
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · rfl
      · simp only [abs_norm]
        apply (hbound x).trans
        apply le_of_eq
        rw [abs_of_nonneg]
        apply add_nonneg
        · apply mul_nonneg
          · exact c1_nonneg
          · apply Real.rpow_nonneg
            exact norm_nonneg x
        apply mul_nonneg
        · exact c2_nonneg
        · refine pow_nonneg ?_ n
          exact norm_nonneg x
      · exact abs_nonneg (η x)
      · exact abs_nonneg _
  · fun_prop

/-- A distribution `(EuclideanSpace ℝ (Fin 3)) →d[ℝ] F` from a function
  `f : EuclideanSpace ℝ (Fin 3) → F` bounded by `c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖ ^ n`.
-/
def ofBounded {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : ∃ c1 c2 n, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ x, ‖f x‖ ≤ c1 * ‖x‖ ^ (-dm1 : ℝ) + c2 * ‖x‖ ^ n)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    (EuclideanSpace ℝ (Fin dm1.succ)) →d[ℝ] F := by
  refine mkCLMtoNormedSpace (fun η => ∫ x, η x • f x) ?_ ?_ ?_
  · intro η κ
    simp only [add_apply]
    conv_lhs =>
      enter [2, a]
      rw [add_smul]
    rw [integral_add]
    · exact bounded_integrable f hf hae η
    · exact bounded_integrable f hf hae κ
  · intro a η
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_lhs =>
      enter [2, a]
      rw [← smul_smul]
    rw [integral_smul]
  obtain ⟨c1, c2, r, c1_nonneg, c2_nonneg, hbound⟩ := hf
  haveI hμ : (boundMeasure (dm1 := dm1) r c1 c2).HasTemperateGrowth := by infer_instance
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(boundMeasure (dm1 := dm1) r c1 c2)
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
      simp only [one_div, Real.norm_eq_abs, smul_eq_mul, mul_one, mul_eq_mul_right_iff,
        add_left_inj, abs_eq_zero]
      left
      exact rfl
    · filter_upwards with x
      rw [norm_smul, mul_comm]
      simp only [Real.norm_eq_abs, mul_one, smul_eq_mul]
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
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
  apply (integral_mono (by simpa using η.integrable_pow_mul ((boundMeasure r c1 c2)) 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

lemma ofBounded_apply {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : ∃ c1 c2 n, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ x, ‖f x‖ ≤ c1 * ‖x‖ ^ (-dm1 : ℝ) + c2 * ‖x‖ ^ n)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    ofBounded f hf hae η = ∫ x, η x • f x := rfl

@[simp]
lemma ofBounded_zero_eq_zero  {dm1 : ℕ} :
    ofBounded (fun _ : EuclideanSpace ℝ (Fin (dm1 + 1)) => (0 : F))
      ⟨0, 0, 0, by simp, by simp, by simp⟩ (by fun_prop) = 0 := by
  ext η
  simp [ofBounded_apply]

TODO "LQX64" "Show that the creation of a distribution
  from a bounded function via `ofBounded` is linear on adding two bounded functions.
  A necessary preliminary is to show that the sum of two bounded functions is bounded,
  this may require a modification of the definition of boundedness."

end Distribution
