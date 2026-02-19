/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Basic
import PhysLean.SpaceAndTime.Space.Integrals.Basic
/-!

# The radial angular measure on Space

## i. Overview

The normal measure on `Space d` is `r^(d-1) dr dΩ` in spherical coordinates,
where `dΩ` is the angular measure on the unit sphere. The radial angular measure
is the measure `dr dΩ`, cancelling the radius contribution from the measure in spherical
coordinates.

This file is equivalent to `invPowMeasure`, which will slowly be deprecated.

## ii. Key results

- `radialAngularMeasure`: The radial angular measure on `Space d`.

## iii. Table of contents

- A. The definition of the radial angular measure
  - A.1. Basic equalities
- B. Integrals with respect to radialAngularMeasure
- C. The radialAngularMeasure on balls
- D. Integrability conditions
- E. HasTemperateGrowth of measures
  - E.1. Integrability of powers
  - E.2. radialAngularMeasure has temperate growth

## iv. References

-/
open SchwartzMap NNReal Real
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The definition of the radial angular measure

-/

/-- The measure on `Space d` weighted by `1 / ‖x‖ ^ (d - 1)`. -/
def radialAngularMeasure {d : ℕ} : Measure (Space d) :=
  volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)))

/-!

### A.1. Basic equalities

-/

lemma radialAngularMeasure_eq_volume_withDensity {d : ℕ} : radialAngularMeasure =
    volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1))) := by
  rfl

@[simp]
lemma radialAngularMeasure_zero_eq_volume :
    radialAngularMeasure (d := 0) = volume := by
  simp [radialAngularMeasure]

/-!

### A.2. SFinite property

-/

instance (d : ℕ) : SFinite (radialAngularMeasure (d := d)) := by
  dsimp [radialAngularMeasure]
  infer_instance

/-!

## B. Integrals with respect to radialAngularMeasure

-/

lemma integral_radialAngularMeasure {d : ℕ} (f : Space d → F) :
    ∫ x, f x ∂radialAngularMeasure = ∫ x, (1 / ‖x‖ ^ (d - 1)) • f x := by
  dsimp [radialAngularMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  simp only [one_div]
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

lemma lintegral_radialMeasure {d : ℕ} (f : Space d → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂radialAngularMeasure = ∫⁻ x, ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)) * f x := by
  dsimp [radialAngularMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul]
  simp only [one_div, Pi.mul_apply]
  · fun_prop
  · fun_prop

lemma lintegral_radialMeasure_eq_spherical_mul (d : ℕ) (f : Space d.succ → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂radialAngularMeasure = ∫⁻ x, f (x.2.1 • x.1.1)
      ∂(volume (α := Space d.succ).toSphere.prod (Measure.volumeIoiPow 0)) := by
  rw [lintegral_radialMeasure, lintegral_volume_eq_spherical_mul]
  apply lintegral_congr_ae
  filter_upwards with x
  have hx := x.2.2
  simp [Nat.succ_eq_add_one, -Subtype.coe_prop] at hx
  simp [norm_smul]
  rw [abs_of_nonneg (le_of_lt x.2.2)]
  trans ENNReal.ofReal (↑x.2 ^ d * (x.2.1 ^ d)⁻¹) * f (x.2.1 • ↑x.1.1)
  · rw [ENNReal.ofReal_mul]
    ring
    have h2 := x.2.2
    simp at h2
    positivity
  trans ENNReal.ofReal 1 * f (x.2.1 • ↑x.1.1)
  · congr
    field_simp
  simp only [ENNReal.ofReal_one, Nat.succ_eq_add_one, one_mul]
  fun_prop
  fun_prop

/-!

## C. The radialAngularMeasure on balls

-/

@[simp]
lemma radialAngularMeasure_closedBall (r : ℝ) :
    radialAngularMeasure (Metric.closedBall (0 : Space 3) r) = ENNReal.ofReal (4 * π * r) := by
  rw [← setLIntegral_one, ← MeasureTheory.lintegral_indicator,
    lintegral_radialMeasure_eq_spherical_mul]
  rotate_left
  · refine (measurable_indicator_const_iff 1).mpr ?_
    exact measurableSet_closedBall
  · exact measurableSet_closedBall
  have h1 (x : (Metric.sphere (0 : Space) 1) × ↑(Set.Ioi (0 : ℝ))) :
      (Metric.closedBall (0 : Space) r).indicator (fun x => (1 : ENNReal)) (x.2.1 • x.1.1) =
      (Set.univ ×ˢ {a | a.1 ≤ r}).indicator (fun x => 1) x := by
    refine Set.indicator_const_eq_indicator_const ?_
    simp [norm_smul]
    rw [abs_of_nonneg (le_of_lt x.2.2)]
  simp [h1]
  rw [MeasureTheory.lintegral_indicator, setLIntegral_one]
  rotate_left
  · refine MeasurableSet.prod ?_ ?_
    · exact MeasurableSet.univ
    · simp
      fun_prop
  rw [MeasureTheory.Measure.prod_prod]
  simp [Measure.volumeIoiPow]
  rw [MeasureTheory.Measure.comap_apply]
  rotate_left
  · exact Subtype.val_injective
  · intro s hs
    refine MeasurableSet.subtype_image ?_ hs
    exact measurableSet_Ioi
  · simp
    fun_prop
  trans 3 * ENNReal.ofReal (4 / 3 * π) * volume (α := ℝ) (Set.Ioc 0 r)
  · congr
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_Ioi, exists_and_left,
      exists_prop, exists_eq_right_right, Set.mem_Ioc]
    grind
  simp only [volume_Ioc, sub_zero]
  trans ENNReal.ofReal (3 * ((4 / 3 * π))) * ENNReal.ofReal r
  · simp [ENNReal.ofReal_mul]
  field_simp
  rw [← ENNReal.ofReal_mul]
  simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
  positivity

lemma radialAngularMeasure_real_closedBall (r : ℝ) (hr : 0 < r) :
    radialAngularMeasure.real (Metric.closedBall (0 : Space 3) r) = 4 * π * r := by
  change (radialAngularMeasure (Metric.closedBall (0 : Space 3) r)).toReal = _
  simp only [radialAngularMeasure_closedBall, ENNReal.toReal_ofReal_eq_iff]
  positivity

/-!

## D. Integrability conditions

-/

lemma integrable_radialAngularMeasure_iff {d : ℕ} {f : Space d → F} :
    Integrable f (radialAngularMeasure (d := d)) ↔
      Integrable (fun x => (1 / ‖x‖ ^ (d - 1)) • f x) volume := by
  dsimp [radialAngularMeasure]
  erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)]
  simp only [one_div]
  refine integrable_congr ?_
  filter_upwards with x
  rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
  simp only [inv_nonneg, norm_nonneg, pow_nonneg, coe_mk]
  positivity

omit [NormedSpace ℝ F] in
lemma integrable_radialAngularMeasure_of_spherical {d : ℕ} (f : Space d.succ → F)
    (fae : AEStronglyMeasurable f radialAngularMeasure)
    (ht : StronglyMeasurable f)
    (hf : Integrable (fun x => f (x.2.1 • x.1.1))
    (volume (α := Space d.succ).toSphere.prod (Measure.volumeIoiPow 0))) :
    Integrable f radialAngularMeasure := by
  have h1 := hf.1
  have h2 := hf.2
  refine ⟨fae, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    rw [lintegral_radialMeasure_eq_spherical_mul]
    rw [← hasFiniteIntegral_iff_norm]
    exact h2
    · simp
      refine StronglyMeasurable.enorm ht

/-!

## E. HasTemperateGrowth of measures

-/

/-!

### E.1. Integrability of powers

-/
private lemma integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
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
    simp only [neg_add_rev, Real.one_rpow, mul_one]
    field_simp
    ring
    linarith
    linarith
  · simp
  · simp
  · simp

lemma radialAngularMeasure_integrable_pow_neg_two {d : ℕ} :
    Integrable (fun x : Space d => (1 + ‖x‖) ^ (- (d + 1) : ℝ))
      radialAngularMeasure := by
  match d with
  | 0 => simp
  | dm1 + 1 =>
  apply integrable_radialAngularMeasure_of_spherical
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · fun_prop
  simp [norm_smul]
  rw [MeasureTheory.integrable_prod_iff]
  rotate_left
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  refine ⟨?_, by simp⟩
  filter_upwards with x
  simp [Measure.volumeIoiPow]
  let f := fun x : ℝ => |(1 + x) ^ (- (dm1 + 2) : ℝ)|
  have h0 : (fun (y : ↑(Set.Ioi 0)) => (1 + |y.1|) ^ (-1 + (-1 + -↑dm1) : ℝ)) =
      f ∘ Subtype.val := by
    funext x
    rcases x with ⟨x, hx⟩
    simp at hx
    simp [f]
    ring_nf
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [h0]
  change Integrable (f ∘ Subtype.val) _
  rw [← MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  exact integrable_neg_pow_on_ioi dm1

/-!

### E.2. radialAngularMeasure has temperate growth

-/

instance (d : ℕ) : Measure.HasTemperateGrowth (radialAngularMeasure (d := d)) where
  exists_integrable := by
    use d + 1
    simpa using radialAngularMeasure_integrable_pow_neg_two (d := d)

end Space
