/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Surfaces.SphericalShell
import PhysLean.SpaceAndTime.Space.Translations
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
/-!

## Ring surface in `Space 3`

-/
open SchwartzMap NNReal
noncomputable section
open Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the ring surface

-/

/-- The map embedding the unit ring in `Space d.succ` into `Space d.succ`. -/
def ring : Metric.sphere (0 : Space 2) 1 → Space 3 := fun x =>
  (slice 2).symm (0, sphericalShell 1 x)

lemma ring_eq : ring = (slice 2).symm ∘ (fun x => (0, sphericalShell 1 x)) := rfl

lemma ring_injective : Function.Injective ring := by
  intro x y h
  simp [ring] at h
  exact sphericalShell_injective _ h

@[fun_prop]
lemma ring_continuous : Continuous ring := by
  apply Continuous.comp
  · fun_prop
  · fun_prop

lemma ring_measurableEmbedding : MeasurableEmbedding ring :=
  Continuous.measurableEmbedding ring_continuous ring_injective

@[simp]
lemma volume_range_ring : volume (Set.range ring) = 0 := by
  rw [ring_eq, Set.range_comp]
  trans (MeasureTheory.Measure.map (slice 2)  volume) (Set.range (fun x => ((0 : ℝ), sphericalShell 1 x)))
  · rw [MeasureTheory.Measure.map_apply_of_aemeasurable]
    congr
    rw [@ContinuousLinearEquiv.image_symm_eq_preimage]
    · fun_prop
    · refine measurableSet_range_of_continuous_injective ?_ ?_
      · fun_prop
      · intro x y h
        simp at h
        exact SetCoe.ext h
  rw [volume_map_slice_eq_prod]
  trans (volume.prod volume) ({(0 : ℝ)} ×ˢ Set.range (sphericalShell 1))
  · congr
    ext a
    grind
  simp

/-!

## B. The measure associated with the ring

-/

/-- The measure on `Space 3` corresponding to integration around a ring. -/
def ringMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map ring (MeasureTheory.Measure.toSphere volume)

instance ringMeasure_hasTemperateGrowth :
    ringMeasure.HasTemperateGrowth := by
  rw [ringMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

instance ringMeasure_prod_volume_hasTemperateGrowth :
    (ringMeasure.prod (volume (α := Space))).HasTemperateGrowth := by
  exact IsDistBounded.instHasTemperateGrowthProdProdOfOpensMeasurableSpace ringMeasure volume

instance ringMeasure_sFinite: SFinite ringMeasure := by
  rw [ringMeasure]
  exact Measure.instSFiniteMap volume.toSphere ring

instance ringMeasure_finite: IsFiniteMeasure ringMeasure := by
  rw [ringMeasure]
  exact Measure.isFiniteMeasure_map volume.toSphere ring

lemma integrable_ringMeasure_of_continuous (f : Space → ℝ) (hf : Continuous (f ∘ ring)) :
    Integrable f ringMeasure := by
  rw [ringMeasure]
  rw [MeasurableEmbedding.integrable_map_iff]
  · let f' : BoundedContinuousFunction (Metric.sphere (0 : Space 2) 1) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨f ∘ ring, hf⟩
    exact BoundedContinuousFunction.integrable _ f'
  · exact ring_measurableEmbedding


lemma ringMeasure_prod_volume_map :
    (ringMeasure.prod (volume (α := Space))).map (fun x : Space × Space => (x.1, x.2 + x.1))
     = (ringMeasure.prod (volume (α := Space))) := by
  refine (MeasureTheory.MeasurePreserving.skew_product (f := id) (g := fun x => fun y => y + x)
    ?_ ?_ ?_).map_eq
  · exact MeasurePreserving.id ringMeasure
  · fun_prop
  · filter_upwards with x
    exact Measure.IsAddRightInvariant.map_add_right_eq_self (x)

instance ringMeasure_prod_volume_weight_hasTemperateGrowth :
     ((ringMeasure.prod (volume (α := Space))).withDensity
      (fun (x : Space × Space) => ENNReal.ofReal (1 / ‖x.2 - x.1‖ ^ 2))).HasTemperateGrowth
      := by
  rw [← ringMeasure_prod_volume_map]
  have h1 : ((Measure.map (fun x => (x.1, x.2 + x.1)) (ringMeasure.prod volume)).withDensity fun x =>
    ENNReal.ofReal (1 / ‖x.2 - x.1‖ ^ 2)) =
    ((((ringMeasure.prod volume)).withDensity fun x =>
    ENNReal.ofReal (1 / ‖x.2‖ ^ 2))).map (fun x => (x.1, x.2 + x.1)) := by
    ext s hs
    rw [withDensity_apply]
    let f' : (Space × Space) ≃ᵐ (Space × Space) :=
      { toFun := fun x => (x.1, x.2 + x.1)
        invFun := fun x => (x.1, x.2 - x.1)
        left_inv x := by simp
        right_inv x := by simp
        measurable_toFun := by fun_prop
        measurable_invFun := by fun_prop}
    change _ = Measure.map f' _ _
    rw [MeasurableEmbedding.map_apply, withDensity_apply, MeasureTheory.setLIntegral_map]
    simp
    rfl
    · exact hs
    · fun_prop
    · fun_prop
    · exact (MeasurableEquiv.measurableSet_preimage f').mpr hs
    · exact MeasurableEquiv.measurableEmbedding f'
    · exact hs
  rw [h1]
  have h2 :
      ((ringMeasure.prod volume).withDensity fun x => ENNReal.ofReal (1 / ‖x.2‖ ^ 2))
      = ringMeasure.prod (radialAngularMeasure (d := 3)) := by
    rw [radialAngularMeasure, MeasureTheory.prod_withDensity_right]
    simp
    fun_prop
  rw [h2]
  refine { exists_integrable := ?_ }
  obtain ⟨C, hC⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := ringMeasure.prod (ringMeasure.prod (radialAngularMeasure (d := 3))))
  use C
  rw [MeasurableEmbedding.integrable_map_iff]
  have h2' (x : Space × Space): (1/2 : ℝ) • ‖x.2‖ ≤ max ‖x.1‖ ‖x.2 + x.1‖ := by
    simp
    by_cases h : 2⁻¹ * ‖x.2‖ ≤ ‖x.1‖
    · simp [h]
    simp at h
    right
    trans ‖x.2‖ - ‖x.1‖
    · grind
    · exact norm_sub_le_norm_add x.2 x.1
  apply Integrable.mono (g := fun x => (1 + (1/2 : ℝ) • ‖x.2‖) ^ (- ↑C :ℝ ))
  ·
    sorry
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with x
    simp
    refine inv_anti₀ ?_ ?_
    · positivity
    refine pow_le_pow_left₀ ?_ ?_ C
    · positivity
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    specialize h2' x
    simp at h2'
    grind


/-!

## C. The distribution associated with the ring

-/

/-- The distribution on `Space 3` corresponding to integration around a ring. -/
def ringDist : (Space 3) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ ringMeasure

lemma ringDist_apply_eq_integral_ringMeasure (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ x, f x ∂ringMeasure := by
  rw [ringDist, SchwartzMap.integralCLM_apply]


lemma ringDist_eq_integral_delta (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ z, diracDelta ℝ z f ∂ringMeasure := by
  rw [ringDist_apply_eq_integral_ringMeasure]
  simp

open InnerProductSpace
open Real
lemma ringDist_eq_integral_ring_integral_inner (f : 𝓢(Space 3, ℝ)) :
    ringDist f = - ∫ z, (∫ r, ⟪(1/ (4 * π )) • ‖r-z‖ ^ (- 3 : ℤ) • basis.repr (r-z),
      Space.grad f r⟫_ℝ)
      ∂ringMeasure := by
  rw [ringDist_eq_integral_delta]
  rw [← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards with a
  have h1 := Space.distDiv_inv_pow_eq_dim (d := 2)
  trans (1/(3 * volume (α := Space).real (Metric.ball 0 1))) * (distDiv <|distTranslate (basis.repr a) <|
    (distOfFunction (fun x => ‖x‖ ^ (-3 : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- 3 : ℤ) (by omega)))) f
  · rw [distDiv_distTranslate,]
    erw [h1]
    simp [distTranslate_apply]
    field_simp
  rw [distTranslate_ofFunction, distDiv_ofFunction]
  simp [inner_smul_left]
  rw [integral_const_mul]
  ring


set_option synthInstance.maxHeartbeats 0 in
lemma ringDist_eq_integral_integral_ring_inner (f : 𝓢(Space 3, ℝ)) :
    ringDist f = - ∫ r, (∫ z,  ⟪(1/ (4 * π)) • ‖r-z‖ ^ (- 3 : ℤ) • basis.repr (r-z), Space.grad f r⟫_ℝ
      ∂ringMeasure) := by
  rw [ringDist_eq_integral_ring_integral_inner, MeasureTheory.integral_integral_swap]
  /- Integrability condition -/
  /- Generalizing the grad of the schwartz map. -/
  conv_lhs =>
    enter [1, x, r]
    rw [← gradSchwartz_apply_eq_grad]
  generalize (gradSchwartz f)  = η
  /- Turning the integral into an integral of the norms -/
  apply MeasureTheory.Integrable.mono (g := fun r =>
    (‖(1/ (4 * π)) • ‖r.2 - r.1‖ ^ (- 3 : ℤ) • basis.repr (r.2 - r.1)‖) * ‖η r.2‖)
  rotate_left
  · simp
    apply MeasureTheory.AEStronglyMeasurable.inner
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    · refine AEStronglyMeasurable.comp_snd ?_
      fun_prop
  · filter_upwards with r
    simp
    change  ‖⟪_, η r.2⟫_ℝ‖  ≤ _
    exact norm_inner_le_norm ((π⁻¹ * 4⁻¹) • (‖r.2 - r.1‖ ^ 3)⁻¹ • (basis.repr r.2 - basis.repr r.1))
        (η r.2)
  /- Removing the `(1/ (4 * π))` from the intergable condition. -/
  generalize  (1/ (4 * π)) = C
  simp [norm_smul, mul_assoc]
  apply Integrable.const_mul
  simp [← mul_assoc]
  /- Simplifying the norms -/
  apply Integrable.congr (f := fun (x : Space × Space) => (‖x.2 - x.1‖ ^ 2)⁻¹ * ‖η x.2‖)
  rotate_left
  · filter_upwards with r
    simp [← map_sub]
    left
    by_cases h : ‖r.2 - r.1‖  = 0
    · simp [h]
    field_simp
  /- Introducng a bump function. -/
  let κ : 𝓢(Space, ℝ)
  /- Turn the condition into a statement about temperate growth -/
  suffices h : ∃ (n : ℕ), Integrable (fun x : Space × Space => (‖x.2 - x.1‖ ^ 2)⁻¹ *
      (1 + ‖x.2‖) ^ (- n : ℝ)) (ringMeasure.prod volume) by
    obtain ⟨n, hn⟩ := h
    let μ := (ringMeasure.prod (volume (α := Space)))
    have h1 {f : Space → EuclideanSpace ℝ (Fin 3)} -- based on integrable_of_le_of_pow_mul_le
        {C₁ C₂ : ℝ} {k : ℕ} (hf : ∀ x, ‖f x‖ ≤ C₁)
        (h'f : ∀ x, ‖x‖ ^ (k + n) * ‖f x‖ ≤ C₂) (h''f : AEStronglyMeasurable (fun x => f x.2) μ) :
        Integrable (fun x : Space × Space ↦ (‖x.2 - x.1‖ ^ 2)⁻¹ * ‖x.2‖ ^ k * ‖f x.2‖) μ := by
      apply (hn.const_mul (2 ^ n * (C₁ + C₂))).mono'
      · apply AEStronglyMeasurable.mul
        · fun_prop
        · exact h''f.norm
      · filter_upwards with v
        simp only [norm_mul, norm_pow, norm_norm, mul_assoc]
        trans ‖(‖v.2 - v.1‖ ^ 2)⁻¹‖ * (2 ^ n * (C₁ + C₂) * (1 + ‖v.2‖) ^ (-n : ℝ))
        · apply mul_le_mul
          · rfl
          · exact pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v.2) (h'f v.2)
          · positivity
          · positivity
        apply le_of_eq
        simp
        ring
    have h2 (f : 𝓢(Space, EuclideanSpace ℝ (Fin 3))) -- based on integrable_pow_mul_iteratedFDeriv
        (k : ℕ) : Integrable (fun x : Space × Space ↦ (‖x.2 - x.1‖ ^ 2)⁻¹ * ‖x.2‖ ^ k * ‖f x.2‖)
        μ := by
      apply h1 (C₁ := (SchwartzMap.seminorm ℝ 0 0) f)
        (C₂ := (SchwartzMap.seminorm ℝ (k + n)  0) f)
      · fun_prop
      · intro x
        simpa using norm_iteratedFDeriv_le_seminorm ℝ f 0 x
      · intro x
        simpa using le_seminorm ℝ (k + n) 0 f x
    simpa using h2 η 0





  sorry





end Space
