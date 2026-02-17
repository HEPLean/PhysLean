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


lemma ringDist_eq_integral_integral_ring_inner (f : 𝓢(Space 3, ℝ)) :
    ringDist f = - ∫ r, (∫ z,  ⟪(1/ (4 * π)) • ‖r-z‖ ^ (- 3 : ℤ) • basis.repr (r-z), Space.grad f r⟫_ℝ
      ∂ringMeasure) := by
  rw [ringDist_eq_integral_ring_integral_inner]
  rw [MeasureTheory.integral_integral_swap]
  /- Integrability condition -/
  refine (integrable_prod_iff' ?_).mpr ⟨?_, ?_⟩
  · simp
    apply MeasureTheory.AEStronglyMeasurable.inner
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    · refine AEStronglyMeasurable.comp_snd ?_
      sorry -- Prove that grad of schwartz map is aestrongly measurable
  · /- We take `r` everywhere except for on the ring itself. -/
    have h_ne : ∀ᵐ r ∂volume, r ∉ Set.range ring := by
      rw [← MeasureTheory.measure_eq_zero_iff_ae_notMem]
      simp
    filter_upwards [h_ne] with r hr
    simp
    apply integrable_ringMeasure_of_continuous
    change  Continuous ((fun x => ⟪(π⁻¹ * 4⁻¹) • (‖r - ring x‖ ^ 3)⁻¹ • (basis.repr r - basis.repr (ring x)), ∇ (⇑f) r⟫_ℝ))
    apply Continuous.inner
    . apply Continuous.const_smul
      apply Continuous.smul
      · refine Continuous.inv₀ ?_ ?_
        · refine Continuous.zpow₀ ?_ 3 ?_
          · fun_prop
          · intro a
            simp
        · intro x
          by_contra h
          have h' : ‖r - ring x‖ = 0 := by exact eq_zero_of_pow_eq_zero h
          simp at h'
          have h'' : r = ring x := by exact eq_of_sub_eq_zero h'
          subst h''
          simp at hr
      · fun_prop
    · fun_prop
  · simp
    apply MeasureTheory.Integrable.mono (g := fun r =>
      (∫ z, ‖(1/ (4 * π)) • ‖r-z‖ ^ (- 3 : ℤ) • basis.repr (r-z)‖ ∂ringMeasure) * ‖Space.grad f r‖)
    · sorry
    ·
      sorry
    · /- Monotonicity condition -/
      filter_upwards with r
      simp
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), ← integral_mul_const]
      refine integral_mono ?_ ?_ ?_
      · sorry
      · sorry
      · refine Pi.le_def.mpr <| fun x => ?_
        exact abs_real_inner_le_norm _ _





end Space
