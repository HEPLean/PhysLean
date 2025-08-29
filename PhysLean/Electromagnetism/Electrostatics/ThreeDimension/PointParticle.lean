/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Mathematics.Distribution.OfBounded
import PhysLean.Mathematics.Distribution.PowMul
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
/-!

# A electrostatics of a point particle in 3d.

This file is currently a stub.

It will eventually contain the proof of Gauss's law for a point particle in 3d.
Any help proving this would be greatly appreciated.

## Some references

- https://math.stackexchange.com/questions/2409008/
- https://math.stackexchange.com/questions/1335591/
-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace ThreeDimPointParticle
open Space StaticElectricField MeasureTheory Real InnerProductSpace
noncomputable section

/-- The charge distribution of a point particle of charge `q` in 1d space sitting at the origin.
  Mathematically, this corresponds to a dirac delta distribution centered at the origin. -/
def chargeDistribution (q : ℝ) : ChargeDistribution 3 := q • diracDelta ℝ 0

/-- The electric field of a point particle of charge `q` in 3d space sitting at the origin.
  Mathematically, this corresponds to the distribution associated to the distribution
  `(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r`. -/
def electricField (q ε : ℝ) : StaticElectricField 3 :=
  Distribution.ofBounded (fun r => (q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r)
  ⟨|q / (4 * π * ε)|, 0, 0, by
    simp only [abs_nonneg, le_refl, Nat.succ_eq_add_one, Nat.reduceAdd, inv_pow, Nat.cast_ofNat,
      rpow_neg_ofNat, Int.reduceNeg, zpow_neg, pow_zero, mul_one, add_zero, true_and]
    intro x
    simp [norm_smul]
    by_cases h : x = 0
    · subst h
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero,
        mul_zero]
      apply le_of_eq
      ring
    have h' : ‖x‖ ≠ 0 := by exact norm_ne_zero_iff.mpr h
    apply le_of_eq
    field_simp [abs_mul, abs_div]
    by_cases hε : ε = 0
    · subst hε
      simp
    field_simp
    trans |q| * ‖x‖ * (4 * |π| * |ε| * ‖x‖ ^ 2)
    · rfl
    ring⟩ (by fun_prop)

/-- Guass' law for a point particle in 3-dimensions, that is this theorem states that
  the divergence of `(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r` is equal to `q • δ(r)`. -/
lemma gaussLaw (q ε : ℝ) : (electricField q ε).GaussLaw ε (chargeDistribution q) := by
  ext η
  let η' (n : ↑(Metric.sphere 0 1)) : 𝓢(ℝ, ℝ) := compCLM (g := fun a => a • n.1) ℝ (by
    apply And.intro
    · fun_prop
    · intro n'
      match n' with
      | 0 =>
        simp [norm_smul]
        use 1, 1
        simp
      | 1 =>
        use 0, 1
        intro x
        rw [iteratedFDeriv_succ_eq_comp_right]
        simp [fderiv_smul_const]
      | n' + 1 + 1 =>
        use 0, 0
        intro x
        simp only [norm_eq_abs, pow_zero, mul_one, norm_le_zero_iff]
        rw [iteratedFDeriv_succ_eq_comp_right]
        simp [fderiv_smul_const]
        rw [iteratedFDeriv_succ_const]
        simp
        rfl) (by use 1, 1; simp [norm_smul]) η
  let s : Set (EuclideanSpace ℝ (Fin 3)) := {0}ᶜ
  haveI : MeasureSpace s := by
    exact Measure.Subtype.measureSpace
  calc _
    _ = (divD (electricField q ε)) η := by rfl
    _ = - ∫ r : Space 3, ⟪((q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r), Space.grad η r⟫_ℝ := by
      rw [electricField, Space.divD_ofBounded]
    _ = - (q/(4 * π * ε)) * ∫ r : Space 3, ‖r‖⁻¹ ^ 2 * ⟪‖r‖⁻¹ • r, Space.grad η r⟫_ℝ := by
      simp [inner_smul_left, integral_const_mul]
      left
      congr
      funext r
      ring
    _ = - (q/(4 * π * ε)) * ∫ r : Space 3, ‖r‖⁻¹ ^ 2 *
        (_root_.deriv (fun a => η (a • ‖r‖⁻¹ • r)) ‖r‖) := by
      congr
      funext r
      congr
      rw [real_inner_comm, ← grad_inner_space_unit_vector _ _ (SchwartzMap.differentiable η)]
    /- Moving to spherical coordinates. -/
    _ = - (q/(4 * π * ε)) * ∫ r, ‖r.2.1‖⁻¹ ^ 2 *
        (_root_.deriv (fun a => η (a • r.1)) ‖r.2.1‖)
        ∂(volume (α := EuclideanSpace ℝ (Fin 3)).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))) := by
      rw [← MeasureTheory.MeasurePreserving.integral_comp (f := homeomorphUnitSphereProd _)
        (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
        (volume (α := EuclideanSpace ℝ (Fin 3))))
          (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))))]
      congr 1
      simp only [inv_pow, homeomorphUnitSphereProd_apply_snd_coe, norm_norm,
        homeomorphUnitSphereProd_apply_fst_coe]
      let f (x : Space 3) : ℝ :=
        (‖↑x‖ ^ 2)⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖↑x‖
      conv_rhs =>
        enter [2, x]
        change f x.1
      rw [MeasureTheory.integral_subtype_comap (by simp), ← setIntegral_univ]
      change ∫ x in Set.univ, f x = ∫ (x : Space) in _, f x
      refine (setIntegral_congr_set ?_)
      rw [← MeasureTheory.ae_eq_set_compl]
      trans (∅ : Set (EuclideanSpace ℝ (Fin 3)))
      · apply Filter.EventuallyEq.of_eq
        rw [← Set.compl_empty]
        exact compl_compl _
      · symm
        simp
    /- Splitting the integral over the sphere and radius-/
    _ = - (q/(4 * π * ε)) * ∫ n, (∫ r, ‖r.1‖⁻¹ ^ 2 *
        (_root_.deriv (fun a => η (a • n)) ‖r.1‖)
        ∂((Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))))
        ∂(volume (α := EuclideanSpace ℝ (Fin 3)).toSphere) := by
      congr 1
      rw [MeasureTheory.integral_prod]
      /- Integrable condition. -/
      convert integrable_ofBounded_inner_grad_schwartzMap_spherical (f := fun r => ‖r‖⁻¹ ^ 3 • r)
        (by
        use 1, 0, 0
        simp [norm_smul]
        intro x
        by_cases hx : x = 0
        · subst hx
          simp [@zpow_two]
        apply le_of_eq
        have hx' : ‖x‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hx
        field_simp
        change ‖x‖ * ‖x‖ ^ 2 = ‖x‖ ^ 3
        conv_rhs => rw [pow_succ, mul_comm]
        rfl) (by fun_prop) η
      rename_i r
      simp only [norm_eq_abs, inv_pow, sq_abs, Nat.succ_eq_add_one, Nat.reduceAdd,
        Function.comp_apply, homeomorphUnitSphereProd_symm_apply_coe]
      let x : Space 3 := r.2.1 • r.1.1
      have hr := r.2.2
      simp [-Subtype.coe_prop] at hr
      have hr2 : r.2.1 ≠ 0 := by exact Ne.symm (ne_of_lt hr)
      trans (r.2.1 ^ 2)⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖x‖
      · simp [x, norm_smul]
        left
        congr
        funext a
        congr
        simp [smul_smul]
        rw [abs_of_nonneg (le_of_lt hr)]
        field_simp
      rw [← grad_inner_space_unit_vector]
      rw [real_inner_comm]
      simp [inner_smul_left, x, norm_smul, abs_of_nonneg (le_of_lt hr)]
      field_simp
      ring
      exact SchwartzMap.differentiable η
    /- Simplifying the inner integral. -/
    _ = - (q/(4 * π * ε)) * ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        (_root_.deriv (fun a => η (a • n)) r.1) ∂(.comap Subtype.val volume))
        ∂(volume (α := EuclideanSpace ℝ (Fin 3)).toSphere) := by
      congr
      funext n
      simp [Measure.volumeIoiPow]
      erw [integral_withDensity_eq_integral_smul]
      congr
      funext r
      trans ((r.1 ^ 2).toNNReal : ℝ) • ((r.1 ^ 2)⁻¹ * _root_.deriv (fun a => η (a • ↑n)) |r.1|)
      · rfl
      trans ((r.1 ^ 2) : ℝ) • ((r.1 ^ 2)⁻¹ * _root_.deriv (fun a => η (a • ↑n)) |r.1|)
      · congr
        refine coe_toNNReal (↑r ^ 2) ?_
        apply pow_two_nonneg
      have h1 : r.1 ≠ 0 := by exact ne_of_gt r.2
      field_simp
      congr
      rw [abs_of_nonneg]
      have h1 := r.2
      simp [- Subtype.coe_prop] at h1
      exact le_of_lt h1
      fun_prop
    _ = - (q/(4 * π * ε)) * ∫ n, (-η 0) ∂(volume (α := EuclideanSpace ℝ (Fin 3)).toSphere) := by
      congr
      funext n
      rw [MeasureTheory.integral_subtype_comap (by simp)]
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        (f := fun a => η (a • n)) (m := 0)]
      · simp
      · refine ContinuousAt.continuousWithinAt ?_
        fun_prop
      · intro x hx
        refine DifferentiableAt.hasDerivAt ?_
        have h1 : Differentiable ℝ η := by exact SchwartzMap.differentiable η
        fun_prop
      · change IntegrableOn (SchwartzMap.derivCLM ℝ (η' n)) (Set.Ioi 0) volume
        refine Integrable.integrableOn ?_
        exact integrable ((derivCLM ℝ) (η' n))
      · change Filter.Tendsto (η' n) Filter.atTop (nhds 0)
        exact Filter.Tendsto.mono_left (η' n).toZeroAtInfty.zero_at_infty' atTop_le_cocompact
    _ = (q/(4 * π * ε)) * η 0 * (3 * (volume (α := EuclideanSpace ℝ (Fin 3))).real
        (Metric.ball 0 1)) := by
      simp only [integral_const, Measure.toSphere_real_apply_univ, finrank_euclideanSpace,
        Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul, mul_neg, neg_mul, neg_neg]
      ring
    _ = (q/(4 * π * ε)) * η 0 * (3 * (π * 4/3)) := by
      congr
      simp [Measure.real]
      positivity
    _ = (q/ε) * η 0 := by
      by_cases hε : ε = 0
      · subst hε
        simp
      field_simp
      ring
  simp [chargeDistribution]
  ring
