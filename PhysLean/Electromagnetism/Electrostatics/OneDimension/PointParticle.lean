/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.Mathematics.Distribution.OfBounded
import PhysLean.Mathematics.Distribution.PowMul
/-!

# A electrostatics of a point particle in 1d.

In this module we study the electrostatics of a point particle of charge `q`
sitting at the origin of 1d space.

-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace OneDimPointParticle
open Space StaticElectricField MeasureTheory
noncomputable section

/-- The charge distribution of a point particle of charge `q` in 1d space sitting at the origin.
  Mathematically, this corresponds to a dirac delta distribution centered at the origin. -/
def chargeDistribution (q : ℝ) : ChargeDistribution 1 := q • diracDelta ℝ 0

/-- An electric potential of a charge distribution of a point particle. Mathematically
  this corresponds to the distribution formed by the function `|x|` multiplied by a
  scalar. -/
def electricPotential (q ε : ℝ) : StaticElectricPotential 1 :=
  - Distribution.ofBounded (fun x => (q/(2 * ε)) • ‖x‖)
  ⟨0, |q/(2 * ε)|, 1, by simp [-norm_div]⟩ (by fun_prop)

@[simp]
lemma electricPotential_eq_zero_of_ε_eq_zero (q : ℝ) :
    electricPotential q 0 = 0 := by
  ext x
  simp [electricPotential, ofBounded_apply, norm_zero, div_zero, zero_smul]

/-- An electric field corresponding to a charge distribution of a point particle,
  defined as the negative of the gradient of `electricPotential q ε`.

  This is the electric field which is symmetric about the origin, and in this sense
  does not sit in a constant electric field.
-/
def electricField (q ε : ℝ) : StaticElectricField 1 := - Space.gradD (electricPotential q ε)

@[simp]
lemma electricField_eq_zero_of_ε_eq_zero (q : ℝ) :
    electricField q 0 = 0 := by
  simp [electricField]

/-- The electric field `electricField q ε` is related to the `heavisideStep` function. -/
lemma electricField_eq_heavisideStep (q ε : ℝ) :
    (electricField q ε) = ((q/ε) • ((heavisideStep 0).smulRight (basis 0) -
    (1/(2 : ℝ)) • constD 1 (basis 0))) := by
  rw [electricField]
  ext η i
  let s : Set (EuclideanSpace ℝ (Fin 1)) :=
    {x : EuclideanSpace ℝ (Fin 1) | 0 < x (Fin.last 0)}
  have hs : NullMeasurableSet s volume := by
    simp [s]
    refine nullMeasurableSet_lt ?_ ?_
    · fun_prop
    · change AEMeasurable oneEquivCLE volume
      fun_prop
  fin_cases i
  calc _
    _ = - (∫ x, fderiv ℝ η x (basis 0) • (q/(2 *ε)) • ‖x‖) := by
      simp only [Fin.zero_eta, Fin.isValue, ContinuousLinearMap.neg_apply, gradD_eq_sum_basis,
        Finset.univ_unique, Fin.default_eq_zero, neg_smul, Finset.sum_neg_distrib,
        Finset.sum_singleton, PiLp.neg_apply, PiLp.smul_apply, basis_self, smul_eq_mul, mul_one,
        neg_neg, s]
      rw [electricPotential]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul, Fin.isValue,
        ContinuousLinearMap.neg_apply, neg_inj, s]
      rw [ofBounded_apply]
      rfl
    _ = - (q/(2 * ε)) * (∫ x, fderiv ℝ η x (basis 0) • ‖x‖) := by
      rw [← integral_const_mul, ← integral_neg]
      congr
      funext x
      simp only [Fin.isValue, smul_eq_mul, neg_mul, neg_inj, s]
      ring
    _ = - (q/(2 * ε)) * (∫ x in s, fderiv ℝ η x (basis 0) • ‖x‖) +
        - (q/(2 * ε)) * (∫ x in sᶜ, fderiv ℝ η x (basis 0) • ‖x‖) := by
      rw [← integral_add_compl₀ hs ?_]
      · ring
      change Integrable (fun x : EuclideanSpace ℝ (Fin 1) =>
        ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0)) ((fderivCLM ℝ) η)) x • ‖x‖)
      apply bounded_integrable
      · exact ⟨0, 1, 1, by simp⟩
      · fun_prop
    _ = - (q/(2 * ε)) * (∫ x in s, fderiv ℝ η x (basis 0) • x 0) +
        - (q/(2 * ε)) * (∫ x in sᶜ, fderiv ℝ η x (basis 0) • (- x 0)) := by
      congr 2
      · refine setIntegral_congr_ae₀ hs ?_
        filter_upwards with x hx
        congr
        rw [@PiLp.norm_eq_of_L2]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
          Finset.sum_singleton, s]
        refine Real.sqrt_eq_cases.mpr ?_
        left
        apply And.intro
        · exact Eq.symm (Lean.Grind.Semiring.pow_two (x 0))
        · simp [s] at hx
          apply le_of_lt hx
      · refine setIntegral_congr_ae₀ ?_ ?_
        · simpa using hs
        filter_upwards with x hx
        congr
        rw [@PiLp.norm_eq_of_L2]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Real.norm_eq_abs, sq_abs,
          Finset.sum_singleton, s]
        refine Real.sqrt_eq_cases.mpr ?_
        left
        simp only [Fin.isValue, mul_neg, neg_mul, neg_neg, Left.nonneg_neg_iff, s]
        apply And.intro
        · exact Eq.symm (Lean.Grind.Semiring.pow_two (x 0))
        · simp [s] at hx
          exact hx
    _ = - (q/(2 * ε)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) x * x) +
        - (q/(2 * ε)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) x * (-x)) := by
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      congr
      · simp only [Fin.isValue, smul_eq_mul, compCLMOfContinuousLinearEquiv_apply, s]
        funext x
        congr 1
        rw [← fderiv_deriv]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        simp only [Fin.isValue, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
          Function.comp_apply, s]
        congr 1
        funext i
        fin_cases i
        simp only [Fin.isValue, Fin.zero_eta, basis_self, oneEquivCLE, s]
        rfl
      · simp only [Fin.reduceLast, Fin.isValue, Set.preimage_compl, Set.preimage_setOf_eq, s]
        ext x
        simp [oneEquiv_symm_apply]
      · simp only [Fin.isValue, smul_eq_mul, mul_neg, compCLMOfContinuousLinearEquiv_apply, s]
        funext x
        congr 1
        rw [← fderiv_deriv]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        simp only [Fin.isValue, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
          Function.comp_apply, s]
        congr 2
        funext i
        fin_cases i
        simp only [Fin.isValue, Fin.zero_eta, basis_self, oneEquivCLE, s]
        rfl
    _ = - (q/(2 * ε)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (fun x => η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x * (fun x => x) x) x
        - η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (fun x => η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x * (fun x => - x) x) x
        + η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · funext x
        rw [deriv_fun_mul]
        simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, deriv_id'', mul_one,
          add_sub_cancel_right, s]
        · exact SchwartzMap.differentiableAt _
        · fun_prop
      · funext x
        rw [deriv_fun_mul]
        simp only [compCLMOfContinuousLinearEquiv_apply, mul_neg, Function.comp_apply, deriv_neg'',
          mul_one, neg_add_cancel_right, s]
        · exact SchwartzMap.differentiableAt _
        · fun_prop
    _ = - (q/(2 * ε)) * (∫ x in Set.Ioi (0 : ℝ),
        deriv (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x
        - η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) * (∫ x in Set.Iic (0 : ℝ),
        deriv (-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x
        + η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · funext x
        congr
        funext x
        simp [powOneMul_apply]
        rw [mul_comm]
      · funext x
        congr
        funext x
        change _ = - ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)) x
        simp [powOneMul_apply]
        rw [mul_comm]
    _ = - (q/(2 * ε)) * ((∫ x in Set.Ioi (0 : ℝ),
        deriv (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) * ((∫ x in Set.Iic (0 : ℝ),
        deriv (-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) x)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      rw [integral_sub, integral_add]
      · refine Integrable.restrict ?_
        change Integrable (derivCLM ℝ
          (-(powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
        exact integrable
            ((derivCLM ℝ) (-(powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
      · refine Integrable.restrict ?_
        exact integrable _
      · refine Integrable.restrict ?_
        change Integrable (derivCLM ℝ
          (powOneMul ℝ ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
        exact integrable
            ((derivCLM ℝ) (powOneMul ℝ ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
      · refine Integrable.restrict ?_
        exact integrable _
    _ = - (q/(2 * ε)) * ((0 -
        (powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) 0)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) *
        (((-powOneMul ℝ (η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm)) 0 - 0)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
        · apply Continuous.continuousWithinAt
          fun_prop
        · intro x hx
          refine DifferentiableAt.hasDerivAt ?_
          exact SchwartzMap.differentiableAt _
        · apply Integrable.integrableOn
          change Integrable (derivCLM ℝ ((powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η))) volume
          exact integrable
            ((derivCLM ℝ) ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
        · exact Filter.Tendsto.mono_left ((powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)).toZeroAtInfty.zero_at_infty'
            atTop_le_cocompact
      · apply MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto
        · apply Continuous.continuousWithinAt
          fun_prop
        · intro x hx
          refine DifferentiableAt.hasDerivAt ?_
          exact SchwartzMap.differentiableAt _
        · apply Integrable.integrableOn
          change Integrable (derivCLM ℝ (- (powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
          exact integrable
            ((derivCLM ℝ) (- (powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)))
        · apply Filter.Tendsto.mono_left
            ((- (powOneMul ℝ)
            ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)).toZeroAtInfty.zero_at_infty')
          exact atBot_le_cocompact
    _ = - (q/(2 * ε)) * ((0 - 0)
        - ∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) * ((0 - 0)
        + ∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      congr
      · simp [powOneMul_apply]
      · change - ((powOneMul ℝ) ((compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm) η)) 0 = 0
        simp [powOneMul_apply]
    _ = (q/(2 * ε)) *
        (∫ x in Set.Ioi (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) +
        - (q/(2 * ε)) *
          (∫ x in Set.Iic (0 : ℝ), η.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm x) := by
      simp
    _ = (q/(2 * ε)) * (∫ x in s, η x) + - (q/(2 * ε)) * (∫ x in sᶜ, η x) := by
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      rw [← oneEquiv_symm_measurePreserving.setIntegral_preimage_emb
        (oneEquiv_symm_measurableEmbedding)]
      congr
      ext x
      simp [oneEquiv_symm_apply, s]
    _ = (q/(2 * ε)) * (∫ x in s, η x) + - (q/(2 * ε)) * ((∫ x, η x) - ∫ x in s, η x) := by
      congr 2
      rw [← integral_add_compl₀ hs]
      · ring
      exact integrable η
    _ = (q/(ε)) * (∫ x in s, η x) + - (q/(2 * ε)) * (∫ x, η x) := by
      ring
  simp [mul_sub]
  congr 2
  rw [← mul_assoc]
  congr 1
  ring
  simp [constD, const_apply]
  rw [integral_smul_const]
  simp

/-- The electric field `electricField q ε` corresponding to a charge distribution of a point
  particle satisfies Gauss's law for the charge distribution of the point particle.
-/
lemma gaussLaw (q ε : ℝ) : (electricField q ε).GaussLaw ε (chargeDistribution q) := by
  by_cases h : ε = 0
  · subst h
    simp [GaussLaw]
  rw [gaussLaw_iff]
  ext η
  rw [electricField_eq_heavisideStep, chargeDistribution]
  field_simp
  left
  rw [divD_apply_eq_sum_fderivD]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd,
    Finset.sum_singleton]
  rw [fderivD_apply]
  simp only [Fin.isValue, ContinuousLinearMap.smulRight_apply, PiLp.neg_apply, PiLp.smul_apply,
    basis_self, smul_eq_mul, mul_one]
  rw [heavisideStep_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceLast, Fin.isValue]
  rw [← MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
    (μ := volume) (ν := volume) (f := oneEquiv.symm)]
  simp only [Fin.isValue, Set.preimage_setOf_eq]
  let f' := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0)) ((fderivCLM ℝ) η))
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ oneEquivCLE.symm η
  change -∫ (x : ℝ) in Set.Ioi 0, f' x = _
  rw [neg_eq_iff_eq_neg]
  trans 0 - f 0
  · apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f' := f')
      (f := f)
    · apply Continuous.continuousWithinAt
      fun_prop
    · have hf : f' = (SchwartzMap.derivCLM ℝ) f := by
        ext x
        simp [f']
        change fderiv ℝ η (oneEquivCLE.symm x) (basis 0) = _
        trans fderiv ℝ η (oneEquivCLE.symm x) (oneEquivCLE.symm 1)
        · congr 1
          funext i
          fin_cases i
          simp
          rfl
        rw [← fderiv_deriv]
        dsimp [f]
        rw [ContinuousLinearEquiv.comp_right_fderiv]
        rfl
      rw [hf]
      simpa using fun x hx => SchwartzMap.differentiableAt f
    · exact (integrable f').integrableOn
    · exact Filter.Tendsto.mono_left f.toZeroAtInfty.zero_at_infty' atTop_le_cocompact
  · simp [f]
  · exact oneEquiv_symm_measurePreserving
  · exact oneEquiv_symm_measurableEmbedding

/-- For the charge distribution of a point particle in 1-dimension, a static electric field
  satifies Gauss's law if and only if it is the linear combination of the
  electric field `electricField q ε` (corresponding to the symmetric step function), plus
  a constant electric field.

  The `if` direction of this result is easy to prove, whilst the `only if` direction
  is difficult.

  Note: This result follows from the (as yet unproven) analgous result for the
  vacuum.
-/
@[sorryful]
lemma gaussLaw_iff (q ε : ℝ) (E : StaticElectricField 1) :
    E.GaussLaw ε (chargeDistribution q) ↔ ∃ m, E = electricField q ε + constD 1 m := by
  sorry

end
end OneDimPointParticle

end Electromagnetism
