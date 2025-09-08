/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Electrostatics.Basic
import PhysLean.SpaceAndTime.Space.Translations
import PhysLean.Mathematics.Distribution.PowMul
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm
/-!

# A electrostatics of a point particle in 3d.

The electrostatics of a point particle in 3d space sitting at an arbitrary position `r₀`.

## Key results

- The electric potential is given by `electricPotential q ε r₀`.
- The electric field is given by `electricField q ε r₀`.
- Gauss's law is given in `gaussLaw`.
- Faraday's law is given in `faradaysLaw`.

## Some references

- https://math.stackexchange.com/questions/2409008/
- https://math.stackexchange.com/questions/1335591/
-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace ThreeDimPointParticle
open Space StaticElectricField MeasureTheory Real InnerProductSpace
noncomputable section

TODO "LQXNC" "Generalize the proof of Gauss' law for a point particle in 3d
  so the particle is not at the origin."

/-- The charge distribution of a point particle of charge `q` in 3d space sitting at the `r₀`.
  Mathematically, this corresponds to a dirac delta distribution centered at the `r₀`. -/
def chargeDistribution (q : ℝ) (r₀ : Space) : ChargeDistribution 3 := q • diracDelta ℝ r₀

lemma chargeDistribution_eq_zero_of_charge_eq_zero (r₀ : Space) :
    chargeDistribution 0 r₀ = 0 := by simp [chargeDistribution]

lemma chargeDistribution_eq_translateD (q : ℝ) (r₀ : Space) :
    chargeDistribution q r₀ = Space.translateD r₀
      (chargeDistribution q 0) := by
  ext η
  simp [chargeDistribution, Space.translateD_apply]

/-- The electric potential of a point particle of charge `q` in 3d space sitting at the `r₀`.
  Mathematically, this corresponds to the distribution associated to the function
  `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹`. -/
def electricPotential (q ε : ℝ) (r₀ : Space) : StaticElectricPotential 3 :=
  Distribution.ofFunction (fun r => (q/(4 * π * ε)) • ‖r - r₀‖⁻¹)
  (by
    apply IsDistBounded.const_smul
    apply IsDistBounded.congr (f := fun r => ‖r - r₀‖ ^ (-1 : ℤ))
      (IsDistBounded.pow_shift (-1) r₀ (by simp))
    simp) (by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd];
    refine AEStronglyMeasurable.const_mul ?_ (q / (4 * π * ε))
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine stronglyMeasurable_iff_measurable.mpr ?_
    fun_prop)

lemma electricPotential_eq_translateD (q ε : ℝ) (r₀ : Space) :
    electricPotential q ε r₀ = Space.translateD r₀ (electricPotential q ε 0) := by
  ext η
  simp [electricPotential]
  rw [Space.translateD_ofFunction]

/-- The electric field of a point particle of charge `q` in 3d space sitting at `r₀`.
  Mathematically, this corresponds to the distribution associated to the function
  `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹ ^ 3 • (r - r₀)`. -/
def electricField (q ε : ℝ) (r₀ : Space) : StaticElectricField 3 :=
  Distribution.ofFunction (fun r => (q/(4 * π * ε)) • ‖r - r₀‖⁻¹ ^ 3 • (r - r₀))
  (by
    apply IsDistBounded.const_smul
    apply IsDistBounded.congr (f := fun r => ‖r - r₀‖ ^ (-2 : ℤ))
      (IsDistBounded.pow_shift _ r₀ (by simp))
    simp [norm_smul]
    intro x
    by_cases hx : ‖x - r₀‖ = 0
    · simp [hx, zpow_two]
    · field_simp [zpow_two]
      ring) (by fun_prop)

lemma electricField_eq_zero_of_charge_eq_zero {ε : ℝ} (r₀ : Space) :
    electricField 0 ε r₀ = 0 := by simp [electricField]

lemma electricField_eq_translateD (q ε : ℝ) (r₀ : Space) :
    electricField q ε r₀ = Space.translateD r₀ (electricField q ε 0) := by
  ext η
  simp [electricField]
  rw [Space.translateD_ofFunction]

open InnerProductSpace

open scoped Topology BigOperators FourierTransform

/-!

## Prove that the electric field is the gradient of the potential

We now prove that the electric field is the negative gradient of the potential.

We do this for `r₀ = 0`, and then use translations to prove it for any `r₀`.

We first show in `gradD_electricPotential_eq_electricField_of_integral_eq_zero` that this
is true if
`∫ x, d_y η x * ‖x‖⁻¹ + η x * -⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ = 0`
for all Schwartz maps `η` and directions `y`.

To prove this integral is zero we define `potentialLimitSeries` which is a sequence of functions
given by
`potentialLimitSeries n x = (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ)`.
The limit of this sequence as `n → ∞` is `‖x‖⁻¹`, and the limit of it's gradient is
`-⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ `.

The key idea is to use `MeasureTheory.tendsto_integral_of_dominated_convergence` to show
that the limit of the integrals
`∫ x, fderiv ℝ η x y * potentialLimitSeries n x + η x * fderiv ℝ (potentialLimitSeries n) x y`
is equal to `∫ x, d_y η x * ‖x‖⁻¹ + η x * -⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ`,
and because it they are total derivatives of differentiable functions, eqaul to zero.

To use `MeasureTheory.tendsto_integral_of_dominated_convergence` we need to show a number
of properties of `potentialLimitSeries` and it's derivatives.

For convience we define
`fderiv ℝ η x y * potentialLimitSeries n x + η x * fderiv ℝ (potentialLimitSeries n) x y`
to be `potentialLimitSeriesFDerivSchwartz`.

### Note

This proof also allows us to prove Faraday's law for a point particle in 3d.

-/

/-- The gradient of the electric potential is equal to the electric field if the integral
  ∫ (a : EuclideanSpace ℝ (Fin 3)), (fderivCLM ℝ η a y * ‖a‖⁻¹ +
    η a * ⟪(‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ)
  is zero.
  -/
lemma gradD_electricPotential_eq_electricField_of_integral_eq_zero (q ε : ℝ)
    (h_integral : ∀ η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ), ∀ y : EuclideanSpace ℝ (Fin 3),
    ∫ (a : EuclideanSpace ℝ (Fin 3)), (fderivCLM ℝ η a y * ‖a‖⁻¹ +
    η a * - ⟪(‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ) = 0) :
    - Space.gradD (electricPotential q ε 0) = electricField q ε 0 := by
  rw [← sub_eq_zero]
  ext1 η
  apply ext_inner_right ℝ
  intro y
  simp [inner_sub_left, gradD_inner_eq, fderivD_apply]
  dsimp [electricPotential, electricField]
  rw [ofFunction_inner, ofFunction_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul, inv_pow]
  rw [← integral_sub]
  simp only [sub_zero]
  change ∫ (a : EuclideanSpace ℝ (Fin 3)), (fderivCLM ℝ η a y * (q / (4 * π * ε) * ‖a‖⁻¹)) -
    η a * ⟪(q / (4 * π * ε)) • (‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ = _
  trans ∫ (a : EuclideanSpace ℝ (Fin 3)), (q / (4 * π * ε)) * (fderivCLM ℝ η a y * ‖a‖⁻¹ +
    η a * -⟪(‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ)
  · congr
    funext a
    rw [inner_smul_left]
    simp only [fderivCLM_apply, map_div₀, conj_trivial]
    ring
  rw [integral_const_mul, h_integral, mul_zero]
  apply IsDistBounded.schwartzMap_mul_integrable
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, sub_zero]
    change IsDistBounded fun x => (q / (4 * π * ε)) • ‖x‖⁻¹
    apply IsDistBounded.const_smul
    fun_prop
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd];
    refine AEStronglyMeasurable.const_mul ?_ (q / (4 * π * ε))
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine stronglyMeasurable_iff_measurable.mpr ?_
    fun_prop
  apply IsDistBounded.schwartzMap_mul_integrable
  · apply IsDistBounded.inner_left
    apply IsDistBounded.const_smul
    apply IsDistBounded.congr (f := fun r => ‖r‖ ^ (-2 : ℤ)) (IsDistBounded.pow _ (by simp))
    simp [norm_smul]
    intro x
    by_cases hx : ‖x‖ = 0
    · simp [hx, zpow_two]
    · field_simp [zpow_two]
      ring
  · fun_prop

/-- A series of functions whose limit is the `‖x‖⁻¹` and for which each function is
  differentiable everywhere. -/
def potentialLimitSeries : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ := fun n x =>
  (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ)

lemma potentialLimitSeries_eq (n : ℕ) :
    potentialLimitSeries n = fun x => (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ) := rfl

lemma potentialLimitSeries_eq_sqrt_inv (n : ℕ) :
    potentialLimitSeries n = fun x => √(‖x‖ ^ 2 + 1/(n + 1))⁻¹ := by
  funext x
  rw [potentialLimitSeries_eq]
  simp only [one_div, sqrt_inv]
  rw [sqrt_eq_rpow]
  nth_rewrite 2 [← Real.rpow_neg_one]
  rw [← Real.rpow_mul]
  congr
  ring
  positivity

lemma potentialLimitSeries_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ potentialLimitSeries n x := by
  rw [potentialLimitSeries_eq_sqrt_inv]
  simp

lemma potentialLimitSeries_differentiable (n : ℕ) :
    Differentiable ℝ (potentialLimitSeries n) := by
  rw [potentialLimitSeries_eq]
  refine Differentiable.rpow_const ?_ ?_
  · refine (Differentiable.fun_add_iff_right ?_).mpr ?_
    apply Differentiable.norm_sq ℝ
    · fun_prop
    · fun_prop
  · intro x
    left
    have h1 : 0 < ‖x‖ ^ 2 + 1 / (↑n + 1) := by
      apply add_pos_of_nonneg_of_pos
      · apply sq_nonneg
      · positivity
    by_contra hn
    rw [hn] at h1
    simp at h1

lemma potentialLimitSeries_fderiv (x y : EuclideanSpace ℝ (Fin 3)) (n : ℕ) :
    fderiv ℝ (potentialLimitSeries n) x y =
    - ((‖x‖ ^ 2 + (1 + (n : ℝ))⁻¹) ^ (- 1 /2 : ℝ)) ^ 3 * ⟪x, y⟫_ℝ := by
    have h0 (x : EuclideanSpace ℝ (Fin 3)) : (‖x‖ ^ 2 + ((n : ℝ) + 1)⁻¹) ^ (-1 / 2 : ℝ) =
        (√(‖x‖ ^ 2 + ((n : ℝ) + 1)⁻¹))⁻¹ := by
      rw [sqrt_eq_rpow]
      nth_rewrite 2 [← Real.rpow_neg_one]
      rw [← Real.rpow_mul]
      congr
      ring
      positivity
    trans fderiv ℝ (fun x => (√(‖x‖ ^2 + 1/(n + 1)))⁻¹) x y
    · congr
      funext x
      simp only [one_div]
      dsimp [potentialLimitSeries]
      simp only [one_div]
      exact h0 x
    rw [fderiv_comp']
    simp only [one_div, ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
      deriv_inv', smul_eq_mul, mul_neg, neg_mul, neg_inj]
    rw [fderiv_sqrt]
    simp only [one_div, mul_inv_rev, fderiv_add_const, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    rw [← @grad_inner_eq]
    rw [grad_norm_sq]
    simp [inner_smul_left]
    ring_nf
    rw [mul_comm]
    congr 2
    trans (‖x‖ ^ 2 + ((n : ℝ)+ 1)⁻¹) ^ (-1 / 2 : ℝ)
    · rw [h0 x]
      ring_nf
    ring_nf
    · refine (DifferentiableAt.fun_add_iff_right ?_).mpr ?_
      · apply Differentiable.norm_sq ℝ
        · fun_prop
      · fun_prop
    · have h1 : 0 < ‖x‖ ^ 2 + 1 / (↑n + 1) := by
        apply add_pos_of_nonneg_of_pos
        · apply sq_nonneg
        · positivity
      by_contra hn
      simp at h1
      rw [hn] at h1
      simp at h1
    · refine differentiableAt_inv ?_
      simp only [one_div, ne_eq]
      refine sqrt_ne_zero'.mpr ?_
      apply add_pos_of_nonneg_of_pos
      · apply sq_nonneg
      · positivity
    · refine DifferentiableAt.sqrt ?_ ?_
      refine (DifferentiableAt.fun_add_iff_right ?_).mpr ?_
      · apply Differentiable.norm_sq ℝ
        · fun_prop
      · fun_prop
      have h1 : 0 < ‖x‖ ^ 2 + 1 / (↑n + 1) := by
        apply add_pos_of_nonneg_of_pos
        · apply sq_nonneg
        · positivity
      by_contra hn
      rw [hn] at h1
      simp at h1

lemma potentialLimitSeries_fderiv_eq_potentialLimitseries_mul
    (x y : EuclideanSpace ℝ (Fin 3)) (n : ℕ) :
    fderiv ℝ (potentialLimitSeries n) x y = - (potentialLimitSeries n x) ^ 3 * ⟪x, y⟫_ℝ := by
  rw [potentialLimitSeries_fderiv]
  congr
  simp only [one_div, inv_inj]
  ring

lemma potentialLimitSeries_tendsto (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => potentialLimitSeries n x) Filter.atTop (𝓝 (‖x‖⁻¹)) := by
  conv => enter [1, n]; rw [potentialLimitSeries_eq]
  simp only [one_div]
  have hx_norm : ‖x‖⁻¹ = (‖x‖ ^ 2 + 0) ^ (-1 / 2 : ℝ) := by
    trans √(‖x‖ ^ 2)⁻¹
    · simp
    rw [sqrt_eq_rpow]
    nth_rewrite 1 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul]
    congr
    ring
    simp only [one_div]
    simp
  rw [hx_norm]
  refine Filter.Tendsto.rpow ?_ tendsto_const_nhds ?_
  · apply Filter.Tendsto.add
    · exact tendsto_const_nhds
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  left
  simpa using hx

lemma potentialLimitSeries_fderiv_tendsto (x y : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => fderiv ℝ (potentialLimitSeries n) x y) Filter.atTop
      (𝓝 (-⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ)) := by
  conv => enter [1, n]; rw [potentialLimitSeries_fderiv, neg_mul]
  apply Filter.Tendsto.neg
  rw [inner_smul_left]
  apply Filter.Tendsto.mul_const
  simp only [map_inv₀, conj_trivial]
  have hx' : (‖x‖ ^ 3)⁻¹ = ‖x‖⁻¹^ 3 := by exact Eq.symm (inv_pow ‖x‖ 3)
  rw [hx']
  apply Filter.Tendsto.pow
  convert potentialLimitSeries_tendsto x hx
  rw [potentialLimitSeries_eq]
  simp only [one_div]
  ring_nf

@[fun_prop]
lemma potentialLimitSeries_aeStronglyMeasurable (n : ℕ) :
    AEStronglyMeasurable (potentialLimitSeries n) := by
  rw [potentialLimitSeries_eq]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

@[fun_prop]
lemma potentialLimitSeries_fderiv_aeStronglyMeasurable (n : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :
    AEStronglyMeasurable (fun x => fderiv ℝ (potentialLimitSeries n) x y) := by
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

lemma potentialLimitSeries_bounded_neq_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    ‖potentialLimitSeries n x‖ ≤ ‖x‖⁻¹ := by
  simp only [norm_eq_abs]
  rw [abs_of_nonneg (potentialLimitSeries_nonneg _ _)]
  rw [potentialLimitSeries_eq_sqrt_inv]
  simp only [one_div, sqrt_inv]
  have hx : 0 < ‖x‖ := by positivity
  generalize ‖x‖ = r at *
  refine inv_anti₀ hx ?_
  refine (le_sqrt' hx).mpr ?_
  simp only [le_add_iff_nonneg_right, inv_nonneg]
  linarith

lemma potentialLimitSeries_bounded (n : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖potentialLimitSeries n x‖ ≤ ‖x‖⁻¹ + √(n + 1) := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_eq_abs, norm_zero, inv_zero, zero_add]
    rw [abs_of_nonneg (potentialLimitSeries_nonneg _ _)]
    simp [potentialLimitSeries_eq_sqrt_inv]
  · apply (potentialLimitSeries_bounded_neq_zero n x hx).trans
    simp

lemma potentialLimitSeries_isDistBounded (n : ℕ) :
    IsDistBounded (potentialLimitSeries n) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖⁻¹ + √(n + 1))
  · apply IsDistBounded.add
    · apply IsDistBounded.inv
    · apply IsDistBounded.const
  · intro x
    apply (potentialLimitSeries_bounded n x).trans
    apply le_of_eq
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, norm_eq_abs]
    rw [abs_of_nonneg]
    positivity

lemma potentialLimitSeries_fderiv_bounded (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    ‖fderiv ℝ (potentialLimitSeries n) x y‖ ≤ (‖x‖⁻¹) ^ 2 * ‖y‖ := by
  by_cases hx : x = 0
  · subst hx
    rw [potentialLimitSeries_fderiv]
    simp
  trans (‖x‖⁻¹) ^ 3 * ‖x‖ * ‖y‖
  rw [potentialLimitSeries_fderiv_eq_potentialLimitseries_mul]
  simp only [neg_mul, norm_neg, norm_mul, norm_pow, norm_eq_abs, inv_pow]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
  · trans ‖x‖⁻¹ ^ 3
    · refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
      · exact abs_nonneg (potentialLimitSeries n x)
      · simp
      · simp
      · exact potentialLimitSeries_bounded_neq_zero n x hx
    · apply le_of_eq
      exact inv_pow ‖x‖ 3
  · exact abs_real_inner_le_norm x y
  · positivity
  · positivity
  apply le_of_eq
  have hx : 0 < ‖x‖ := by positivity
  field_simp
  ring

lemma potentialLimitSeries_fderiv_isDistBounded (n : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :
    IsDistBounded (fun x => fderiv ℝ (potentialLimitSeries n) x y) := by
  apply IsDistBounded.mono (f := fun x => (‖x‖⁻¹) ^ 2 * ‖y‖)
  · conv => enter [1, x]; rw [mul_comm]
    apply IsDistBounded.const_mul_fun
    convert IsDistBounded.pow (dm1 := 2) (-2) (by simp) using 1
    funext x
    simp
    rfl
  · intro x
    apply (potentialLimitSeries_fderiv_bounded n x y).trans
    simp

/-- A series of functions of the form `fderiv ℝ (fun x => η x * potentialLimitSeries n x) x y`. -/
def potentialLimitSeriesFDerivSchwartz
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  fderiv ℝ (fun x => η x * potentialLimitSeries n x) x y

lemma potentialLimitSeriesFDerivSchwartz_eq
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    potentialLimitSeriesFDerivSchwartz y η n x=
      fderiv ℝ η x y * potentialLimitSeries n x + η x * fderiv ℝ (potentialLimitSeries n) x y := by
  simp [potentialLimitSeriesFDerivSchwartz]
  rw [fderiv_fun_mul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring
  · exact SchwartzMap.differentiableAt η
  · refine Differentiable.differentiableAt ?_
    exact potentialLimitSeries_differentiable n

lemma potentialLimitSeriesFDerivSchwartz_integral_eq_zero
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) (n : ℕ) :
    ∫ (x : EuclideanSpace ℝ (Fin 3)), potentialLimitSeriesFDerivSchwartz y η n x = 0 := by
  conv_lhs => enter [2, x]; rw [potentialLimitSeriesFDerivSchwartz_eq y η n x]
  rw [integral_add, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  simp only [add_neg_cancel]
  · apply IsDistBounded.integrable_fderviv_schwartzMap_mul
    · exact potentialLimitSeries_isDistBounded n
    · exact potentialLimitSeries_aeStronglyMeasurable n
  · apply IsDistBounded.schwartzMap_mul_integrable
    · exact potentialLimitSeries_fderiv_isDistBounded n y
    · exact potentialLimitSeries_fderiv_aeStronglyMeasurable n y
  · apply IsDistBounded.schwartzMap_mul_integrable
    · exact potentialLimitSeries_isDistBounded n
    · exact potentialLimitSeries_aeStronglyMeasurable n
  · exact SchwartzMap.differentiable η
  · exact potentialLimitSeries_differentiable n
  · apply IsDistBounded.integrable_fderviv_schwartzMap_mul
    · exact potentialLimitSeries_isDistBounded n
    · exact potentialLimitSeries_aeStronglyMeasurable n
  · apply IsDistBounded.schwartzMap_mul_integrable
    · exact potentialLimitSeries_fderiv_isDistBounded n y
    · exact potentialLimitSeries_fderiv_aeStronglyMeasurable n y

lemma potentialLimitSeriesFDerivSchwartz_tendsto
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) :
    ∀ᵐ (a : EuclideanSpace ℝ (Fin 3)) ∂(volume),
    Filter.Tendsto (fun n => potentialLimitSeriesFDerivSchwartz y η n a)
      Filter.atTop (𝓝 (fderiv ℝ η a y * ‖a‖⁻¹ + η a * -⟪(‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ)) := by
  rw [Filter.eventually_iff_exists_mem]
  use {0}ᶜ
  constructor
  · rw [compl_mem_ae_iff, measure_singleton]
  intro x hx
  simp at hx
  conv => enter [1, n]; rw [potentialLimitSeriesFDerivSchwartz_eq y η n x]
  apply Filter.Tendsto.add
  · apply Filter.Tendsto.const_mul
    exact potentialLimitSeries_tendsto x hx
  · apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    · exact potentialLimitSeries_fderiv_tendsto x y hx

lemma potentialLimitSeriesFDerivSchwartz_aeStronglyMeasurable
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) (n : ℕ) :
    AEStronglyMeasurable (fun x => potentialLimitSeriesFDerivSchwartz y η n x) := by
  conv => enter [1, x]; rw [potentialLimitSeriesFDerivSchwartz_eq y η n x]
  fun_prop

lemma potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_integral
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) :
    Filter.Tendsto (fun n => ∫ (x : EuclideanSpace ℝ (Fin 3)),
      potentialLimitSeriesFDerivSchwartz y η n x) Filter.atTop
      (𝓝 (∫ (x : EuclideanSpace ℝ (Fin 3)), fderiv ℝ η x y * ‖x‖⁻¹ +
        η x * -⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => ‖fderiv ℝ η x y * ‖x‖⁻¹‖+ ‖η x * (‖x‖⁻¹ ^ 2 * ‖y‖)‖)
    (potentialLimitSeriesFDerivSchwartz_aeStronglyMeasurable y η)
    ?_ ?_
    (potentialLimitSeriesFDerivSchwartz_tendsto y η)
  · apply Integrable.add
    · refine Integrable.norm ?_
      apply IsDistBounded.integrable_fderviv_schwartzMap_mul
      · fun_prop
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine stronglyMeasurable_iff_measurable.mpr ?_
        fun_prop
    · refine Integrable.norm ?_
      apply IsDistBounded.schwartzMap_mul_integrable
      · conv => enter [1, x]; rw [mul_comm]
        refine IsDistBounded.const_mul_fun ?_ ‖y‖
        convert IsDistBounded.pow (dm1 := 2) (-2) (by simp) using 1
        funext x
        simp
        rfl
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine stronglyMeasurable_iff_measurable.mpr ?_
        fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp [potentialLimitSeriesFDerivSchwartz_eq y η n x]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp [abs_mul]
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · rfl
      · exact potentialLimitSeries_bounded_neq_zero n x hx
      · exact abs_nonneg (fderiv ℝ η x y)
      · positivity
    · simp [abs_mul]
      refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · rfl
      · convert potentialLimitSeries_fderiv_bounded n x y
        simp
      · exact abs_nonneg (η x)
      · positivity

lemma potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_zero
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) :
    Filter.Tendsto (fun n => ∫ (x : EuclideanSpace ℝ (Fin 3)),
      potentialLimitSeriesFDerivSchwartz y η n x) Filter.atTop (𝓝 (0)) := by
  conv => enter [1, n]; rw [potentialLimitSeriesFDerivSchwartz_integral_eq_zero y η n]
  simp

lemma electricField_eq_neg_gradD_electricPotential_origin (q ε : ℝ) :
    electricField q ε 0 = - Space.gradD (electricPotential q ε 0) :=
  Eq.symm <|
  gradD_electricPotential_eq_electricField_of_integral_eq_zero q ε <|
  fun η y => tendsto_nhds_unique
    (potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_integral y η)
    (potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_zero y η)

lemma electricField_eq_neg_gradD_electricPotential (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    electricField q ε r₀ = - Space.gradD (electricPotential q ε r₀) := by
  rw [electricField_eq_translateD, electricPotential_eq_translateD]
  simp only [Space.translateD_gradD]
  rw [electricField_eq_neg_gradD_electricPotential_origin]
  simp

lemma electricField_eq_ofPotential_electricPotential (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    electricField q ε r₀ = ofPotential (electricPotential q ε r₀) :=
  electricField_eq_neg_gradD_electricPotential q ε r₀

/-!

## Prove of Gauss' law

We now prove Gauss' law for a point particle in 3-dimensions.

-/

/-- Guass' law for a point particle in 3-dimensions at the origin, that is this theorem states that
  the divergence of `(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r` is equal to `q • δ(r)`. -/
lemma gaussLaw_origin (q ε : ℝ) : (electricField q ε 0).GaussLaw ε (chargeDistribution q 0) := by
  /- The proof here follows that given here: https://math.stackexchange.com/questions/2409008/
  -/
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
    _ = (divD (electricField q ε 0)) η := by rfl
    _ = - ∫ r : Space 3, ⟪((q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r), Space.grad η r⟫_ℝ := by
      rw [electricField, Space.divD_ofFunction]
      simp
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
      convert integrable_isDistBounded_inner_grad_schwartzMap_spherical
          (f := fun r => ‖r‖⁻¹ ^ 3 • r)
        (by
        apply IsDistBounded.congr (f := fun r => ‖r‖ ^ (-2 : ℤ)) (IsDistBounded.pow _ (by simp))
        simp [norm_smul]
        intro x
        by_cases hx : ‖x‖ = 0
        · simp [hx, zpow_two]
        · field_simp [zpow_two]
          ring) (by fun_prop) η
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

lemma gaussLaw (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    (electricField q ε r₀).GaussLaw ε (chargeDistribution q r₀) := by
  rw [electricField_eq_translateD, chargeDistribution_eq_translateD]
  rw [gaussLaw_iff]
  rw [Space.divD_translateD]
  rw [gaussLaw_origin q ε]
  simp

/-!

## Prove of Faraday's law

Faraday's law for a point particle in 3-dimensions follows immediately from the fact that the
electric field is derived from a potential.

-/

lemma faradaysLaw (q ε : ℝ) (r₀ : Space) : (electricField q ε r₀).FaradaysLaw := by
  rw [electricField_eq_ofPotential_electricPotential]
  exact ofPotential_faradaysLaw (electricPotential q ε r₀)
