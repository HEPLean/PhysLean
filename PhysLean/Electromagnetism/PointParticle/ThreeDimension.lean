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

In this module we derive properties of the electrostatics of a point particle of
charge `q` sitting in `3`d space.

### i. Key results

- The electric potential is given by `electricPotential q ε r₀`.
- The electric field is given by `electricField q ε r₀`.
- Gauss's law is given in `gaussLaw`.
- Faraday's law is given in `faradaysLaw`.

### ii. References

- The proof of Gauss' law in this module follows:
  https://math.stackexchange.com/questions/2409008/

-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace ThreeDimPointParticle
open Space StaticElectricField MeasureTheory Real InnerProductSpace
noncomputable section

/-!

## A. Definitions

We start by stating the charge distribution, electric potential and electric field of
the point particle. Later on in this module we will prove that these definitions are
correct, by showing they satisfy the necessary physical properties.

We have the following definitions:
- The `chargeDistribution` is `q δ(r-r₀)`.
- The `electricPotential` is `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹`.
- The `electricField` is `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹ ^ 3 • (r - r₀)`.

-/

/-- The charge distribution of a point particle of charge `q` in 3d space sitting at the `r₀`.
  In the physicists notation this corresponds to the 'function' `q δ(r-r₀)`. -/
def chargeDistribution (q : ℝ) (r₀ : Space) : ChargeDistribution 3 := q • diracDelta ℝ r₀

/-- The electric potential of a point particle of charge `q` in 3d space sitting at the `r₀`.
  In physics notation this corresponds to the 'function' `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹`.
  Here it is defined as the distribution corresponding to that function. -/
def electricPotential (q ε : ℝ) (r₀ : Space) : StaticElectricPotential 3 :=
  distOfFunction (fun r => (q/(4 * π * ε)) • ‖r - r₀‖⁻¹)
  ((IsDistBounded.inv.comp_sub_right (f := fun r => ‖r‖⁻¹) (c := r₀)).const_smul _)

/-- The electric field of a point particle of charge `q` in 3d space sitting at `r₀`.
  In physics notation this corresponds to the 'function'
  `(q/(4 * π * ε)) • ‖r - r₀‖⁻¹ ^ 3 • (r - r₀)`.
  Here it is defined as the distribution corresponding to that function. -/
def electricField (q ε : ℝ) (r₀ : Space) : StaticElectricField 3 :=
  distOfFunction (fun r => (q/(4 * π * ε)) • ‖r - r₀‖⁻¹ ^ 3 • (r - r₀))
  (by
    apply IsDistBounded.const_smul
    apply IsDistBounded.congr (f := fun r => ‖r - r₀‖ ^ (-2 : ℤ))
      (IsDistBounded.pow_shift _ r₀ (by simp))
    · fun_prop
    simp [norm_smul]
    intro x
    by_cases hx : ‖x - r₀‖ = 0
    · simp [hx, zpow_two]
    · field_simp [zpow_two])

/-!

## B. Properties for `q = 0`

We first prove that the charge distribution, electric potential and electric field are
all zero when the charge of the particle is zero.

-/

lemma chargeDistribution_eq_zero_of_charge_eq_zero (r₀ : Space) :
    chargeDistribution 0 r₀ = 0 := by simp [chargeDistribution]

lemma electricPotential_eq_zero_of_charge_eq_zero {ε : ℝ} (r₀ : Space) :
    electricPotential 0 ε r₀ = 0 := by simp [electricPotential]

lemma electricField_eq_zero_of_charge_eq_zero {ε : ℝ} (r₀ : Space) :
    electricField 0 ε r₀ = 0 := by simp [electricField]

/-!

## C. Translations

We now prove that the charge distribution, electric potential and electric field
for the point particle at `r₀` is just the translation of the charge distribution,
electric potential and electric field for the point particle located at `0`.

-/

lemma chargeDistribution_eq_translateD (q : ℝ) (r₀ : Space) :
    chargeDistribution q r₀ = Space.translateD r₀
      (chargeDistribution q 0) := by
  ext η
  simp [chargeDistribution, Space.translateD_apply]

lemma electricPotential_eq_translateD (q ε : ℝ) (r₀ : Space) :
    electricPotential q ε r₀ = Space.translateD r₀ (electricPotential q ε 0) := by
  ext η
  simp [electricPotential]
  rw [Space.translateD_ofFunction]

lemma electricField_eq_translateD (q ε : ℝ) (r₀ : Space) :
    electricField q ε r₀ = Space.translateD r₀ (electricField q ε 0) := by
  ext η
  simp [electricField]
  rw [Space.translateD_ofFunction]

open InnerProductSpace

open scoped Topology BigOperators FourierTransform

/-!

## D. Proving the gradient of the potential is the electric field

We now prove that the electric field is equal to the negative gradient of the potential,
i.e. `E = -∇φ`.

-/

/-!

### D.1. Reducing the problem to showing an integral is zero

Until the very end of this problem we will implicitly assume that `r₀ = 0`.
We generalize at the end.

The first step of our proof is to show that `E = -∇φ` if for any Schwartz map `η` and direction `y`
the integral
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ = 0`
is equal to zero.

Recall that a 'Schwartz map' is a smooth function which, along with all it's
derivatives, decays fast. It's presence here is because the electric field and potential
are defined as distributions, and distributions are defined by how they act on Schwartz maps.

-/

/--
  The relation `E = -∇φ` holds for the point particle if the integral
  `∫ x, d_y η x * ‖x‖⁻¹ + η x * -⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ = 0`
  is zero.
-/
lemma distGrad_electricPotential_eq_electricField_of_integral_eq_zero (q ε : ℝ)
    (h_integral : ∀ η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ), ∀ y : EuclideanSpace ℝ (Fin 3),
    ∫ (a : EuclideanSpace ℝ (Fin 3)), (fderivCLM ℝ η a y * ‖a‖⁻¹ +
    η a * - ⟪(‖a‖ ^ 3)⁻¹ • a, y⟫_ℝ) = 0) :
    - Space.distGrad (electricPotential q ε 0) = electricField q ε 0 := by
  rw [← sub_eq_zero]
  ext1 η
  apply ext_inner_right ℝ
  intro y
  simp [inner_sub_left, distGrad_inner_eq, fderivD_apply]
  dsimp [electricPotential, electricField]
  rw [distOfFunction_inner, distOfFunction_apply]
  simp only [smul_eq_mul, inv_pow]
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
  apply IsDistBounded.integrable_space
  · simp only [sub_zero]
    change IsDistBounded fun x => (q / (4 * π * ε)) • ‖x‖⁻¹
    apply IsDistBounded.const_smul
    fun_prop
  apply IsDistBounded.integrable_space
  · apply IsDistBounded.inner_left
    apply IsDistBounded.const_smul
    apply IsDistBounded.congr (f := fun r => ‖r‖ ^ (-2 : ℤ)) (IsDistBounded.pow _ (by simp))
    · fun_prop
    simp [norm_smul]
    intro x
    by_cases hx : ‖x‖ = 0
    · simp [hx, zpow_two]
    · field_simp [zpow_two]

/-!

### D.2. A smooth approximation to `‖r‖⁻¹`

Notice that in the integral
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ = 0`
the integrand is has the structure of the total derivative of the function
`η r * ‖r‖⁻¹` in the direction `y`, i.e. `d_y (η r * ‖r‖⁻¹)`.

However, this does not quite work because `‖r‖⁻¹` is not differentiable at `r = 0`.
To get around this we define a sequence of functions, which for `n : ℕ` are given by
`potentialLimitSeries n r = (‖r‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ)`.

The overall aim will be to write `∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ`
as the limit of the integrals
`∫ r, d_y η r * potentialLimitSeries n r + η r * d_y (potentialLimitSeries n) r y`
as `n → ∞`, and then show that each of these integrals is zero because they
are integrals of total derivatives of differentiable functions.

-/

/-- A series of functions whose limit is the `‖x‖⁻¹` and for which each function is
  differentiable everywhere. -/
def potentialLimitSeries : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ := fun n x =>
  (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ)

lemma potentialLimitSeries_eq (n : ℕ) :
    potentialLimitSeries n = fun x => (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ) := rfl

/-!

#### Part D.2.I.
The most important property of `potentialLimitSeries` is that it converges to `‖x‖⁻¹` as
`n → ∞`. That is, it approximates `‖x‖⁻¹` arbitrarily closely for large enough `n`.

-/

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
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  left
  simpa using hx

/-!

#### Part D.2.II.
Unlike `‖r‖⁻¹`, importantly the functions `potentialLimitSeries n` are
differentiable everywhere.

-/

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

/-!

#### Part D.2.III.
  The derivative of `potentialLimitSeries n` in the direction `y` is given by
  `- (‖r‖^1 + 1/(1 + n))^(-3/2) * ⟪r, y⟫_ℝ`, or equivalently
  `- (potentialLimitSeries n r) ^ 3 * ⟪r, y⟫_ℝ`.

-/

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

/-!

#### Part D.2.IV.
  as `n → ∞` the limit of the derivative of `potentialLimitSeries n` in the direction `y` is
  `-⟪(‖x‖ ^ 3)⁻¹ • x, y⟫_ℝ`. This is exactly the derivative of `‖x‖⁻¹`
  in the direction `y`, when it exists (i.e. when `x ≠ 0`).

-/

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

/-!

#### Part D.2.V

Because we are integrating, we need to show some integrability and measurability properties
of `potentialLimitSeries` and it's derivative.

We first show that they are almost everywhere strongly measurable.

-/

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

/-!

#### Part D.2.VI.

We now show that `potentialLimitSeries` satisfies the condition `IsDistBounded`.
Along with the fact it is almost everywhere strongly measurable, this means
it can be made into a tempered distribution, but for our purposes means that it is
integrable when multiplied by a Schwartz map.

There are a number of precursory lemmas first.

-/

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

@[fun_prop]
lemma potentialLimitSeries_isDistBounded (n : ℕ) :
    IsDistBounded (potentialLimitSeries n) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖⁻¹ + √(n + 1))
  · apply IsDistBounded.add
    · apply IsDistBounded.inv
    · apply IsDistBounded.const
  · fun_prop
  · intro x
    apply (potentialLimitSeries_bounded n x).trans
    apply le_of_eq
    simp only [norm_eq_abs]
    rw [abs_of_nonneg]
    positivity

/-!

#### Part D.2.VII.

In a similar fashion, and for the same reason,
we now show that the derivative of `potentialLimitSeries` satisfies the condition `IsDistBounded`.

-/

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

@[fun_prop]
lemma potentialLimitSeries_fderiv_isDistBounded (n : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :
    IsDistBounded (fun x => fderiv ℝ (potentialLimitSeries n) x y) := by
  apply IsDistBounded.mono (f := fun x => (‖x‖⁻¹) ^ 2 * ‖y‖)
  · conv => enter [1, x]; rw [mul_comm]
    apply IsDistBounded.const_mul_fun
    convert IsDistBounded.pow (d := 3) (-2) (by simp) using 1
    funext x
    simp
    rfl
  · fun_prop
  · intro x
    apply (potentialLimitSeries_fderiv_bounded n x y).trans
    simp

/-!

### D.3. A series of integrals

We now show that the integral
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ` is the limit of the integrals
`∫ r, d_y (η r * potentialLimitSeries n r)` as `n → ∞`.

-/

/-!
#### Part D.3.I.

We first define a series of functions which are the integrands of
`∫ r, d_y (η r * potentialLimitSeries n r)`.
These functions are `potentialLimitSeriesFDerivSchwartz y η n r`.

-/

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

/-!
#### Part D.3.II.

We show that these integrands converge to the integrand of
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ` as `n → ∞`.

-/
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

/-!

#### Part D.3.III.

We use 'Lebesgue dominated convergence theorem' to show that the integrals
`∫ r, d_y (η r * potentialLimitSeries n r)` converge to the integral
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ` as `n → ∞`.

This requires some measurability properties of `potentialLimitSeriesFDerivSchwartz`
and uses the integrability properties of `potentialLimitSeries` and
its derivative shown above.

-/

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
      fun_prop
    · refine Integrable.norm ?_
      apply IsDistBounded.integrable_space
      · conv => enter [1, x]; rw [mul_comm]
        refine IsDistBounded.const_mul_fun ?_ ‖y‖
        convert IsDistBounded.pow (d := 3) (-2) (by simp) using 1
        funext x
        simp
        rfl
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

/-!

### D.4. The limit of the series of integrals is zero

Above we showed that the limit of the integrals
`∫ r, d_y (η r * potentialLimitSeries n r)` as `n → ∞` is
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ`.
We now show that this same limit is zero.

-/

/-!
#### Part D.4.I.

The integral
`∫ r, d_y (η r * potentialLimitSeries n r)` is zero for each `n : ℕ`.
This follows because this integrand is the total derivative of a differentiable function.
-/

lemma potentialLimitSeriesFDerivSchwartz_integral_eq_zero
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) (n : ℕ) :
    ∫ (x : EuclideanSpace ℝ (Fin 3)), potentialLimitSeriesFDerivSchwartz y η n x = 0 := by
  conv_lhs => enter [2, x]; rw [potentialLimitSeriesFDerivSchwartz_eq y η n x]
  rw [integral_add (by fun_prop) (by fun_prop),
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (by fun_prop)
      (by fun_prop) (by fun_prop) η.differentiable (potentialLimitSeries_differentiable n)]
  simp only [add_neg_cancel]

/-!
#### Part D.4.II.

From part D.4.I it follows that the limit of the integrals
`∫ r, d_y (η r * potentialLimitSeries n r)` as `n → ∞` is zero, since each
individual integral is zero.

-/
lemma potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_zero
    (y : EuclideanSpace ℝ (Fin 3)) (η : 𝓢(EuclideanSpace ℝ (Fin 3), ℝ)) :
    Filter.Tendsto (fun n => ∫ (x : EuclideanSpace ℝ (Fin 3)),
      potentialLimitSeriesFDerivSchwartz y η n x) Filter.atTop (𝓝 (0)) := by
  conv => enter [1, n]; rw [potentialLimitSeriesFDerivSchwartz_integral_eq_zero y η n]
  simp

/-!

### D.5. E = -∇ V for a particle at the origin

We now put everything together. In part D.1 we showed that `E = -∇ V` follows from the integral
`∫ r, d_y η r * ‖r‖⁻¹ + η r * -⟪(‖r‖ ^ 3)⁻¹ • x, r⟫_ℝ = 0` for all Schwartz maps `η` and
directions `y`.
In part D.3 we showed that this integral is the limit of the integrals
`∫ r, d_y (η r * potentialLimitSeries n r)` as `n → ∞`.
In part D.4 we showed that this limit is zero, and therefore this integral itself must be zero.

It follows that `E = -∇ V` for a particle at the origin.

-/
lemma electricField_eq_neg_distGrad_electricPotential_origin (q ε : ℝ) :
    electricField q ε 0 = - Space.distGrad (electricPotential q ε 0) :=
  Eq.symm <|
  distGrad_electricPotential_eq_electricField_of_integral_eq_zero q ε <|
  fun η y => tendsto_nhds_unique
    (potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_integral y η)
    (potentialLimitSeriesFDerivSchwartz_integral_tendsto_eq_zero y η)

/-!

### D.6. E = -∇ V for a particle at r₀

The general case of a particle at `r₀` follows from the case of a particle at the origin
by using that the gradient commutes with translation.

-/
lemma electricField_eq_neg_distGrad_electricPotential (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    electricField q ε r₀ = - Space.distGrad (electricPotential q ε r₀) := by
  rw [electricField_eq_translateD, electricPotential_eq_translateD]
  simp only [Space.translateD_distGrad]
  rw [electricField_eq_neg_distGrad_electricPotential_origin]
  simp

lemma electricField_eq_ofPotential_electricPotential (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    electricField q ε r₀ = ofPotential (electricPotential q ε r₀) :=
  electricField_eq_neg_distGrad_electricPotential q ε r₀

/-!

## E. Faraday's law

Faraday's law, which says that `∇ × E = 0`,
is an immediate consequence of the fact that `E = -∇ V`, because
the curl of a gradient is always zero.

-/

lemma faradaysLaw (q ε : ℝ) (r₀ : Space) : (electricField q ε r₀).FaradaysLaw := by
  rw [electricField_eq_ofPotential_electricPotential]
  exact ofPotential_faradaysLaw (electricPotential q ε r₀)

/-!

## F. Gauss' law

We now prove Gauss' law for a point particle in 3-dimensions. Recall that Gauss' law states that
the divergence of the electric field is equal to the charge density divided by the permittivity,
i.e. `∇ • E = ρ/ε`.

In this case, this result is related to the sometimes confusing fact that
`∇ • ((‖r‖⁻¹) ^ 3 • r) ∝ δ(r)`.

We first prove Gauss' law for a point particle at the origin, and then use translation to
prove it for a point particle at `r₀`.

-/

/-!

### F.1. Gauss' law for a point particle at the origin

The proof of Gauss' law for a point particle at the origin follows the proof given here:
https://math.stackexchange.com/questions/2409008/

We highlight the main steps of the proof here (the below comments also appear
in-line within the proof) :
- **Step 1**: `∇ ⬝ E = 1/ε ρ` if for all Schwartz maps`η`, `∇ ⬝ E η = (1/ε ρ) η`.
- **Step 2**: We focus on rewriting the LHS, by definition it is equal to
    `- ∫ d³r ⟪(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r, (∇ η) r⟫`
- **Step 3**: We rearrange the integral to
    `- q/(4 * π * ε) * ∫ d³r ‖r‖⁻¹ ^ 2 * ⟪‖r‖⁻¹ • r), (∇ η) r⟫`
- **Step 4**: We use that `⟪‖r‖⁻¹ • r), (∇ η) r⟫ = (d(η (a • ‖r‖⁻¹ • r))/d a)_‖r‖`
    to rewrite the integral as
    `- q/(4 * π * ε) * ∫ d³r ‖r‖⁻¹ ^ 2 * (d(η (a • ‖r‖⁻¹ • r))/d a)_‖r‖`.
- **Step 5**: We move over to spherical coordinates rewriting
      `d³r` as `r² dr dn` where `dn` is the integral over the unit vectors `n`.
      In `d³r` the `r` is a vector whilst in `r² dr dn` the `r` is a scalar (the distance).
      `- q/(4 * π * ε) * ∫ dr² dr dn r⁻¹ ^ 2 * (d(η (a • n))/d a)_r`
- **Step 6**: The integral is rearranged to
      `- q/(4 * π * ε) * ∫ dn (∫_0^∞ r² dr r⁻¹ ^ 2 * (d(η (a • n))/d a)_r)`
- **Step 7**: The integral is further rearranged to
    `- q/(4 * π * ε) * ∫ dn (∫_0^∞ dr (d(η (a • n))/d a)_r)`
- **Step 8**: The inner integral `(∫_0^∞ dr (d(η (a • n))/d a)_r)` is an integral over
      a total derivative of a function which tends to zero at infinity,
      and so is equal to `-η 0`. Thus the integral is equal to
      `- q/(4 * π * ε) * ∫ dn (-η 0)`.
- **Step 9**: The integral `∫ dn` is equal to the surface area of the unit sphere, which is
      `4 * π`. And thus we get after some simplification
      `(q/ε) * η 0`.
- **Step 10**: This is manifestly equal to the right hand side `1/ε ρ η` since `ρ = q δ(r)`,
    thereby proving the result.

-/

set_option maxHeartbeats 400000 in
/-- Gauss' law for a point particle in 3-dimensions at the origin, that is this theorem states that
  the divergence of `(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r` is equal to `q • δ(r)`. -/
lemma gaussLaw_origin (q ε : ℝ) : (electricField q ε 0).GaussLaw ε (chargeDistribution q 0) := by
  /- Step 1: `∇ ⬝ E = 1/ε ρ` if for all Schwartz maps`η`, `∇ ⬝ E η = (1/ε ρ) η`. -/
  ext η
  /- Preliminary definitions. -/
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
    _ = (distDiv (electricField q ε 0)) η := by rfl
    /- Step 2: We focus on rewriting the LHS, by definition it is equal to
      `- ∫ d³r ⟪(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r, (∇ η) r⟫`. -/
    _ = - ∫ r, ⟪(q/(4 * π * ε)) • ‖r‖⁻¹ ^ 3 • r, Space.grad η r⟫_ℝ := by
      rw [electricField, Space.distDiv_ofFunction]
      simp
    /- Step 3: We rearrange the integral to
      `- q/(4 * π * ε) * ∫ d³r ‖r‖⁻¹ ^ 2 * ⟪‖r‖⁻¹ • r), (∇ η) r⟫`. -/
    _ = - (q/(4 * π * ε)) * ∫ r : Space 3, ‖r‖⁻¹ ^ 2 * ⟪‖r‖⁻¹ • r, Space.grad η r⟫_ℝ := by
      simp [inner_smul_left, integral_const_mul]
      left
      congr
      funext r
      ring
    /- Step 4: We use that `⟪‖r‖⁻¹ • r), (∇ η) r⟫ = (d(η (a • ‖r‖⁻¹ • r))/d a)_‖r‖`
      to rewrite the integral as
      `- q/(4 * π * ε) * ∫ d³r ‖r‖⁻¹ ^ 2 * (d(η (a • ‖r‖⁻¹ • r))/d a)_‖r‖`. -/
    _ = - (q/(4 * π * ε)) * ∫ r : Space 3, ‖r‖⁻¹ ^ 2 *
        (_root_.deriv (fun a => η (a • ‖r‖⁻¹ • r)) ‖r‖) := by
      congr
      funext r
      congr
      rw [real_inner_comm, ← grad_inner_space_unit_vector _ _ (SchwartzMap.differentiable η)]
    /- Step 5: We move over to spherical coordinates rewriting
      `d³r` as `r² dr dn` where `dn` is the integral over the unit vectors `n`.
      In `d³r` the `r` is a vector whilst in `r² dr dn` the `r` is a scalar (the distance).
      `- q/(4 * π * ε) * ∫ dr² dr dn r⁻¹ ^ 2 * (d(η (a • n))/d a)_r` -/
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
    /- Step 6: The integral is rearranged to
      `- q/(4 * π * ε) * ∫ dn (∫_0^∞ r² dr r⁻¹ ^ 2 * (d(η (a • n))/d a)_r)` -/
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
        · fun_prop
        simp [norm_smul]
        intro x
        by_cases hx : ‖x‖ = 0
        · simp [hx, zpow_two]
        · field_simp [zpow_two]) η
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
        simp
      rw [← grad_inner_space_unit_vector]
      rw [real_inner_comm]
      simp [inner_smul_left, x, norm_smul, abs_of_nonneg (le_of_lt hr)]
      field_simp
      exact SchwartzMap.differentiable η
    /- Step 7: The integral is further rearranged to
      `- q/(4 * π * ε) * ∫ dn (∫_0^∞ dr (d(η (a • n))/d a)_r)` -/
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
      simp only [smul_eq_mul]
      field_simp
      congr
      rw [abs_of_nonneg]
      have h1 := r.2
      simp [- Subtype.coe_prop] at h1
      exact le_of_lt h1
      fun_prop
    /- Step 8: The inner integral `(∫_0^∞ dr (d(η (a • n))/d a)_r)` is an integral over
      a total derivative of a function which tends to zero at infinity,
      and so is equal to `-η 0`. Thus the integral is equal to
      `- q/(4 * π * ε) * ∫ dn (-η 0) ` -/
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
      /- Step 9: The integral `∫ dn` is equal to the surface area of the unit sphere, which is
      `4 * π`. And thus we get after some simplification
      `(q/ε) * η 0` -/
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
  /- Step 10: This is manifestly equal to the right hand side `1/ε ρ η` since `ρ = q δ(r)`,
    thereby proving the result. -/
  simp [chargeDistribution]
  ring

/-!

### F.2. Gauss' law for a point particle at `r₀`

We now show Gauss' law for a point particle at `r₀`.
This follows from the case of a point particle at the origin
by using that the divergence commutes with translation.

-/

lemma gaussLaw (q ε : ℝ) (r₀ : EuclideanSpace ℝ (Fin 3)) :
    (electricField q ε r₀).GaussLaw ε (chargeDistribution q r₀) := by
  rw [electricField_eq_translateD, chargeDistribution_eq_translateD]
  rw [gaussLaw_iff]
  rw [Space.distDiv_translateD]
  rw [gaussLaw_origin q ε]
  simp

/-!

## G. Rotational invariance

We now prove the electric field, charge distribution and potential of a point particle
are rotationally invariant.

This is yet to be done, and is a TODO item.

-/

/-- The electrostatic field of a point particle is rotationally invariant. -/
informal_lemma electricField_rotationally_invariant where
  deps := [``electricField]
  tag := "L7NXF"
