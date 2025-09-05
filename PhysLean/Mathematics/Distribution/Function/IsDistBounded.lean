/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Basic
import PhysLean.Mathematics.Distribution.Function.InvPowMeasure
import PhysLean.Meta.Linters.Sorry
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

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

namespace Distribution

variable [NormedSpace ℝ E]

open MeasureTheory

/-!

## IsBounded

-/

/-- The boundedness condition on a function ` EuclideanSpace ℝ (Fin dm1.succ) → F`
  for it to form a distribution. -/
@[fun_prop]
def IsDistBounded {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F) : Prop :=
    ∃ n, ∃ c : Fin n → ℝ, ∃ g : Fin n → EuclideanSpace ℝ (Fin dm1.succ),
    ∃ p : Fin n → ℤ,
    (∀ i, 0 ≤ c i) ∧
    (∀ i, -dm1 ≤ p i) ∧
     ∀ x, ‖f x‖ ≤ ∑ i, c i * ‖x + g i‖ ^ p i

@[fun_prop]
lemma IsDistBounded.add {dm1 : ℕ} {f g : EuclideanSpace ℝ (Fin dm1.succ) → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  rcases hg with ⟨n2, c2, g2, p2, c2_nonneg, p2_bound, bound2⟩
  refine ⟨n1 + n2, Fin.append c1 c2, Fin.append g1 g2, Fin.append p1 p2, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp
      exact c1_nonneg i
    | .inr i =>
      simp
      exact c2_nonneg i
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp
      exact p1_bound i
    | .inr i =>
      simp
      exact p2_bound i
  · intro x
    apply (norm_add_le _ _).trans
    apply (add_le_add (bound1 x) (bound2 x)).trans
    apply le_of_eq
    rw [← finSumFinEquiv.sum_comp ]
    simp

@[fun_prop]
lemma IsDistBounded.const_smul {dm1 : ℕ} [NormedSpace ℝ F] {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (c • f) := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  refine ⟨n1 , ‖c‖ • c1, g1, p1, ?_, p1_bound, ?_⟩
  · intro i
    simp
    have hi := c1_nonneg i
    positivity
  · intro x
    simp [norm_smul]
    conv_rhs => enter [2, x]; rw [mul_assoc]
    rw [← Finset.mul_sum]
    refine mul_le_mul (by rfl) (bound1 x) ?_ ?_
    · exact norm_nonneg (f x)
    · exact abs_nonneg c

lemma IsDistBounded.comp_add_right {dm1 : ℕ} {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    (hf : IsDistBounded f) (c : EuclideanSpace ℝ (Fin dm1.succ)) :
    IsDistBounded (fun x => f (x + c)) := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  refine ⟨n1, c1, fun i => g1 i + c, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  apply (bound1 (x + c)).trans
  apply le_of_eq
  simp
  congr 1
  funext x
  congr 3
  module

@[fun_prop]
lemma IsDistBounded.const_mul_fun {dm1 : ℕ}
    {f : EuclideanSpace ℝ (Fin dm1.succ) → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c * f x) := by
  convert hf.const_smul c using 1

lemma IsDistBounded.congr {dm1 : ℕ} {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    {g : EuclideanSpace ℝ (Fin dm1.succ) → F'}
    (hf : IsDistBounded f) (hfg : ∀ x, ‖g x‖ = ‖f x‖) : IsDistBounded g := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  rw [hfg x]
  exact bound1 x

lemma IsDistBounded.mono {dm1 : ℕ} {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    {g : EuclideanSpace ℝ (Fin dm1.succ) → F'}
    (hf : IsDistBounded f) (hfg : ∀ x, ‖g x‖ ≤ ‖f x‖) : IsDistBounded g := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  exact (hfg x).trans (bound1 x)

open InnerProductSpace
@[fun_prop]
lemma IsDistBounded.inner_left {dm1 n : ℕ}
    {f : EuclideanSpace ℝ (Fin dm1.succ) → EuclideanSpace ℝ (Fin n) }
    (hf : IsDistBounded f) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ) := by
  rcases hf with ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩
  refine ⟨n1, fun i => ‖y‖ * c1 i, g1, p1, ?_, p1_bound, ?_⟩
  · intro i
    simp
    have hi := c1_nonneg i
    positivity
  · intro x
    apply (norm_inner_le_norm (f x) y).trans
    rw [mul_comm]
    simp
    conv_rhs => enter [2, i]; rw [mul_assoc]
    rw [← Finset.mul_sum]
    refine mul_le_mul (by rfl) (bound1 x) ?_ ?_
    · exact norm_nonneg (f x)
    · exact norm_nonneg y

/-!

## Specific cases

-/

TODO "LSLHW" "The proof `IsDistBounded.pow` needs golfing."

@[fun_prop]
lemma IsDistBounded.const {dm1 : ℕ} (f : F) :
    IsDistBounded (dm1 := dm1) (fun _ : EuclideanSpace ℝ (Fin dm1.succ) => f) := by
  use 1, fun _ => ‖f‖, fun _ => 0, fun _ => 0
  simp

@[fun_prop]
lemma IsDistBounded.pow {dm1 : ℕ} (n : ℤ) (hn : - dm1 ≤ n) :
    IsDistBounded (dm1 := dm1) (fun x => ‖x‖ ^ n) := by
  refine ⟨1, fun _ => 1, fun _ => 0, fun _ => n, ?_, ?_, ?_⟩
  · simp
  · simp
    exact hn
  · intro x
    simp

@[fun_prop]
lemma IsDistBounded.inv {n : ℕ} :
    IsDistBounded (dm1 := n.succ) (fun x => ‖x‖⁻¹) := by
  convert IsDistBounded.pow (dm1 := n.succ) (-1) (by simp) using 1
  ext1 x
  simp

/-!

## Integrability

-/

private lemma schwartzMap_mul_pow_integrable {dm1 : ℕ} (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ))
    (p : ℤ) (hp : - (dm1 : ℤ) ≤ p) :
    Integrable (fun x => ‖η x‖ * ‖x‖ ^ p) volume := by
  by_cases hp : p = 0
  · subst hp
    simp only [Nat.succ_eq_add_one, zpow_zero, mul_one]
    apply Integrable.norm
    exact η.integrable
  suffices h1 : Integrable (fun x => ‖η x‖ * ‖x‖ ^ (p + dm1)) (invPowMeasure (dm1 := dm1)) by
    rw [invPowMeasure] at h1
    erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)] at h1
    convert h1 using 1
    funext x
    simp
    rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
    simp
    ring_nf
    rw [mul_assoc]
    congr
    have hx : 0 ≤ ‖x‖  := norm_nonneg x
    generalize ‖x‖ = r at *
    by_cases hr : r = 0
    · subst hr
      simp
      rw [zero_pow_eq, zero_zpow_eq, zero_zpow_eq]
      split_ifs <;> simp
      any_goals omega
    · field_simp
      rw [zpow_add₀ hr]
      simp
    · simp
  convert integrable_pow_mul_iteratedFDeriv invPowMeasure η (p + dm1).toNat 0 using 1
  funext x
  simp
  rw [mul_comm]
  congr 1
  rw [← zpow_natCast]
  congr
  refine Int.eq_natCast_toNat.mpr ?_
  omega


lemma IsDistBounded.schwartzMap_mul_integrable_norm {dm1 : ℕ}
    {η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)}
    {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    Integrable (fun x => ‖η x‖ * ‖f x‖ ) volume := by
  rcases hf with ⟨n, c, g, p, c_nonneg, p_bound, hbound⟩
  apply Integrable.mono' (g := fun x =>  ∑ i, ‖η x‖ * (c i * ‖x + g i‖ ^ p i)) _
  · fun_prop
  · filter_upwards with x
    rw [← Finset.mul_sum]
    simp
    exact mul_le_mul (by rfl) (hbound x) (norm_nonneg _) (abs_nonneg _)
  · apply MeasureTheory.integrable_finset_sum
    intro i _
    conv =>
      enter [1, x]
      rw [← mul_assoc, mul_comm _ (c i), mul_assoc]
    apply Integrable.const_mul
    suffices h1 : Integrable (fun x => ‖η ((x + g i) - g i)‖ * ‖x + g i‖ ^ p i) volume by
      convert h1 using 1
      simp
    apply MeasureTheory.Integrable.comp_add_right (g :=  g i) (f := fun x => ‖η (x - g i)‖ * ‖x‖ ^ p i)
    let η' := SchwartzMap.compCLM (𝕜 := ℝ)
      (g := fun x => x - g i)
      (by
        apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖g i‖)
        · have hx : (fderiv ℝ (fun x => x - g i)) = fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (dm1 + 1))) := by
            funext x
            simp
            erw [fderiv_sub]
            simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, sub_zero]
            fun_prop
            fun_prop
          rw [hx]
          exact
            Function.HasTemperateGrowth.const
              (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (dm1 + 1))))
        · fun_prop
        · intro x
          simp
          trans ‖x‖ + ‖g i‖
          · apply norm_sub_le
          simp [mul_add, add_mul]
          trans 1 + (‖x‖ + ‖g i‖)
          · simp
          trans (1 + (‖x‖ + ‖g i‖)) + ‖x‖ * ‖g i‖
          · simp
            positivity
          ring_nf
          rfl) (by
          simp
          use 1, (1 + ‖g i‖)
          intro x
          simp
          apply (norm_le_norm_add_norm_sub' x (g i)).trans
          trans 1 + (‖g i‖ + ‖x - g i‖)
          · simp
          trans (1 + (‖g i‖ + ‖x - g i‖)) + ‖g i‖ * ‖x - g i‖
          · simp
            positivity
          ring_nf
          rfl ) η
    exact schwartzMap_mul_pow_integrable η' (p i) (p_bound i)

lemma IsDistBounded.schwartzMap_smul_integrable {dm1 : ℕ}
    {η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)}
    {f : EuclideanSpace ℝ (Fin dm1.succ) → F}
    (hf : IsDistBounded f) [NormedSpace ℝ F]
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    Integrable (fun x => η x • f x) volume := by
  rw [← MeasureTheory.integrable_norm_iff ]
  convert hf.schwartzMap_mul_integrable_norm (η := η) hae using 1
  funext x
  simp [norm_smul]
  fun_prop

@[fun_prop]
lemma IsDistBounded.schwartzMap_mul_integrable {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → ℝ)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume)
    (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin dm1.succ) => η x * f x) := by
  convert hf.schwartzMap_smul_integrable (η := η) hae using 1

@[fun_prop]
lemma IsDistBounded.integrable_fderviv_schwartzMap_mul {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → ℝ)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume)
    (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) (y : EuclideanSpace ℝ (Fin dm1.succ)):
    Integrable (fun x : EuclideanSpace ℝ (Fin dm1.succ) => fderiv ℝ η x y * f x) := by
  exact hf.schwartzMap_smul_integrable hae
    (η := ((SchwartzMap.evalCLM (𝕜 := ℝ) y) ((fderivCLM ℝ) η)))

/-!


## Integrability of 1/(1 + ‖x‖)
-/

lemma intergrable_pow {dm1 : ℕ} (p: ℤ) (r : ℕ) (p_bound : -dm1 ≤ p)
    (r_bound : (p + ↑dm1).toNat + (invPowMeasure (dm1 := dm1)).integrablePower ≤ r)
    (v : EuclideanSpace ℝ (Fin dm1.succ)) :
    Integrable (fun x => ‖x + v‖ ^ p  * ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
  let m := (invPowMeasure (dm1 := dm1)).integrablePower
  have h0  (q : ℕ) : Integrable (fun x => ‖x‖ ^ q * ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖) invPowMeasure := by
    have hr1  (x : EuclideanSpace ℝ (Fin dm1.succ)):
        ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖ = ((1 + ‖x - v‖) ^ (q + m))⁻¹ := by
      simp
      rw [abs_of_nonneg (by positivity)]
    apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ :=2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + 1))
    · simp
      intro x
      refine inv_le_one_of_one_le₀ ?_
      rw [abs_of_nonneg (by positivity)]
      refine one_le_pow₀ ?_
      simp
    · intro x
      rw [hr1]
      refine mul_inv_le_of_le_mul₀ ?_ (by positivity) ?_
      · positivity
      change ‖x‖^ (q + m) ≤ _
      by_cases hzero : m = 0 ∧ q = 0
      · rcases hzero with ⟨hm, hq⟩
        generalize hm : m = m' at *
        subst hm hq
        rw [pow_zero, pow_zero]
        simp
      trans (‖v‖ + ‖x - v‖) ^ (q + m)
      · rw [pow_le_pow_iff_left₀]
        · apply norm_le_norm_add_norm_sub'
        · positivity
        · positivity
        simp
        intro hq
        omega
      apply (add_pow_le _ _ _).trans
      trans 2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + ‖x - v‖ ^ (q + m)) + (2 ^ (q + m - 1)
         + 2 ^ (q + m - 1) * ‖v‖ ^ (q + m) * ‖x - v‖ ^ (q + m ))
      · simp
        positivity
      trans (2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + 1)) * (1 + ‖x - v‖ ^ (q + m))
      · ring_nf
        apply le_of_eq
        rfl
      refine mul_le_mul_of_nonneg (by rfl) ?_ ?_ ?_
      · trans 1 ^ (q + m) + ‖x - v‖ ^ (q + m)
        · simp
        apply pow_add_pow_le
        · simp
        · positivity
        · simp
          omega
      · positivity
      · positivity
      · positivity
      · positivity
    · refine Measurable.aestronglyMeasurable ?_
      fun_prop
  have h0' (q : ℕ) :
      Integrable (fun x => ‖x‖ ^ (q - dm1 : ℤ) * ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖) volume := by
    specialize h0 q
    rw [invPowMeasure] at h0
    rw [MeasureTheory.integrable_withDensity_iff] at h0
    apply Integrable.congr h0
    rw [Filter.eventuallyEq_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp
    simp at hx
    field_simp
    have hx': ‖x‖ ≠ 0 := by simpa using hx
    rw [zpow_sub₀ hx']
    field_simp
    ring
    · fun_prop
    · filter_upwards with x
      simp
  have h2 (q : ℕ) : Integrable (fun x => ‖x + v‖ ^ (q - dm1 : ℤ)
      * ‖((1 + ‖x‖) ^ (q + (invPowMeasure (dm1 := dm1)).integrablePower))⁻¹‖) volume := by
    convert (h0' q).comp_add_right v using 1
    funext x
    simp [m]
  apply Integrable.mono' (h2 (p + dm1).toNat)
  · fun_prop
  rw [Filter.eventually_iff_exists_mem]
  use {0}ᶜ
  constructor
  · rw [compl_mem_ae_iff, measure_singleton]
  intro x hx
  refine norm_mul_le_of_le ?_ ?_
  simp
  apply le_of_eq
  congr
  rw [max_eq_left]
  simp
  omega
  simp
  refine inv_pow_le_inv_pow_of_le ?_ ?_
  · rw [abs_of_nonneg (by positivity)]
    simp
  · exact r_bound

lemma IsDistBounded.norm__inv_mul_exists_pow_integrable {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → ℝ)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    ∃ r, Integrable (fun x => f x * ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
  rcases hf with ⟨n, c, g, p, c_nonneg, p_bound, hbound⟩
  induction' n

  let pMax := Finset.max' (Finset.image p Finset.univ)
  have pMax_max (i : Fin n) : p i ≤ pMax := by
    simp [pMax]
    apply?
open InnerProductSpace

end Distribution
