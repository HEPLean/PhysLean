/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Function.IsDistBounded
/-!

# Distributions from bounded functions

In this module we define distributions from functions `f : EuclideanSpace ℝ (Fin d.succ) → F`
whose norm is bounded by `c1 * ‖x‖ ^ (-d : ℝ) + c2 * ‖x‖ ^ n`
for some constants `c1`, `c2` and `n`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## Key definition

- `ofFunction`: Creates a distribution from a `f` satisfying `IsDistBounded f`.

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Distribution

open MeasureTheory

/-- A distribution `(EuclideanSpace ℝ (Fin 3)) →d[ℝ] F` from a function
  `f : EuclideanSpace ℝ (Fin 3) → F` bounded by `c1 * ‖x‖ ^ (-2 : ℝ) + c2 * ‖x‖ ^ n`.
-/
def ofFunction {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) :
    (EuclideanSpace ℝ (Fin dm1.succ)) →d[ℝ] F := by
  refine mkCLMtoNormedSpace (fun η => ∫ x, η x • f x) ?_ ?_ ?_
  · /- Addition -/
    intro η κ
    simp only [add_apply]
    conv_lhs =>
      enter [2, a]
      rw [add_smul]
    rw [integral_add]
    · apply hf.schwartzMap_smul_integrable hae
    · exact hf.schwartzMap_smul_integrable hae
  · /- SMul-/
    intro a η
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_lhs =>
      enter [2, a]
      rw [← smul_smul]
    rw [integral_smul]
  /- boundedness -/
  obtain ⟨r, hr⟩ := hf.norm_inv_mul_exists_pow_integrable f hae
  use Finset.Iic (r, 0), 2 ^ r * ∫ x, ‖f x‖ * ‖((1 + ‖x‖) ^ r)⁻¹‖
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards with x
    positivity
  · apply Integrable.mul_const
    apply Integrable.const_mul
    exact hr
  · filter_upwards with x
    simp [norm_smul]
    trans (2 ^ r *
      ((Finset.Iic (r, 0)).sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (dm1 + 1))) ℝ)) η
      *(|1 + ‖x‖| ^ r)⁻¹) * ‖f x‖; swap
    · apply le_of_eq
      ring
    apply mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
    have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (r, 0))
      (k := r) (n := 0) le_rfl le_rfl η x
    rw [Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le _ _ (by positivity)]
    convert h0 using 1
    simp only [Nat.succ_eq_add_one, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    ring_nf
    congr
    rw [abs_of_nonneg (by positivity)]

lemma ofFunction_apply {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    ofFunction f hf hae η = ∫ x, η x • f x := rfl

@[simp]
lemma ofFunction_zero_eq_zero {dm1 : ℕ} :
    ofFunction (fun _ : EuclideanSpace ℝ (Fin (dm1 + 1)) => (0 : F))
      ⟨0, 0, 0, 0, by simp⟩ (by fun_prop) = 0 := by
  ext η
  simp [ofFunction_apply]

lemma ofFunction_smul {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (c : ℝ) :
    ofFunction (c • f) (by fun_prop) (by fun_prop) = c • ofFunction f hf hae := by
  ext η
  change _ = c • ∫ x, η x • f x
  rw [ofFunction_apply]
  simp only [Nat.succ_eq_add_one, Pi.smul_apply]
  rw [← integral_smul]
  congr
  funext x
  rw [smul_comm]

lemma ofFunction_smul_fun {dm1 : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → F)
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (c : ℝ) :
    ofFunction (fun x => c • f x) (by
      change IsDistBounded (c • f)
      fun_prop) (by fun_prop) = c • ofFunction f hf hae := by
  ext η
  change _ = c • ∫ x, η x • f x
  rw [ofFunction_apply]
  simp only [Nat.succ_eq_add_one]
  rw [← integral_smul]
  congr
  funext x
  rw [smul_comm]

open InnerProductSpace

lemma ofFunction_inner {dm1 n : ℕ} (f : EuclideanSpace ℝ (Fin dm1.succ) → EuclideanSpace ℝ (Fin n))
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume)
    (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪ofFunction f hf hae η, y⟫_ℝ = ∫ x, η x * ⟪f x, y⟫_ℝ := by
  rw [ofFunction_apply]
  trans ∫ x, ⟪y, η x • f x⟫_ℝ; swap
  · congr
    funext x
    rw [real_inner_comm]
    simp [inner_smul_left]
  rw [integral_inner, real_inner_comm]
  exact IsDistBounded.schwartzMap_smul_integrable hf hae

TODO "LV5RM" "Add a general lemma specifying the derivative of
  functions from distributions."
end Distribution
