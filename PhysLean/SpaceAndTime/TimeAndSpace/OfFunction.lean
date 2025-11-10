/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.TimeAndSpace.IsDistBounded
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

/-!

## A. Space Functions to distributions on Time and Space

-/


namespace Space
open Distribution MeasureTheory
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

def distOfSpaceFunction {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) : (Time × Space d) →d[ℝ] F := by
  refine mkCLMtoNormedSpace (fun η => ∫ x, η x • f x.2) ?_ ?_ ?_
  · /- Addition -/
    intro η κ
    simp only [add_apply]
    conv_lhs =>
      enter [2, a]
      rw [add_smul]
    rw [integral_add]
    · exact hf.integrable_time_space η
    · exact hf.integrable_time_space κ
  · /- SMul-/
    intro a η
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_lhs =>
      enter [2, a]
      rw [← smul_smul]
    rw [integral_smul]
  /- boundedness -/

  obtain ⟨r, hr⟩ := hf.norm_inv_mul_exists_pow_integrable f
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

end Space
