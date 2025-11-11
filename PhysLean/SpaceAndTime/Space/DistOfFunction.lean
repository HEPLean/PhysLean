/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.IsDistBounded
/-!

# Distributions from functions on space

## i. Overview

In this module we define distributions on space constructed from functions
`f : Space d → F` satisfying the condition `IsDistBounded f`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## ii. Key results

- `distOfFunction f hf` : The distribution on space constructed from the function
  `f : Space d → F` satisfying the `IsDistBounded f` condition.

## iii. Table of contents

- A. Definition of a distribution from a function
- B. Linarity properties of getting distributions from functions
- C. Properties related to inner products

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. Definition of a distribution from a function

-/

/-- A distribution `Space d →d[ℝ] F` from a function
  `f : Space d → F` which satisfies the `IsDistBounded f` condition. -/
def distOfFunction {d : ℕ} (f : Space d → F) (hf : IsDistBounded f) :
    (Space d) →d[ℝ] F := by
  refine mkCLMtoNormedSpace (fun η => ∫ x, η x • f x) ?_ ?_ hf.integral_mul_schwartzMap_bounded
  · /- Addition -/
    intro η κ
    simp only [add_apply]
    conv_lhs =>
      enter [2, a]
      rw [add_smul]
    rw [integral_add (by fun_prop) (by fun_prop)]
  · /- SMul-/
    intro a η
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_lhs =>
      enter [2, a]
      rw [← smul_smul]
    rw [integral_smul]

lemma distOfFunction_apply {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) :
    distOfFunction f hf η = ∫ x, η x • f x := rfl

/-!

## B. Linarity properties of getting distributions from functions

-/
@[simp]
lemma distOfFunction_zero_eq_zero {d : ℕ} :
    distOfFunction (fun _ : Space d => (0 : F)) (by fun_prop) = 0 := by
  ext η
  simp [distOfFunction_apply]

lemma distOfFunction_smul {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (c : ℝ) :
    distOfFunction (c • f) (by fun_prop) = c • distOfFunction f hf := by
  ext η
  change _ = c • ∫ x, η x • f x
  rw [distOfFunction_apply]
  simp only [Pi.smul_apply]
  rw [← integral_smul]
  congr
  funext x
  rw [smul_comm]

lemma distOfFunction_smul_fun {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (c : ℝ) :
    distOfFunction (fun x => c • f x) (by fun_prop) = c • distOfFunction f hf := by
  ext η
  change _ = c • ∫ x, η x • f x
  rw [distOfFunction_apply]
  rw [← integral_smul]
  congr
  funext x
  rw [smul_comm]

/-!

## C. Properties related to inner products

-/

open InnerProductSpace

lemma distOfFunction_inner {d n : ℕ} (f : Space d → EuclideanSpace ℝ (Fin n))
    (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪distOfFunction f hf η, y⟫_ℝ = ∫ x, η x * ⟪f x, y⟫_ℝ := by
  rw [distOfFunction_apply]
  trans ∫ x, ⟪y, η x • f x⟫_ℝ; swap
  · congr
    funext x
    rw [real_inner_comm]
    simp [inner_smul_left]
  rw [integral_inner, real_inner_comm]
  fun_prop

TODO "LV5RM" "Add a general lemma specifying the derivative of
  functions from distributions."
end Space
