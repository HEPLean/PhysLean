/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PhysLean.Mathematics.VariationalCalculus.IsTestFunction
import PhysLean.Meta.Informal.SemiFormal
/-!

# Fundamental lemma of the calculus of variations

The key took in variational calculus is:
```
∀ h, ∫ x, f x * h x = 0 → f = 0
```
which allows use to go from reasoning about integrals to reasoning about functions. There are

-/

open MeasureTheory InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma fundamental_theorem_of_variational_calculus {f : X → V}
    (μ : Measure X)  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (hf : IsTestFunction f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
  have hf' := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hf'
  · rw [Continuous.ae_eq_iff_eq] at hf'
    · funext x
      have hf'' := congrFun hf' x
      simpa using hf''
    · have hf : Continuous f := hf.smooth.continuous
      fun_prop
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    exact real_inner_self_nonneg
  · apply IsTestFunction.integrable
    exact IsTestFunction.inner hf hf


/-- The assumption `IsTestFunction f` `in fundamental_theorem_of_variational_calculus` can be
weakened to `Continuous f`.

The proof is by contradiction, assume that there is `x₀` such that `f x₀` then you can easily
 construct `g` test function with support on the neighborhood of `x₀` such that `⟪f x, g x⟫ ≥ 0`. -/
semiformal_result "FIE3I" fundamental_theorem_of_variational_calculus' {f : X → V}
    (μ : Measure X)  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0
