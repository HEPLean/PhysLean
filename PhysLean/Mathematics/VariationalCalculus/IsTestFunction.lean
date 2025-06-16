/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/

import Mathlib

/-! Test function

Definition of test function, smooth and compactly supported function, and theorems about them.
-/
section IsTestFunction
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open ContDiff InnerProductSpace MeasureTheory
/-- A test function is a smooth function with compact support. -/
@[fun_prop]
structure IsTestFunction (f : X → U) where
  smooth : ContDiff ℝ ∞ f
  supp : HasCompactSupport f

@[fun_prop]
theorem IsTestFunction.integrable [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → U} (hf : IsTestFunction f)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    MeasureTheory.Integrable f μ :=
  Continuous.integrable_of_hasCompactSupport (continuous hf.smooth) hf.supp

@[fun_prop]
theorem IsTestFunction.differentiable {f : X → U} (hf : IsTestFunction f) :
    Differentiable ℝ f := hf.1.differentiable ENat.LEInfty.out

@[fun_prop]
theorem IsTestFunction.contDiff {f : X → U} (hf : IsTestFunction f) :
    ContDiff ℝ ∞ f := hf.1

@[fun_prop]
theorem IsTestFunction.deriv {f : ℝ → U} (hf : IsTestFunction f) :
    IsTestFunction (fun x => deriv f x) where
  smooth := deriv' hf.smooth
  supp := HasCompactSupport.deriv hf.supp


@[fun_prop]
theorem IsTestFunction.mul {f g : X → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf.smooth hg.smooth
  supp := HasCompactSupport.mul_left hg.supp

@[fun_prop]
theorem IsTestFunction.inner {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) where
  smooth := ContDiff.inner ℝ hf.smooth hg.smooth
  supp := by
    have hf := hg.supp
    rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
    exact hf.mono fun x hx => by simp [hx]

@[fun_prop]
theorem IsTestFunction.mul_left {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf hg.smooth
  supp := HasCompactSupport.mul_left hg.supp

@[fun_prop]
theorem IsTestFunction.mul_right {f g : X → ℝ} (hf : IsTestFunction f) (hg : ContDiff ℝ ∞  g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf.smooth hg
  supp := HasCompactSupport.mul_right hf.supp


@[fun_prop]
theorem IsTestFunction.smul_left {f : X → ℝ} {g : X → U}
    (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf hg.smooth
  supp := HasCompactSupport.smul_left hg.supp

@[fun_prop]
theorem IsTestFunction.smul_right {f : X → ℝ} {g : X → U}
    (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf.smooth hg
  supp := HasCompactSupport.smul_right hf.supp
