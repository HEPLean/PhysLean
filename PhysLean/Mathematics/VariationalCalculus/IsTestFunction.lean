/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
/-!

# Test functions

Definition of test function, smooth and compactly supported function, and theorems about them.
-/

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
lemma IsTestFunction.integrable [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → U} (hf : IsTestFunction f)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    MeasureTheory.Integrable f μ :=
  Continuous.integrable_of_hasCompactSupport (continuous hf.smooth) hf.supp

@[fun_prop]
lemma IsTestFunction.differentiable {f : X → U} (hf : IsTestFunction f) :
    Differentiable ℝ f := hf.1.differentiable ENat.LEInfty.out

@[fun_prop]
lemma IsTestFunction.contDiff {f : X → U} (hf : IsTestFunction f) :
    ContDiff ℝ ∞ f := hf.1

@[fun_prop]
lemma IsTestFunction.deriv {f : ℝ → U} (hf : IsTestFunction f) :
    IsTestFunction (fun x => deriv f x) where
  smooth := deriv' hf.smooth
  supp := HasCompactSupport.deriv hf.supp

@[fun_prop]
lemma IsTestFunction.add {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x + g x) where
  smooth := ContDiff.add hf.smooth hg.smooth
  supp := by
    apply HasCompactSupport.add
    · exact hf.supp
    · exact hg.supp

@[fun_prop]
lemma IsTestFunction.neg {f : X → V} (hf : IsTestFunction f) :
    IsTestFunction (fun x => - f x) where
  smooth := ContDiff.neg hf.smooth
  supp := by
    apply HasCompactSupport.neg' hf.supp

@[fun_prop]
lemma IsTestFunction.sub {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (f - g) where
  smooth := ContDiff.sub hf.smooth hg.smooth
  supp := by
    rw [SubNegMonoid.sub_eq_add_neg]
    apply HasCompactSupport.add
    · exact hf.supp
    · exact HasCompactSupport.neg' hg.supp

@[fun_prop]
lemma IsTestFunction.mul {f g : X → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf.smooth hg.smooth
  supp := HasCompactSupport.mul_left hg.supp

@[fun_prop]
lemma IsTestFunction.inner {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) where
  smooth := ContDiff.inner ℝ hf.smooth hg.smooth
  supp := by
    have hf := hg.supp
    rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
    exact hf.mono fun x hx => by simp [hx]

@[fun_prop]
lemma IsTestFunction.mul_left {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf hg.smooth
  supp := HasCompactSupport.mul_left hg.supp

@[fun_prop]
lemma IsTestFunction.mul_right {f g : X → ℝ} (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf.smooth hg
  supp := HasCompactSupport.mul_right hf.supp

@[fun_prop]
lemma IsTestFunction.smul_left {f : X → ℝ} {g : X → U}
    (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf hg.smooth
  supp := HasCompactSupport.smul_left hg.supp

@[fun_prop]
lemma IsTestFunction.smul_right {f : X → ℝ} {g : X → U}
    (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf.smooth hg
  supp := HasCompactSupport.smul_right hf.supp
