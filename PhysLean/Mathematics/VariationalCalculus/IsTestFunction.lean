/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.CompactlySupported

import PhysLean.Mathematics.InnerProductSpace.Basic
import PhysLean.SpaceAndTime.Space.Basic
/-!

# Test functions

Definition of test function, smooth and compactly supported function, and theorems about them.
-/

section IsTestFunction
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] -- [InnerProductSpace' ℝ V]

open ContDiff InnerProductSpace MeasureTheory
/-- A test function is a smooth function with compact support. -/
@[fun_prop]
structure IsTestFunction (f : X → U) where
  smooth : ContDiff ℝ ∞ f
  supp : HasCompactSupport f

/-- A compactly supported continuous map from a test function. -/
def IsTestFunction.toCompactlySupportedContinuousMap {f : X → U}
    (hf : IsTestFunction f) : CompactlySupportedContinuousMap X U where
  toFun := f
  hasCompactSupport' := hf.supp
  continuous_toFun := hf.smooth.continuous

lemma IsTestFunction.of_compactlySupportedContinuousMap {f : CompactlySupportedContinuousMap X U}
    (hf : ContDiff ℝ ∞ f) :
    IsTestFunction f.toFun where
  smooth := hf
  supp := f.hasCompactSupport'

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
lemma IsTestFunction.of_fderiv {f : X → U} (hf : IsTestFunction f) :
    IsTestFunction (fderiv ℝ f ·) where
  smooth := by
    apply ContDiff.fderiv (m := ∞)
    · fun_prop
    · fun_prop
    · exact Preorder.le_refl (∞ + 1)
  supp := by
    apply HasCompactSupport.fderiv
    exact hf.supp

@[fun_prop]
lemma IsTestFunction.fderiv_apply {f : X → U} (hf : IsTestFunction f) (δx : X) :
    IsTestFunction (fderiv ℝ f · δx) where
  smooth := by
    apply ContDiff.fderiv_apply (m := ∞)
    · fun_prop
    · fun_prop
    · fun_prop
    · exact Preorder.le_refl (∞ + 1)
  supp := by
    apply HasCompactSupport.fderiv_apply
    exact hf.supp

@[fun_prop]
lemma IsTestFunction.zero :
    IsTestFunction (fun _ : X => (0 : U)) where
  smooth := by fun_prop
  supp := HasCompactSupport.zero

@[fun_prop]
lemma IsTestFunction.add {f g : X → U} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x + g x) where
  smooth := ContDiff.add hf.smooth hg.smooth
  supp := by
    apply HasCompactSupport.add
    · exact hf.supp
    · exact hg.supp

@[fun_prop]
lemma IsTestFunction.neg {f : X → U} (hf : IsTestFunction f) :
    IsTestFunction (fun x => - f x) where
  smooth := ContDiff.neg hf.smooth
  supp := by
    apply HasCompactSupport.neg' hf.supp

@[fun_prop]
lemma IsTestFunction.sub {f g : X → U} (hf : IsTestFunction f) (hg : IsTestFunction g) :
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
lemma IsTestFunction.inner [InnerProductSpace' ℝ V]
    {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) where
  smooth := by fun_prop
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

@[fun_prop]
lemma IsTestFunction.linearMap_comp {f : X → V} (hf : IsTestFunction f)
    {g : V →ₗ[ℝ] U} (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g (f x)) where
  smooth := ContDiff.comp hg hf.smooth
  supp := by
    have hf' := hf.supp
    rw [← exists_compact_iff_hasCompactSupport] at hf' ⊢
    obtain ⟨K, cK, hK⟩ := hf'
    refine ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp

@[fun_prop]
lemma IsTestFunction.family_linearMap_comp {f : X → V} (hf : IsTestFunction f)
    {g : X → V →L[ℝ] U} (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g x (f x)) where
  smooth := by
    fun_prop
  supp := by
    have hf' := hf.supp
    rw [← exists_compact_iff_hasCompactSupport] at hf' ⊢
    obtain ⟨K, cK, hK⟩ := hf'
    refine ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp

lemma IsTestFunction.gradient {d : ℕ} (φ : Space d → ℝ)
    (hφ : IsTestFunction φ) :
    IsTestFunction (gradient φ) where
  smooth := by
    rw [@contDiff_euclidean]
    simp [_root_.gradient]
    rw [← contDiff_euclidean]
    apply ContDiff.fun_comp
    · apply LinearIsometryEquiv.contDiff
    · have hφ := hφ.smooth
      fun_prop
  supp := by
    have hg : _root_.gradient φ = fun x => (toDual ℝ (Space d)).symm (fderiv ℝ φ x) := by
      exact rfl
    rw [hg]
    have hf : HasCompactSupport (fun x => fderiv ℝ φ x) := by
      exact supp (of_fderiv hφ)
    rw [← exists_compact_iff_hasCompactSupport] at hf ⊢
    obtain ⟨K, cK, hK⟩ := hf
    refine ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp

@[fun_prop]
lemma IsTestFunction.of_div {d : ℕ} (φ : Space d → Space d)
    (hφ : IsTestFunction φ) :
    IsTestFunction (Space.div φ) := by
  let f (i : Fin d) : CompactlySupportedContinuousMap (Space d) ℝ := {
      toFun := fun x => Space.deriv i (fun x => Space.coord i (φ x)) x
      hasCompactSupport' := by
        apply supp
        simp [Space.deriv]
        refine fderiv_apply ?_ (EuclideanSpace.single i 1)
        constructor
        · unfold Space.coord
          apply ContDiff.inner
          · fun_prop
          · fun_prop
        have h1 := hφ.supp
        rw [← exists_compact_iff_hasCompactSupport] at h1 ⊢
        obtain ⟨K, cK, hK⟩ := h1
        refine ⟨K, cK, fun x hx => ?_⟩
        rw [hK x hx]
        simp [Space.coord]
      continuous_toFun := by
        simp [Space.deriv]
        apply ContDiff.continuous (𝕜 := ℝ) (n := ∞)
        apply ContDiff.fderiv_apply (m := ∞)
        · apply ContDiff.comp
          · unfold Space.coord
            apply ContDiff.inner
            · fun_prop
            · fun_prop
          · fun_prop
        · fun_prop
        · fun_prop
        · exact Preorder.le_refl (∞ + 1)
        }
  let g := ∑ i, f i
  have h1 :  (Space.div φ) = g := by
    funext x
    simp [g, CompactlySupportedContinuousMap.sum_apply, f]
    unfold Space.div
    simp
  rw [h1]
  apply IsTestFunction.of_compactlySupportedContinuousMap
  rw [← h1]
  unfold Space.div
  simp
  apply ContDiff.sum
  intro i _
  simp [Space.deriv]
  apply ContDiff.fderiv_apply (m := ∞)
  · apply ContDiff.comp
    · unfold Space.coord
      apply ContDiff.inner
      · fun_prop
      · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop
  · exact Preorder.le_refl (∞ + 1)

@[fun_prop]
lemma IsTestFunction.prod_fst {f : X → U × V} (hf : IsTestFunction f) :
    IsTestFunction (fun x => (f x).1) where
  smooth := by
    fun_prop
  supp := by
    have hf' := hf.supp
    rw [hasCompactSupport_iff_eventuallyEq] at hf' ⊢
    exact hf'.mono fun x hx => by simp [hx]

@[fun_prop]
lemma IsTestFunction.prod_snd {f : X → U × V} (hf : IsTestFunction f) :
    IsTestFunction (fun x => (f x).2) where
  smooth := by
    fun_prop
  supp := by
    have hf' := hf.supp
    rw [hasCompactSupport_iff_eventuallyEq] at hf' ⊢
    exact hf'.mono fun x hx => by simp [hx]
