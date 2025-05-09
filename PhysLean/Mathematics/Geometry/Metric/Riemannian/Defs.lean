/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Riemannian Metric Definitions

This module defines the Riemannian metric, building on pseudo-Riemannian metrics.
-/
namespace PseudoRiemannianMetric
section RiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual
open PseudoRiemannianMetric InnerProductSpace

noncomputable section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞}

/-- A Riemannian metric of smoothness class `n` on a manifold `M` over `ℝ`.
    This extends a pseudo-Riemannian metric with the positive definiteness condition. -/
@[ext]
structure RiemannianMetric
  (I : ModelWithCorners ℝ E H) (n : ℕ∞) (M : Type w)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (n + 1) M]
  [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)] : Type _ where
  /-- The underlying pseudo-Riemannian metric. -/
  toPseudoRiemannianMetric : PseudoRiemannianMetric E H M (n) I
  /-- `gₓ(v, v) > 0` for all nonzero `v`. -/
  pos_def' : ∀ x v, v ≠ 0 → toPseudoRiemannianMetric.val x v v > 0

namespace RiemannianMetric

variable {I : ModelWithCorners ℝ E H} {n : ℕ∞} {M : Type w}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-- Coercion from RiemannianMetric to its underlying PseudoRiemannianMetric. -/
instance : Coe (RiemannianMetric I n M) (PseudoRiemannianMetric E H M (n) I) where
  coe g := g.toPseudoRiemannianMetric

@[simp]
lemma pos_def (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x)
    (hv : v ≠ 0) :
  (g.toPseudoRiemannianMetric.val x v) v > 0 := g.pos_def' x v hv

/-- The inverse of the musical isomorphism (index raising), which is an isomorphism
    in the Riemannian case. This is well-defined because the metric is positive definite. -/
def sharp
    (g : RiemannianMetric I n M) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  g.toPseudoRiemannianMetric.sharpEquiv x

/-- Express a Riemannian metric at a point as a quadratic form. -/
abbrev toQuadraticForm (g : RiemannianMetric I n M) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  g.toPseudoRiemannianMetric.toQuadraticForm x

/-- The quadratic form associated with a Riemannian metric is positive definite. -/
@[simp]
lemma toQuadraticForm_posDef (g : RiemannianMetric I n M) (x : M) :
    (g.toQuadraticForm x).PosDef :=
  λ v hv => g.pos_def x v hv

/-- The application of a Riemannian metric's quadratic form to a vector. -/
@[simp]
lemma toQuadraticForm_apply (g : RiemannianMetric I n M) (x : M)
    (v : TangentSpace I x) :
    g.toQuadraticForm x v = g.toPseudoRiemannianMetric.val x v v := by
  simp only [toQuadraticForm, PseudoRiemannianMetric.toQuadraticForm_apply]

lemma riemannian_metric_negDim_zero (g : RiemannianMetric I n M) (x : M) :
    (g.toQuadraticForm x).negDim = 0 := by
  apply QuadraticForm.rankNeg_eq_zero
  exact g.toQuadraticForm_posDef x

/-- The inner product on the tangent space at point `x` induced by the Riemannian metric `g`. -/
def inner (g : RiemannianMetric I n M) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.toPseudoRiemannianMetric.val x v w

@[simp]
lemma inner_apply (g : RiemannianMetric I n M) (x : M) (v w : TangentSpace I x) :
    inner g x v w = g.toPseudoRiemannianMetric.val x v w := rfl

variable (g : RiemannianMetric I n M) (x : M)

/-- Pointwise symmetry of the inner product. -/
lemma inner_symm (v w : TangentSpace I x) :
    g.inner x v w = g.inner x w v := by
  simp only [inner_apply]
  exact g.toPseudoRiemannianMetric.symm x v w

/-- The inner product space core for the tangent space at a point, derived from the
Riemannian metric. -/
noncomputable def tangentInnerCore (g : RiemannianMetric I n M) (x : M) :
    InnerProductSpace.Core ℝ (TangentSpace I x) where
  inner := λ v w => g.inner x v w
  conj_symm := λ v w => by
    simp only [inner_apply, conj_trivial]
    exact g.toPseudoRiemannianMetric.symm x w v
  nonneg_re := λ v => by
    simp only [inner_apply, RCLike.re_to_real]
    by_cases hv : v = 0
    · simp [hv, inner_apply, map_zero]
    · exact le_of_lt (g.pos_def x v hv)
  add_left := λ u v w => by
    simp only [inner_apply, map_add, ContinuousLinearMap.add_apply]
  smul_left := λ r u v => by
    simp only [inner_apply, map_smul, conj_trivial]
    rfl
  definite := fun v (h_inner_zero : g.inner x v v = 0) => by
    by_contra h_v_ne_zero
    have h_pos : g.inner x v v > 0 := g.pos_def x v h_v_ne_zero
    linarith [h_inner_zero, h_pos]

/- We Define NormedAddCommGroup and InnerProductSpace structures locally.
 We DO NOT mark them as instance.-/

/-- Creates a `NormedAddCommGroup` structure on the tangent space at a point,
    derived from a Riemannian metric. -/
noncomputable def TangentSpace.metricNormedAddCommGroup (g : RiemannianMetric I n M) (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ (tangentInnerCore g x)

/-- Creates an `InnerProductSpace` structure on the tangent space at a point,
    derived from a Riemannian metric. Alternative implementation using `letI`. -/
noncomputable def TangentSpace.metricInnerProductSpace' (g : RiemannianMetric I n M) (x : M) :
    letI := TangentSpace.metricNormedAddCommGroup g x
    InnerProductSpace ℝ (TangentSpace I x) :=
  InnerProductSpace.ofCore (tangentInnerCore g x)

/-- Creates an `InnerProductSpace` structure on the tangent space at a point,
    derived from a Riemannian metric. -/
noncomputable def TangentSpace.metricInnerProductSpace (g : RiemannianMetric I n M) (x : M) :
    let _ := TangentSpace.metricNormedAddCommGroup g x
    InnerProductSpace ℝ (TangentSpace I x) :=
  let inner_core := tangentInnerCore g x
  let _ := TangentSpace.metricNormedAddCommGroup g x
  InnerProductSpace.ofCore inner_core

/-- The norm on a tangent space induced by a Riemannian metric, defined as the square root
    of the inner product of a vector with itself. -/
noncomputable def norm (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)

-- Example using the norm function
example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) :
    norm g x v ≥ 0 := Real.sqrt_nonneg _

-- Example showing how to use the metric inner product space
example (g : RiemannianMetric I n M) (x : M) (v w : TangentSpace I x) :
    (TangentSpace.metricInnerProductSpace g x).inner v w = g.inner x v w := by
  letI := TangentSpace.metricInnerProductSpace g x
  rfl

/-- Helper function to compute the norm on a tangent space from a Riemannian metric,
    using the underlying `NormedAddCommGroup` structure. -/
noncomputable def norm' (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  @Norm.norm (TangentSpace I x) (@NormedAddCommGroup.toNorm (TangentSpace I x) normed_group) v

-- Example: Using a custom norm function instead of the notation
example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) :
    norm g x v ≥ 0 := by
  unfold norm
  apply Real.sqrt_nonneg

example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  letI := TangentSpace.metricNormedAddCommGroup g x
  ‖v‖

example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  @Norm.norm (TangentSpace I x) (@NormedAddCommGroup.toNorm (TangentSpace I x) normed_group) v

lemma norm_eq_norm_of_metricNormedAddCommGroup (g : RiemannianMetric I n M) (x : M)
    (v : TangentSpace I x) : norm g x v = @Norm.norm (TangentSpace I x)
    (@NormedAddCommGroup.toNorm _ (TangentSpace.metricNormedAddCommGroup g x)) v := by
  unfold norm
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  unfold TangentSpace.metricNormedAddCommGroup
  simp only [inner_apply]
  rfl

/-- Calculates the length of a curve `γ` between parameters `t₀` and `t₁`
    using the Riemannian metric `g`. This is defined as the integral of the norm of
    the tangent vector along the curve. -/
def curveLength (g : RiemannianMetric I n M) (γ : ℝ → M) (t₀ t₁ : ℝ)
    {IDE : ModelWithCorners ℝ ℝ ℝ}[ChartedSpace ℝ ℝ] : ℝ :=
  ∫ t in t₀..t₁, norm g (γ t) ((mfderiv IDE I γ t) ((1 : ℝ) : TangentSpace IDE t))

end RiemannianMetric
