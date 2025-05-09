/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import PhysLean.Mathematics.Geometry.Manifold.Chart.Smoothness
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import PhysLean.Mathematics.LinearAlgebra.BilinearForm

/-!
# Pseudo-Riemannian Metric in Chart Coordinates

This file defines `chartMetric`, which expresses a pseudo-Riemannian metric in local chart
coordinates, and proves its transformation properties under coordinate changes.
-/

namespace PseudoRiemannianMetric

noncomputable section
open BilinearForm PartialHomeomorph ContinuousLinearMap PartialEquiv ContDiff Manifold.Chart

open Filter

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] --[FiniteDimensional ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] --[T2Space M]
variable {I : ModelWithCorners ℝ E E} --[ModelWithCorners.Boundaryless I]
variable [inst_mani_smooth : IsManifold I (n + 1) M] -- For C^{n+1} manifold for C^n metric
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

noncomputable instance (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  show NormedAddCommGroup E from inferInstance

noncomputable instance (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  show NormedSpace ℝ E from inferInstance

/-- Given a pseudo-Riemannian metric `g` and a partial homeomorphism `e`, computes the metric
in the chart coordinates. At a point `y` in the target of `e`, the result is the pullback of
the metric at `e.symm y` by the derivative of `e.symm` at `y`. -/
def chartMetric (g : PseudoRiemannianMetric E E M n I) (e : PartialHomeomorph M E) (y : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  letI := Classical.propDecidable
  dite (y ∈ e.target)
    (fun _ : y ∈ e.target =>
      let x := e.symm y
      letI : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
      let Df : E →L[ℝ] TangentSpace I x := mfderiv I I e.symm y
      BilinearForm.pullback (g.val x) Df)
    (fun _ => (0 : E →L[ℝ] E →L[ℝ] ℝ))

@[simp]
lemma chartMetric_apply_of_mem (g : PseudoRiemannianMetric E E M n I) (e : PartialHomeomorph M E)
    {y : E} (hy : y ∈ e.target) (v w : E) :
    chartMetric g e y v w = g.val (e.symm y) (mfderiv I I e.symm y v) (mfderiv I I e.symm y w) := by
  letI := Classical.propDecidable
  rw [chartMetric, dite_eq_ite, if_pos hy]
  simp only [BilinearForm.pullback, ContinuousLinearMap.bilinearComp_apply]
  exact rfl

lemma chartMetric_apply_of_not_mem
    (g : PseudoRiemannianMetric E E M n I)
    (e : PartialHomeomorph M E)
    {y : E} (hy : y ∉ e.target) (v w : E) :
    chartMetric g e y v w = 0 := by
  simp only [chartMetric, hy, ↓reduceDIte, ContinuousLinearMap.zero_apply]

/-- The value of a metric in chart coordinates at corresponding points. -/
lemma chartMetric_at_corresponding_points (g : PseudoRiemannianMetric E E M n I)
    (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source)
    (hmani : IsManifold I n M)
    (hn1 : 1 ≤ n)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M)
    (v w : E) :
    let y := e x
    let y' := e' x
    g.val x (mfderiv I I e.symm y v) (mfderiv I I e.symm y w) =
    g.val x (mfderiv I I e'.symm y' (mfderiv I I (e.symm.trans e') y v))
            (mfderiv I I e'.symm y' (mfderiv I I (e.symm.trans e') y w)) := by
  intro y y'
  have h_chain := mfderiv_chart_transition e e' x hx_e hx_e'
                    hn1 hmani he he'
  rw [h_chain]
  congr

/-- The relationship between chart metrics under coordinate change. -/
lemma chartMetric_bilinear_pullback (g : PseudoRiemannianMetric E E M n I)
    (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source)
    (hmani : IsManifold I n M)
    (hn1 : 1 ≤ n)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M)
    (v w : E) :
    let y := e x
    let y' := e' x
    let φ := e.symm.trans e'
    chartMetric g e y v w =
    (BilinearForm.pullback (chartMetric g e' y') (mfderiv I I φ y)) v w := by
  intro y y' φ
  have hy_target : y ∈ e.target := e.mapsTo hx_e
  have hy'_target : y' ∈ e'.target := e'.mapsTo hx_e'
  have h_x_e : e.symm y = x := e.left_inv hx_e
  have h_x_e' : e'.symm y' = x := e'.left_inv hx_e'
  simp only [chartMetric_apply_of_mem g e hy_target,
    chartMetric_apply_of_mem g e' hy'_target,
    BilinearForm.pullback, ContinuousLinearMap.bilinearComp_apply]
  rw [h_x_e]
  rw [h_x_e']
  have h_phi_def : φ = e.symm.trans e' := rfl
  rw [h_phi_def]
  exact chartMetric_at_corresponding_points g e e' x hx_e hx_e' hmani hn1 he he' v w

/--
The metric tensor transformation law under chart changes.

This theorem states that the representation of a pseudo-Riemannian metric in different charts
are related by the pullback of the coordinate transformation between these charts.
Specifically, if `e` and `e'` are two charts containing a point `x_pt`, then the metric
expressed in chart `e` equals the pullback of the metric expressed in chart `e'`
by the differential of the transition map from `e` to `e'`.
-/
theorem chartMetric_coord_change (g : PseudoRiemannianMetric E E M n I)
    (e e' : PartialHomeomorph M E)
    (x_pt : M)
    (hx_e_source : x_pt ∈ e.source) (hx_e'_source : x_pt ∈ e'.source)
    (hn1 : 1 ≤ n)
    (hmani_chart : IsManifold I n M)
    (he_atlas : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he'_atlas : e' ∈ (contDiffGroupoid n I).maximalAtlas M) :
    chartMetric g e (e x_pt) =
      BilinearForm.pullback (chartMetric g e' (e' x_pt))
        (mfderiv I I (e.symm.trans e') (e x_pt)) := by
  let φ := e.symm.trans e'
  let y := e x_pt
  let y' := e' x_pt
  ext v w
  exact chartMetric_bilinear_pullback g e e' x_pt hx_e_source hx_e'_source
                                     hmani_chart hn1 he_atlas he'_atlas v w
