/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import PhysLean.Mathematics.LinearAlgebra.BilinearForm
import PhysLean.Mathematics.Geometry.Manifold.Chart.Smoothness
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Pseudo-Riemannian Metric in Chart Coordinates

This file defines `chartMetric`, which expresses a pseudo-Riemannian metric `g`
on a manifold `M` in local chart coordinates `e`. It establishes the
tensor transformation law for `chartMetric` under a change of chart,
`chartMetric_coord_change`. Auxiliary lemmas concern the smoothness of
bilinear forms when viewed as maps into function spaces, and properties
of chart transitions necessary for proving the main transformation result.
-/

namespace PseudoRiemannianMetric

noncomputable section
open BilinearForm PartialHomeomorph ContinuousLinearMap PartialEquiv ContDiff Manifold.Chart

open Filter

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M]
variable {I : ModelWithCorners ℝ E E}
variable [inst_mani_smooth : IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

noncomputable instance (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  show NormedAddCommGroup E from inferInstance

noncomputable instance (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  show NormedSpace ℝ E from inferInstance

/-- Given a pseudo-Riemannian metric `g` on a manifold `M` and a chart `e : PartialHomeomorph M E`,
`chartMetric g e y` computes the metric tensor in the local coordinates provided by `e`.
Let `x := e.symm y` be the point on `M` corresponding to chart coordinates `y : E`.
Let `Df_y := mfderiv I I e.symm y : E →L[ℝ] TangentSpace I x` be the differential of `e.symm` at
`y`. Then `chartMetric g e y` is the bilinear form on `E` defined as the pullback of `g.val x` by
`Df_y`. That is, for `v, w : E`, `(chartMetric g e y) v w = g.val x (Df_y v) (Df_y w)`.
If `(b_i)` is a basis for `E`, then the values `(chartMetric g e y) (b_i) (b_j)` are the
components `g_{ij}(y)` of the metric `g` at `x` with respect to the basis for `T_xM`
induced by `(b_i)` via `Df_y`.
If `y ∉ e.target`, the result is defined as the zero bilinear form. -/
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

/-- Evaluation of `chartMetric` at `y ∈ e.target`.
For `v, w : E`, `chartMetric g e y v w = g_x(D(e⁻¹)_y v, D(e⁻¹)_y w)`, where `x = e⁻¹y`. -/
@[simp]
lemma chartMetric_apply_of_mem (g : PseudoRiemannianMetric E E M n I) (e : PartialHomeomorph M E)
    {y : E} (hy : y ∈ e.target) (v w : E) :
    chartMetric g e y v w = g.val (e.symm y) (mfderiv I I e.symm y v) (mfderiv I I e.symm y w) := by
  letI := Classical.propDecidable
  rw [chartMetric, dite_eq_ite, if_pos hy]
  simp only [BilinearForm.pullback, ContinuousLinearMap.bilinearComp_apply]
  exact rfl

/-- If `y ∉ e.target`, `chartMetric g e y` is the zero bilinear form. -/
lemma chartMetric_apply_of_not_mem
    (g : PseudoRiemannianMetric E E M n I)
    (e : PartialHomeomorph M E)
    {y : E} (hy : y ∉ e.target) (v w : E) :
    chartMetric g e y v w = 0 := by
  simp only [chartMetric, hy, ↓reduceDIte, ContinuousLinearMap.zero_apply]

/-- The metric `g_x(D(e⁻¹)_y v, D(e⁻¹)_y w)` can be expressed using a second chart `e'`
via the chain rule for `D(e⁻¹) = D(e'⁻¹) ∘ D(φ)`.
`x` is a point on the manifold, `y = ex`, `y' = e'x`.
`φ = e' ∘ e⁻¹` is the transition map. `1 ≤ n`. -/
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

/-- Transformation law for the metric components under chart change.
    `g_e(y)(v,w) = g_{e'}(y')(D(φ)_y v, D(φ)_y w)`, where `y = ex`, `y' = e'x`, `φ = e' ∘ e⁻¹`.
    Assumes `e, e'` are in a `C^n` maximal atlas (`1 ≤ n`). -/
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

/-- Transformation law for `chartMetric`: `(g_e)_y = ((e'∘e⁻¹)^* (g_{e'})_{e'y})_y`.
Given a metric `g`, and two charts `e, e'`, the representation of `g` in chart `e` at `y = ex`
is the pullback by the transition map `φ = e' ∘ e⁻¹` (evaluated at `y`)
of the representation of `g` in chart `e'` (evaluated at `y' = e'x = φy`).
Assumes charts are `C^n` compatible, `1 ≤ n`. -/
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
