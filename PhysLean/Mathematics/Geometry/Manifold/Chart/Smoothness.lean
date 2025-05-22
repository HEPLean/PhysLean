/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import PhysLean.Mathematics.Geometry.Manifold.PartialHomeomorph

/-!
# Smoothness of Charts and Transition Maps

This file contains lemmas about the smoothness and differentiability of charts and transition maps.
-/

namespace Manifold.Chart

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E]
variable [TopologicalSpace M]

open PartialHomeomorph ContinuousLinearMap PartialEquiv

/-- Coordinate transformation identity: e' x = φ(e x) where φ is the transition map. -/
lemma chart_coordinate_transform (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) :
    let φ := e.symm.trans e';
    let y := e x;
    e' x = φ y := (apply_transition_map_eq_chart_apply e e' x hx_e).symm

/-- Chart inverse composition identity: e.symm = e'.symm ∘ φ in a neighborhood of e x,
    where φ is the transition map. -/
lemma chart_inverse_composition (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source) :
    let φ := e.symm.trans e';
    let y := e x;
    e.symm =ᶠ[nhds y] e'.symm ∘ φ := by
  intro φ y
  have hy_dom_φ : y ∈ φ.source :=
    transition_map_source_contains_image_point e e' x hx_e hx_e'
  filter_upwards [φ.open_source.mem_nhds hy_dom_φ] with z hz
  exact apply_symm_eq_apply_symm_comp_transition e e' z hz

variable [NormedSpace ℝ E]
variable [ChartedSpace E M]
variable {I : ModelWithCorners ℝ E E}

open PartialHomeomorph ContinuousLinearMap PartialEquiv

/-- Transition maps between charts in the maximal atlas are smooth. -/
lemma chart_transition_smooth (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source)
    (n : WithTop ℕ∞)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M) :
    let φ := e.symm.trans e';
    let y := e x;
    ContMDiffAt I I n φ y := by
  intro φ y
  have hy_dom_φ : y ∈ φ.source :=
    transition_map_source_contains_image_point e e' x hx_e hx_e'
  have h_φ_groupoid : φ ∈ contDiffGroupoid n I :=
    (contDiffGroupoid n I).compatible_of_mem_maximalAtlas he he'
  have h_φ_smooth : ContMDiffOn I I n φ φ.source :=
    contMDiffOn_of_mem_contDiffGroupoid h_φ_groupoid
  exact ContMDiffOn.contMDiffAt h_φ_smooth (φ.open_source.mem_nhds hy_dom_φ)

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] --[FiniteDimensional ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] --[T2Space M]
variable {I : ModelWithCorners ℝ E E} --[ModelWithCorners.Boundaryless I]

/-- Charts in the maximal atlas are differentiable on their source. -/
lemma chart_differentiable_on_source
    (e : PartialHomeomorph M E) (hmani : IsManifold I n M)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (hn1 : 1 ≤ n) :
    MDifferentiableOn I I e e.source := by
  intro x hx
  have h_smooth : ContMDiffAt I I n e x :=
    (contMDiffOn_of_mem_maximalAtlas he).contMDiffAt (e.open_source.mem_nhds hx)
  exact (h_smooth.mdifferentiableWithinAt hn1).mono (by exact fun ⦃a⦄ a => trivial)

lemma chart_symm_differentiable_on_target
    (e : PartialHomeomorph M E) (hmani : IsManifold I n M)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (hn1 : 1 ≤ n) :
    MDifferentiableOn I I e.symm e.target := by
  intro y hy
  have h_smooth : ContMDiffAt I I n e.symm y :=
    (contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt (e.open_target.mem_nhds hy)
  let h_md := h_smooth.mdifferentiableWithinAt hn1
  exact h_md.mono (Set.subset_univ _)

/-- The manifold derivative of a chart transition map can be computed from charts. -/
lemma mfderiv_chart_transition_helper (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source)
    (hn1 : 1 ≤ n) (hmani : IsManifold I n M)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M) :
    let φ := e.symm.trans e';
    let y := e x;
    mfderiv I I (e'.symm ∘ φ) y = (mfderiv I I e'.symm (φ y)).comp (mfderiv I I φ y) := by
  intro φ y
  have h_φ_y_eq : φ y = e' x := (chart_coordinate_transform e e' x hx_e).symm
  have hφ_diff : ContMDiffAt I I n φ y :=
    chart_transition_smooth e e' x hx_e hx_e' n he he'
  have hφ_mdiff : MDifferentiableAt I I φ y := hφ_diff.mdifferentiableAt hn1
  have he'_symm_diff : MDifferentiableAt I I e'.symm (e' x) :=
    ((chart_symm_differentiable_on_target e' hmani he' hn1) (e' x)
      (e'.mapsTo hx_e')).mdifferentiableAt
      (e'.open_target.mem_nhds (e'.mapsTo hx_e'))
  exact mfderiv_comp_of_eq he'_symm_diff hφ_mdiff h_φ_y_eq

/-- Chain rule for composition of chart inverses with transition maps. -/
theorem mfderiv_chart_transition (e e' : PartialHomeomorph M E) (x : M)
    (hx_e : x ∈ e.source) (hx_e' : x ∈ e'.source)
    (hn1 : 1 ≤ n) (hmani : IsManifold I n M)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M) :
    let φ := e.symm.trans e';
    let y := e x;
    mfderiv I I e.symm y = (mfderiv I I e'.symm (e' x)).comp (mfderiv I I φ y) := by
  intro φ y
  have h_fun_eq : e.symm =ᶠ[nhds y] e'.symm ∘ φ :=
    chart_inverse_composition e e' x hx_e hx_e'
  have h_φ_y_eq : φ y = e' x :=
    (chart_coordinate_transform e e' x hx_e).symm
  have h_deriv_eq : mfderiv I I e.symm y = mfderiv I I (e'.symm ∘ φ) y :=
    Filter.EventuallyEq.mfderiv_eq h_fun_eq
  rw [h_deriv_eq]
  have h_comp := mfderiv_chart_transition_helper e e' x hx_e hx_e' hn1 hmani he he'
  rw [h_comp, h_φ_y_eq]

end Manifold.Chart
