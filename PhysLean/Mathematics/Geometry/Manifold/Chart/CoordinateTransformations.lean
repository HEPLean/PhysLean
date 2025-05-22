/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.Mathematics.Geometry.Manifold.Chart.Smoothness
import PhysLean.Mathematics.Geometry.Manifold.Chart.Utilities
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Coordinate Transformations and Transition Maps

This file contains lemmas about coordinate transformations and transition maps between charts.
-/

namespace Manifold.Chart
open ContDiff ContinuousLinearMap
open PartialHomeomorph
open Filter Manifold

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E]
variable [TopologicalSpace M]

/-- The domain where the chart transition map `φ = e' ∘ e.symm` is well-defined forms
a neighborhood of `y`. -/
lemma chartMetric_transition_domain_in_nhds (e e' : PartialHomeomorph M E) (y : E)
    (hy_target : y ∈ e.target) (hz_source' : e.symm y ∈ e'.source) :
    let _ := e' ∘ e.symm
    y ∈ e.target ∩ e.symm ⁻¹' e'.source := by
  intro φ
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨hy_target, hz_source'⟩

/-- When applying the transition map `φ = e' ∘ e.symm` to a point `z` in the domain,
the result is in `e'.target`. -/
lemma chartMetric_transition_map_target (e e' : PartialHomeomorph M E) {z : E}
    (hz_source' : e.symm z ∈ e'.source) :
    let φ := e' ∘ e.symm
    φ z ∈ e'.target := by
  intro φ
  exact e'.mapsTo hz_source'

variable [NormedSpace ℝ E]
variable [ChartedSpace E M]
variable {I : ModelWithCorners ℝ E E}
variable [inst_mani_smooth : IsManifold I (n + 1) M] -- For C^{n+1} manifold for C^n metric
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {f_bilin : X → E →L[ℝ] E →L[ℝ] ℝ} {s_set : Set X} {x₀_pt : X}

/-- Core derivative chain rule for manifold derivatives that combines correctly with the metric. -/
theorem manifold_derivative_chain_rule (g : PseudoRiemannianMetric E E M n I)
    (e e' : PartialHomeomorph M E) {z : E}
    (hz_target : z ∈ e.target) (hz_source' : e.symm z ∈ e'.source)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M)
    (hn1 : 1 ≤ n) :
    let φ := e' ∘ e.symm
    let ψ := e.symm.trans e'
    let x_z := e.symm z
    ∀ v w : E,
      g.val x_z (mfderiv I I e.symm z v) (mfderiv I I e.symm z w) =
        g.val x_z (mfderiv I I e'.symm (φ z) ((mfderiv I I ψ z) v))
                 (mfderiv I I e'.symm (φ z) ((mfderiv I I ψ z) w)) := by
  intro φ ψ x_z v w
  have hmani : IsManifold I n M := by
    letI := inst_mani_smooth
    have h_le : n ≤ n + 1 := by simp [self_le_add_right]
    exact IsManifold.of_le h_le
  have h_chain_rule_v : mfderiv I I e'.symm (φ z) ((mfderiv I I ψ z) v) =
                        mfderiv I I e.symm z v := by
    let x := e.symm z
    have h_z_eq : z = e x := Eq.symm (PartialHomeomorph.right_inv e hz_target)
    have hx_e : x ∈ e.source := e.map_target hz_target
    have h_fun_eq : e.symm =ᶠ[nhds z] e'.symm ∘ φ := by
      have h_z_eq_ex : z = e x := by
        exact h_z_eq
      have h_lemma : e.symm =ᶠ[nhds (e x)] e'.symm ∘ ↑(e.symm.trans e') :=
        chart_inverse_composition e e' x hx_e hz_source'
      have h_φ_eq : φ = ↑(e.symm.trans e') := by
        ext y
        simp [φ, trans_apply, Function.comp_apply]
      rw [← h_z_eq_ex, ← h_φ_eq] at h_lemma
      exact h_lemma
    have h_deriv_eq : mfderiv I I e.symm z = mfderiv I I (e'.symm ∘ φ) z :=
      Filter.EventuallyEq.mfderiv_eq h_fun_eq
    have h_chain : mfderiv I I (e'.symm ∘ φ) z v =
                   mfderiv I I e'.symm (φ z) (mfderiv I I φ z v) := by
      have h_comp : mfderiv I I (e'.symm ∘ φ) z =
                    (mfderiv I I e'.symm (φ z)).comp (mfderiv I I φ z) := by
        have hφz_target : φ z ∈ e'.target :=
          chartMetric_phi_maps_to_target e e' hz_source'
        have hφ_diff : MDifferentiableAt I I φ z := by
          have h_φ_eq_ψ : φ = ψ := rfl
          rw [h_φ_eq_ψ]
          let x := e.symm z
          have hx_e := e.map_target hz_target
          have h_smooth := chart_transition_smooth e e' x hx_e hz_source' n he he'
          simpa [h_z_eq] using h_smooth.mdifferentiableAt hn1
        have he'_symm_diff : MDifferentiableAt I I e'.symm (φ z) := by
          have hmani : IsManifold I n M := by
            letI := inst_mani_smooth
            have h : n ≤ n + 1 := by
              simp only [self_le_add_right, φ]
            exact IsManifold.of_le h
          have hn1 : 1 ≤ n := by exact hn1
          have h_symm_smooth : ContMDiffOn I I n e'.symm e'.target :=
            contMDiffOn_symm_of_mem_maximalAtlas he'
          exact
            (h_symm_smooth.contMDiffAt (e'.open_target.mem_nhds hφz_target)).mdifferentiableAt hn1
        exact mfderiv_comp_of_eq he'_symm_diff hφ_diff rfl
      have h_apply : mfderiv I I (e'.symm ∘ φ) z v =
                     (mfderiv I I e'.symm (φ z)).comp (mfderiv I I φ z) v := by
        rw [h_comp]
        exact rfl
      rw [h_apply]
      rfl
    have h_φ_eq_ψ : φ = ψ := rfl
    rw [← h_deriv_eq, h_φ_eq_ψ] at h_chain
    exact h_chain.symm
  have h_chain_rule_w : mfderiv I I e'.symm (φ z) ((mfderiv I I ψ z) w) =
                      mfderiv I I e.symm z w := by
    let x := e.symm z
    have h_z_eq : z = e x := Eq.symm (PartialHomeomorph.right_inv e hz_target)
    have hx_e : x ∈ e.source := e.map_target hz_target
    have h_fun_eq : e.symm =ᶠ[nhds z] e'.symm ∘ φ := by
      have h_z_eq_ex : z = e x := h_z_eq
      have h_lemma := chart_inverse_composition e e' x hx_e hz_source'
      have h_φ_eq : φ = (e.symm.trans e') := rfl
      simpa [h_z_eq_ex, h_φ_eq] using h_lemma
    have h_deriv_eq : mfderiv I I e.symm z = mfderiv I I (e'.symm ∘ φ) z :=
      Filter.EventuallyEq.mfderiv_eq h_fun_eq
    let h_comp := mfderiv_chart_transition_helper e e' x hx_e hz_source' hn1 hmani he he'
    have h_comp_w : mfderiv I I (e'.symm ∘ φ) z w =
                   (mfderiv I I e'.symm (φ z)).comp (mfderiv I I φ z) w := by
      have h_comp_map : mfderiv I I (e'.symm ∘ φ) z =
                        (mfderiv I I e'.symm (φ z)).comp (mfderiv I I φ z) := by
        have hφz_target : φ z ∈ e'.target :=
          chartMetric_phi_maps_to_target e e' hz_source'
        have hφ_diff : MDifferentiableAt I I φ z := by
          have h_φ_eq_ψ : φ = ψ := rfl
          rw [h_φ_eq_ψ]
          have h_smooth := chart_transition_smooth e e' x hx_e hz_source' n he he'
          simpa [h_z_eq] using h_smooth.mdifferentiableAt hn1
        have he'_symm_diff : MDifferentiableAt I I e'.symm (φ z) := by
          have h_symm_smooth : ContMDiffOn I I n e'.symm e'.target :=
            contMDiffOn_symm_of_mem_maximalAtlas he'
          exact
            (h_symm_smooth.contMDiffAt (e'.open_target.mem_nhds hφz_target)).mdifferentiableAt hn1
        exact mfderiv_comp_of_eq he'_symm_diff hφ_diff rfl
      rw [h_comp_map]
      rfl
    have h_φ_eq_ψ : φ = ψ := rfl
    rw [← h_deriv_eq, h_φ_eq_ψ] at h_comp_w
    exact h_comp_w.symm
  rw [h_chain_rule_v, h_chain_rule_w]

end Manifold.Chart
