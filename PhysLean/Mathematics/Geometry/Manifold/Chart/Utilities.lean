/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.PartialHomeomorph
/-!
# Utilities for Charts and Transition Maps

This file contains general utility lemmas for charts and transition maps.
-/

namespace Manifold.Chart
variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E]
variable [TopologicalSpace M]

/-- The domain where the chart transition is well-defined forms a neighborhood of y. -/
lemma chartMetric_domain_in_nhds (e e' : PartialHomeomorph M E) (y : E)
    (hy : y ∈ e.target) (hx_source' : e.symm y ∈ e'.source) :
    let s := e.target ∩ e.symm ⁻¹' e'.source
    s ∈ nhds y := by
  intro s
  apply Filter.inter_mem
  · exact e.open_target.mem_nhds hy
  · exact (e.continuousAt_symm hy).preimage_mem_nhds (e'.open_source.mem_nhds hx_source')

/-- When applying φ = e' ∘ e.symm to a point z in the domain s, the result is in e'.target -/
lemma chartMetric_phi_in_target (e e' : PartialHomeomorph M E) {z : E}
    (hz_source' : e.symm z ∈ e'.source) :
    let φ := e'.toPartialEquiv ∘ e.symm
    φ z ∈ e'.target := by
  intro φ
  unfold φ
  exact e'.mapsTo hz_source'

/-- When applying φ = e' ∘ e.symm to a point z, the result is in e'.target -/
lemma chartMetric_phi_maps_to_target (e e' : PartialHomeomorph M E) {z : E}
    (hz_source' : e.symm z ∈ e'.source) :
    let φ := e' ∘ e.symm
    φ z ∈ e'.target := by
  intro φ
  unfold φ
  exact e'.mapsTo hz_source'

/-- The composition of chart maps preserves points: e'.symm (e' (e.symm z)) = e.symm z -/
lemma chart_map_composition_identity (e e' : PartialHomeomorph M E) {z : E}
    (hz_source' : e.symm z ∈ e'.source) :
    let φ := e' ∘ e.symm
    let x_z := e.symm z
    e'.symm (φ z) = x_z := by
  intro φ x_z
  unfold φ
  simp only [Function.comp_apply, PartialHomeomorph.coe_coe]
  rw [e'.left_inv hz_source']

end Manifold.Chart
