/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# PartialHomeomorph Utilities for Manifolds

This file contains lemmas for `PartialHomeomorph` specifically relevant to manifolds.
-/

namespace PartialHomeomorph

open Set ModelWithCorners PartialEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}

/-- The toPartialEquiv of the symm of a partial homeomorphism equals the symm of its
toPartialEquiv. -/
@[simp, mfld_simps]
theorem toPartialEquiv_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : PartialHomeomorph X Y) :
    e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

/-- The function component of the symm of a partial homeomorphism equals its invFun. -/
theorem coe_symm_eq_invFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : PartialHomeomorph X Y) : ⇑e.symm = e.invFun :=
  rfl

omit [NormedAddCommGroup H] [NormedSpace 𝕜 H] in
/-- If a partial homeomorphism belongs to the `contDiffGroupoid n I`, then the forward map is
`C^n` on its source. This extracts the smoothness property directly from groupoid membership. -/
theorem contMDiffOn_of_mem_groupoid {e : PartialHomeomorph H H}
    (he : e ∈ contDiffGroupoid n I) : ContMDiffOn I I n e e.source :=
  contMDiffOn_of_mem_contDiffGroupoid he

omit [NormedAddCommGroup H] [NormedSpace 𝕜 H] in
/-- The coordinate change map `φ = e' ∘ e.symm` between two charts `e` and `e'` is `C^n` smooth
    at a point `y = e x` if `x` is in the intersection of the sources of `e` and `e'`. -/
lemma contMDiffAt_coord_change
    {e e' : PartialHomeomorph M H} {x : M}
    (hx_e_source : x ∈ e.source) (hx_e'_source : x ∈ e'.source)
    (he : e ∈ (contDiffGroupoid n I).maximalAtlas M)
    (he' : e' ∈ (contDiffGroupoid n I).maximalAtlas M) :
    ContMDiffAt I I n (e' ∘ e.symm) (e x) := by
  let y := e x
  have hy_target : y ∈ e.target := e.mapsTo hx_e_source
  let transition_domain := e.target ∩ e.symm ⁻¹' e'.source
  have hy_domain : y ∈ transition_domain := ⟨hy_target, by
    rw [@Set.mem_preimage];
    rw [e.left_inv hx_e_source];
    exact hx_e'_source⟩
  have open_domain : IsOpen transition_domain := e.isOpen_inter_preimage_symm e'.open_source
  have h_compatible := StructureGroupoid.compatible_of_mem_maximalAtlas he he'
  have h_transition_smooth : ContMDiffOn I I n (e' ∘ e.symm) transition_domain :=
    contMDiffOn_of_mem_groupoid h_compatible
  exact h_transition_smooth.contMDiffAt (open_domain.mem_nhds hy_domain)

omit [NormedAddCommGroup H] [NormedSpace 𝕜 H] in
/-- The coordinate change map between atlas charts is smooth in the manifold sense. -/
lemma contMDiffAt_atlas_coord_change [IsManifold I n M]
    {e e' : PartialHomeomorph M H}
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) {x : M}
    (hx_e_source : x ∈ e.source) (hx_e'_source : x ∈ e'.source) :
    ContMDiffAt I I n (e' ∘ e.symm) (e x) := by
  let transition_domain := e.target ∩ e.symm ⁻¹' e'.source
  have open_domain : IsOpen transition_domain := e.isOpen_inter_preimage_symm e'.open_source
  have hy_target : e x ∈ e.target := e.mapsTo hx_e_source
  have hy_domain : e x ∈ transition_domain := ⟨hy_target, by
    show e.symm (e x) ∈ e'.source
    rw [e.left_inv hx_e_source]
    exact hx_e'_source⟩
  have h_compatible : e.symm.trans e' ∈ contDiffGroupoid n I := HasGroupoid.compatible he he'
  have h_transition_smooth : ContMDiffOn I I n (e' ∘ e.symm) transition_domain :=
    contMDiffOn_of_mem_groupoid h_compatible
  exact h_transition_smooth.contMDiffAt (open_domain.mem_nhds hy_domain)

/-- The coordinate change map `φ = e' ∘ e.symm` between two charts `e` and `e'` taken from the
    atlas is `C^n` smooth at a point `y = e x` if `x` is in the intersection of their sources. -/
lemma contDiffAt_atlas_coord_change
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    {n : WithTop ℕ∞} [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf 𝕜 E) n M]
    {e e' : PartialHomeomorph M E}
    (he : e ∈ atlas E M) (he' : e' ∈ atlas E M) {x : M}
    (hx_e_source : x ∈ e.source) (hx_e'_source : x ∈ e'.source) :
    let y := e x
    ContDiffAt 𝕜 n (e' ∘ e.symm) y := by
  intro y
  have hy_target : y ∈ e.target := e.mapsTo hx_e_source
  let transition_domain := e.target ∩ e.symm ⁻¹' e'.source
  have hy_domain : y ∈ transition_domain := by
    refine ⟨hy_target, ?_⟩
    simp only [Set.mem_preimage]
    rw [e.left_inv hx_e_source]
    exact hx_e'_source
  have h_compatible : e.symm.trans e' ∈ contDiffGroupoid n (modelWithCornersSelf 𝕜 E) :=
    HasGroupoid.compatible he he'
  have h_transition_mfd_smooth : ContMDiffOn (modelWithCornersSelf 𝕜 E)
      (modelWithCornersSelf 𝕜 E) n (e' ∘ e.symm) transition_domain :=
    contMDiffOn_of_mem_contDiffGroupoid h_compatible
  have h_transition_smooth : ContDiffOn 𝕜 n (e' ∘ e.symm) transition_domain :=
    (contMDiffOn_iff_contDiffOn).mp h_transition_mfd_smooth
  have open_domain : IsOpen transition_domain :=
    ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target e'.open_source
  exact h_transition_smooth.contDiffAt (IsOpen.mem_nhds open_domain hy_domain)

lemma extChartAt_eq_extend_chartAt {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' E') (x_m : M) [ChartedSpace E' M] :
    extChartAt I' x_m = (chartAt E' x_m).extend I' :=
  rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [K_bl : I.Boundaryless] -- Changed K to I

omit [NormedSpace 𝕜 E] in
/-- Domain of the transition map `e.symm.trans e'` contains `e x`. -/
lemma transition_map_source_contains_image_point {E_chart : Type*} [TopologicalSpace E_chart]
    (e e' : PartialHomeomorph M E_chart) (x : M)
    (hx_e_source : x ∈ e.source) (hx_e'_source : x ∈ e'.source) :
    (e x) ∈ (e.symm.toPartialEquiv.trans e'.toPartialEquiv).source := by
  rw [@PartialEquiv.trans_source'']
  simp only [symm_toPartialEquiv, PartialEquiv.symm_symm, toFun_eq_coe, PartialEquiv.symm_target,
    Set.mem_image, Set.mem_inter_iff]
  rw [← @symm_image_target_eq_source]
  rw [@symm_image_target_eq_source]
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl
    }
    · simp_all only [and_self]

variable {f_map : H → H} {y_pt : H} -- Renamed f, y to avoid clash

omit [NormedAddCommGroup H] [NormedSpace 𝕜 H] K_bl in
lemma contDiffAt_chart_expression_of_contMDiffAt [I.Boundaryless]
    (h_contMDiff : ContMDiffAt I I n f_map y_pt) :
    ContDiffAt 𝕜 n (I ∘ f_map ∘ I.symm) (I y_pt) := by
  rw [@contMDiffAt_iff] at h_contMDiff
  obtain ⟨_, h_diff⟩ := h_contMDiff
  have h_fun_eq : (extChartAt I (f_map y_pt)) ∘ f_map ∘ (extChartAt I y_pt).symm =
      I ∘ f_map ∘ I.symm := by
    simp only [extChartAt, extend, refl_partialEquiv, PartialEquiv.refl_source,
      singletonChartedSpace_chartAt_eq, PartialEquiv.refl_trans, toPartialEquiv_coe,
      toPartialEquiv_coe_symm]
  have h_point_eq : (extChartAt I y_pt) y_pt = I y_pt := by
    simp only [extChartAt, extend, refl_partialEquiv, PartialEquiv.refl_source,
      singletonChartedSpace_chartAt_eq, PartialEquiv.refl_trans, toPartialEquiv_coe]
  have h_diff' : ContDiffWithinAt 𝕜 n (I ∘ f_map ∘ I.symm) (Set.range I) (I y_pt) := by
    rw [← h_fun_eq, ← h_point_eq]
    exact h_diff
  apply ContDiffWithinAt.contDiffAt h_diff'
  have : I y_pt ∈ interior (Set.range I) := by
    have h_range : Set.range I = Set.univ := I.range_eq_univ
    simp [h_range, interior_univ]
  exact mem_interior_iff_mem_nhds.mp this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : ModelWithCorners ℝ E E} [I.Boundaryless]
variable {n : WithTop ℕ∞}

lemma contDiff_of_boundaryless_model_on_self :
    ContDiff ℝ n (modelWithCornersSelf ℝ E).toFun := by
  let I := modelWithCornersSelf ℝ E
  have h_mem_groupoid : PartialHomeomorph.refl E ∈ contDiffGroupoid n I :=
    StructureGroupoid.id_mem (contDiffGroupoid n I)
  have h_contMDiffOn : ContMDiffOn I I n (PartialHomeomorph.refl E) Set.univ :=
    contMDiffOn_of_mem_contDiffGroupoid h_mem_groupoid
  rw [contMDiffOn_iff_contDiffOn] at h_contMDiffOn
  simpa [contDiffOn_univ] using h_contMDiffOn

lemma contDiff_symm_of_boundaryless_model_on_self :
    ContDiff ℝ n (modelWithCornersSelf ℝ E).symm.toFun := by
  let I := modelWithCornersSelf ℝ E
  have h_mem_groupoid : PartialHomeomorph.refl E ∈ contDiffGroupoid n I :=
    StructureGroupoid.id_mem (contDiffGroupoid n I)
  have h_mdf := contMDiffOn_of_mem_contDiffGroupoid h_mem_groupoid
  exact contDiffOn_univ.1 (contMDiffOn_iff_contDiffOn.1 h_mdf)

omit [NormedSpace ℝ E]  in
/-- Functional equality e.symm = e'.symm ∘ φ-/
lemma apply_symm_eq_apply_symm_comp_transition (e e' : PartialHomeomorph M E) :
    let φ_pe := e.symm.toPartialEquiv.trans e'.toPartialEquiv;
    ∀ z ∈ φ_pe.source, e.symm z = (e'.symm ∘ ⇑φ_pe) z := by
  intro φ_pe z hz_in_φ_source
  rw [PartialEquiv.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hz_in_φ_source
  rcases hz_in_φ_source with ⟨_, hz_esymm_z_in_eprime_source⟩
  simp only [Function.comp_apply, PartialEquiv.trans_apply,
             PartialHomeomorph.coe_coe]
  exact Eq.symm (e'.left_inv' hz_esymm_z_in_eprime_source)

omit [NormedSpace ℝ E]  in
/-- Image of y under φ-/
lemma apply_transition_map_eq_chart_apply (e e' : PartialHomeomorph M E) (x : M)
    (hx_e_source : x ∈ e.source) :
    (e.symm.toPartialEquiv.trans e'.toPartialEquiv) (e x) = e' x := by
  simp only [PartialEquiv.trans_apply, PartialHomeomorph.coe_coe,
             e.left_inv hx_e_source]

end PartialHomeomorph
