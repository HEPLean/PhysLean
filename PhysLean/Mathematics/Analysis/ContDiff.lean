/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import PhysLean.Mathematics.LinearAlgebra.BilinearForm

/-!
# Smoothness (ContDiff) Utilities

This file provides utility lemmas and constructions for working with smooth
functions (`ContDiff`) and continuity in the context of normed and finite-dimensional
vector spaces over a nontrivially normed field.

-/

namespace ContDiff

variable {𝕜 X V : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {f : X → V} {s : Set X} {x₀ : X} {n : WithTop ℕ∞}

-- First direction: if f is C^n, then φ ∘ f is C^n for any continuous linear functional φ
lemma comp_continuous_linear_apply_right
    (hf : ContDiffWithinAt 𝕜 n f s x₀) (φ : V →L[𝕜] 𝕜) :
    ContDiffWithinAt 𝕜 n (φ ∘ f) s x₀ :=
  ContDiffWithinAt.comp x₀ φ.contDiff.contDiffWithinAt hf (Set.mapsTo_univ _ _)

-- Second direction: in finite dimensions, if all projections are C^n, then f is C^n
lemma of_forall_coord [FiniteDimensional 𝕜 V] [CompleteSpace 𝕜]
    (h : ∀ φ : V →L[𝕜] 𝕜, ContDiffWithinAt 𝕜 n (φ ∘ f) s x₀) :
    ContDiffWithinAt 𝕜 n f s x₀ := by
  let b := Module.finBasis 𝕜 V
  let equiv := b.equivFunL
  suffices ContDiffWithinAt 𝕜 n (equiv ∘ f) s x₀ by
    have hequiv_symm_smooth : ContDiff 𝕜 ⊤ equiv.symm := ContinuousLinearEquiv.contDiff equiv.symm
    have hequiv_symm_smooth_n : ContDiff 𝕜 n equiv.symm :=
      ContDiff.of_le hequiv_symm_smooth (le_top : n ≤ ⊤)
    have h_eq : f = equiv.symm ∘ (equiv ∘ f) := by
      ext x; simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply];
    rw [h_eq]
    apply ContDiffWithinAt.comp x₀ hequiv_symm_smooth_n.contDiffWithinAt this (Set.mapsTo_univ _ _)
  apply contDiffWithinAt_pi.mpr
  intro i
  let coord_i : V →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
  exact h coord_i

-- Full bidirectional lemma
lemma iff_forall_coord [FiniteDimensional 𝕜 V] [CompleteSpace 𝕜] :
    ContDiffWithinAt 𝕜 n f s x₀ ↔
    ∀ φ : V →L[𝕜] 𝕜, ContDiffWithinAt 𝕜 n (φ ∘ f) s x₀ := by
  constructor
  · exact comp_continuous_linear_apply_right
  · exact of_forall_coord

end ContDiff

section ContinuityBounds

variable {𝕜 E F FHom : Type*} [NormedField 𝕜]

@[simp]
lemma AddMonoidHomClass.coe_fn_to_addMonoidHom
    [FunLike FHom E F] [AddZeroClass E] [AddZeroClass F]
    [AddMonoidHomClass FHom E F] (φ : FHom) :
    ⇑(AddMonoidHomClass.toAddMonoidHom φ) = ⇑φ := by
  rfl

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded additive map is continuous at zero. -/
lemma AddMonoidHom.continuousAt_zero_of_bound
    (φ : AddMonoidHom E F) {C : ℝ} (h : ∀ x, ‖φ x‖ ≤ C * ‖x‖) :
    ContinuousAt φ 0 := by
  rw [Metric.continuousAt_iff]
  intro ε εpos
  simp only [map_zero φ, dist_zero_right]
  by_cases hE : Subsingleton E
  · use 1
    refine ⟨zero_lt_one, fun y _hy_norm_lt_one => ?_⟩
    rw [@Subsingleton.elim E hE y 0, map_zero φ, norm_zero]
    exact εpos
  · have C_nonneg : 0 ≤ C := by
      obtain ⟨x_ne, y_ne, h_x_ne_y⟩ : ∃ x y : E, x ≠ y := by
        contrapose! hE; exact { allEq := hE }
      let z := x_ne - y_ne
      have hz_ne_zero : z ≠ 0 := sub_ne_zero_of_ne h_x_ne_y
      have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
      by_contra hC_is_neg
      push_neg at hC_is_neg
      have h_phi_z_bound := h z
      have H1 : 0 ≤ C * ‖z‖ := le_trans (norm_nonneg (φ z)) h_phi_z_bound
      have H2 : C * ‖z‖ < 0 := mul_neg_of_neg_of_pos hC_is_neg hz_norm_pos
      linarith [H1, H2]
    by_cases hC_eq_zero : C = 0
    · have phi_is_zero : φ = 0 := by
        ext x_val
        have h_phi_x_val_bound := h x_val
        rw [hC_eq_zero, zero_mul] at h_phi_x_val_bound
        exact norm_le_zero_iff.mp h_phi_x_val_bound
      use 1
      refine ⟨zero_lt_one, fun y _hy_norm_lt_one => ?_⟩
      rw [phi_is_zero, AddMonoidHom.zero_apply, norm_zero]
      exact εpos
    · have C_pos : 0 < C := lt_of_le_of_ne C_nonneg fun a => hC_eq_zero (_root_.id (Eq.symm a))
      use ε / C
      refine ⟨div_pos εpos C_pos, fun y hy_norm_lt_delta => ?_⟩
      calc
        ‖φ y‖ ≤ C * ‖y‖ := h y
        _ < C * (ε / C) := mul_lt_mul_of_pos_left hy_norm_lt_delta C_pos
        _ = ε := by rw [mul_div_cancel₀ ε hC_eq_zero]

omit [NormedSpace 𝕜 F] in
/-- A semi-linear map that is linearly bounded by the norm of its input is continuous. -/
lemma SemilinearMapClass.continuous_of_bound {𝕜₂ : Type*} [NormedField 𝕜₂] [NormedSpace 𝕜₂ F]
    [FunLike FHom E F] {σ : 𝕜 →+* 𝕜₂} [SemilinearMapClass FHom σ E F]
    {φ : FHom} {C : ℝ} (h : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : Continuous φ := by
  haveI : AddMonoidHomClass FHom E F := inferInstance
  let φ_add_hom : AddMonoidHom E F := AddMonoidHomClass.toAddMonoidHom φ
  exact continuous_of_continuousAt_zero φ_add_hom
    (AddMonoidHom.continuousAt_zero_of_bound φ_add_hom h)

/-- A function that is linearly bounded by the norm of its input is continuous. -/
lemma AddMonoidHomClass.continuous_of_bound' [FunLike FHom E F] [AddMonoidHomClass FHom E F]
    {φ : FHom} {C : ℝ} (h : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : Continuous φ := by
  let φ_add_hom : AddMonoidHom E F := AddMonoidHomClass.toAddMonoidHom φ
  exact continuous_of_continuousAt_zero φ_add_hom
    (AddMonoidHom.continuousAt_zero_of_bound φ_add_hom h)

end ContinuityBounds

namespace ContinuousLinearMap

variable {X₁ E₁ F₁ G₁ E₁' F₁' : Type*} [NontriviallyNormedField 𝕜₁]
  [NormedAddCommGroup X₁] [NormedSpace 𝕜₁ X₁]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜₁ E₁]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁]
  [NormedAddCommGroup G₁] [NormedSpace 𝕜₁ G₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜₁ E₁']
  [NormedAddCommGroup F₁'] [NormedSpace 𝕜₁ F₁']
  {n₁ : WithTop ℕ∞}

/-- The `ContinuousLinearMap.bilinearComp` operation is smooth.
    Given smooth functions `f : X₁ → (E₁ →L[𝕜₁] F₁ →L[𝕜₁] G₁)`, `g : X₁ → (E₁' →L[𝕜₁] E₁)`,
    and `h : X₁ → (F₁' →L[𝕜₁] F₁)`, the composition `x ↦ (f x).bilinearComp (g x) (h x)`
    is smooth. -/
lemma contDiff_bilinearComp
    {f : X₁ → E₁ →L[𝕜₁] F₁ →L[𝕜₁] G₁} {g : X₁ → E₁' →L[𝕜₁] E₁} {h : X₁ → F₁' →L[𝕜₁] F₁}
    (hf : ContDiff 𝕜₁ n₁ f) (hg : ContDiff 𝕜₁ n₁ g) (hh : ContDiff 𝕜₁ n₁ h) :
    ContDiff 𝕜₁ n₁ fun x => (f x).bilinearComp (g x) (h x) := by
  have h1 : ContDiff 𝕜₁ n₁ (fun x ↦ (f x).comp (g x)) := ContDiff.clm_comp hf hg
  let L_flip1 := ContinuousLinearMap.flipₗᵢ 𝕜₁ E₁' F₁ G₁
  have eq_flip : ∀ x, L_flip1 ((f x).comp (g x)) = ((f x).comp (g x)).flip := by
    intro x
    rfl
  have h2 : ContDiff 𝕜₁ n₁ (fun x => ((f x).comp (g x)).flip) := by
    have hL₁ : ContDiff 𝕜₁ n₁ L_flip1 :=
      (ContinuousLinearMap.contDiff (𝕜 := 𝕜₁) (E := E₁' →L[𝕜₁] F₁ →L[𝕜₁] G₁)
        (F := F₁ →L[𝕜₁] E₁' →L[𝕜₁] G₁) L_flip1).of_le le_top
    have h2' : ContDiff 𝕜₁ n₁ (fun x => L_flip1 ((f x).comp (g x))) :=
      ContDiff.comp hL₁ h1
    exact (funext eq_flip).symm ▸ h2'
  have h3 : ContDiff 𝕜₁ n₁ (fun x => (((f x).comp (g x)).flip).comp (h x)) :=
    ContDiff.clm_comp h2 hh
  let L_flip2 := ContinuousLinearMap.flipₗᵢ 𝕜₁ F₁' E₁' G₁
  have eq_flip2 : ∀ x, L_flip2 ((((f x).comp (g x)).flip).comp (h x)) =
      ((((f x).comp (g x)).flip).comp (h x)).flip := by
    intro x
    rfl
  have h4 : ContDiff 𝕜₁ n₁ (fun x => ((((f x).comp (g x)).flip).comp (h x)).flip) := by
    have hL₂ : ContDiff 𝕜₁ n₁ L_flip2 :=
      (ContinuousLinearMap.contDiff (𝕜 := 𝕜₁) (E := F₁' →L[𝕜₁] E₁' →L[𝕜₁] G₁)
        (F := E₁' →L[𝕜₁] F₁' →L[𝕜₁] G₁) L_flip2).of_le le_top
    have h4' := ContDiff.comp hL₂ h3
    exact (funext eq_flip2).symm ▸ h4'
  exact h4

variable {X₁ E₁ F₁ G₁ E₁' F₁' : Type*} [NontriviallyNormedField 𝕜₁]
  [NormedAddCommGroup X₁] [NormedSpace 𝕜₁ X₁]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜₁ E₁] [FiniteDimensional 𝕜₁ E₁]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] [FiniteDimensional 𝕜₁ F₁]
  [NormedAddCommGroup G₁] [NormedSpace 𝕜₁ G₁] [FiniteDimensional 𝕜₁ G₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜₁ E₁'] [FiniteDimensional 𝕜₁ E₁']
  [NormedAddCommGroup F₁'] [NormedSpace 𝕜₁ F₁'] [FiniteDimensional 𝕜₁ F₁']
  {n₁ : WithTop ℕ∞}

/-- The "flip" operation on continuous bilinear maps is smooth. -/
lemma flip_contDiff {F₁ F₂ R : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup R] [NormedSpace ℝ R] :
    ContDiff ℝ ⊤ (fun f : F₁ →L[ℝ] F₂ →L[ℝ] R => ContinuousLinearMap.flip f) := by
  let flip_clm :=
    (ContinuousLinearMap.flipₗᵢ ℝ F₁ F₂ R).toContinuousLinearEquiv.toContinuousLinearMap
  exact
    @ContinuousLinearMap.contDiff ℝ _
      (F₁ →L[ℝ] F₂ →L[ℝ] R) _ _ (F₂ →L[ℝ] F₁ →L[ℝ] R) _ _ _ flip_clm

/-- Composition of a bilinear map with a linear map in the first argument is smooth. -/
lemma comp_first_contDiff {F₁ F₂ F₃ R : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    [NormedAddCommGroup R] [NormedSpace ℝ R] :
    ContDiff ℝ ⊤ (fun p : (F₂ →L[ℝ] F₃ →L[ℝ] R) × (F₁ →L[ℝ] F₂) =>
      ContinuousLinearMap.comp p.1 p.2) := by
  exact ContDiff.clm_comp contDiff_fst contDiff_snd

variable {E₁_₂ : Type*} {E₂_₂ : Type*} {R₂ : Type*}
variable [NormedAddCommGroup E₁_₂] [NormedSpace ℝ E₁_₂]
variable [NormedAddCommGroup E₂_₂] [NormedSpace ℝ E₂_₂]
variable [NormedAddCommGroup R₂] [NormedSpace ℝ R₂]

/-- The pullback of a bilinear map by a linear map is smooth with respect to both arguments. -/
theorem contDiff_pullbackBilinear_op :
    ContDiff ℝ ⊤ (fun p : (E₂_₂ →L[ℝ] E₂_₂ →L[ℝ] R₂) × (E₁_₂ →L[ℝ] E₂_₂) =>
      BilinearForm.pullback p.1 p.2) := by
  apply contDiff_bilinearComp
  · exact (contDiff_fst (E := (E₂_₂ →L[ℝ] E₂_₂ →L[ℝ] R₂)) (F := (E₁_₂ →L[ℝ] E₂_₂))).of_le le_top
  · exact (contDiff_snd (E := (E₂_₂ →L[ℝ] E₂_₂ →L[ℝ] R₂)) (F := (E₁_₂ →L[ℝ] E₂_₂))).of_le le_top
  · exact (contDiff_snd (E := (E₂_₂ →L[ℝ] E₂_₂ →L[ℝ] R₂)) (F := (E₁_₂ →L[ℝ] E₂_₂))).of_le le_top

end ContinuousLinearMap
