/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Geometry.Manifold.IsManifold.Basic
import PhysLean.Mathematics.Analysis.ContDiff

/-!
# Smoothness of Bilinear Forms in Chart Coordinates

This file contains lemmas about the smoothness of bilinear forms in chart coordinates.
-/
noncomputable section
open BilinearForm
open Filter

variable {E : Type v} {M : Type v} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
variable {I : ModelWithCorners ℝ E E} [ModelWithCorners.Boundaryless I]
variable [inst_mani_smooth : IsManifold I (n + 1) M] -- For C^{n+1} manifold for C^n metric
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

noncomputable instance (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  show NormedAddCommGroup E from inferInstance

noncomputable instance (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  show NormedSpace ℝ E from inferInstance
namespace Manifold.ChartSmoothness

open BilinearForm ContDiff ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {f_bilin : X → E →L[ℝ] E →L[ℝ] ℝ} {s_set : Set X} {x₀_pt : X}
-- n is from the outer scope (smoothness of the metric)

lemma contDiffWithinAt_eval_bilinear_apply (hf : ContDiffWithinAt ℝ n f_bilin s_set x₀_pt)
    (v w : E) :
    ContDiffWithinAt ℝ n (fun x => f_bilin x v w) s_set x₀_pt := by
  let eval_vw : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ := BilinearForm.eval_vectors_continuousLinear v w
  exact (eval_vw.contDiff.of_le le_top).contDiffWithinAt.comp x₀_pt hf (Set.mapsTo_univ _ _)

variable[FiniteDimensional ℝ E]

lemma contDiffWithinAt_bilinear_apply_iff_forall_coord :
    (∀ v w, ContDiffWithinAt ℝ n (fun x => f_bilin x v w) s_set x₀_pt) →
    ContDiffWithinAt ℝ n f_bilin s_set x₀_pt := by
  intro h_comp
  rw [ContDiff.iff_forall_coord (V := E →L[ℝ] E →L[ℝ] ℝ) (𝕜 := ℝ)]
  intro φ
  let b := Module.finBasis ℝ E
  obtain ⟨e_forms, h_e_forms_def⟩ := BilinearForm.elementary_bilinear_forms_def b
  have h_f_decomp : ∀ (x : X), f_bilin x =
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, ((f_bilin x) (b i) (b j)) • e_forms i j := by
    intro x
    obtain ⟨e, h_e_prop, h_decomp⟩ := BilinearForm.decomposition b (f_bilin x)
    have e_eq_e_forms : e = e_forms := by
      ext i j v w
      rw [h_e_prop i j v w, h_e_forms_def i j v w]
    rw [e_eq_e_forms] at h_decomp
    exact h_decomp
  have h_phi_f : ∀ x, φ (f_bilin x) =
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, ((f_bilin x) (b i) (b j)) * φ (e_forms i j) := by
    intro x
    rw [h_f_decomp x]
    have h_expand : φ (∑ i ∈ Finset.univ,
      ∑ j ∈ Finset.univ, ((f_bilin x) (b i) (b j)) • e_forms i j) =
        ∑ i ∈ Finset.univ, φ (∑ j ∈ Finset.univ, ((f_bilin x) (b i) (b j)) • e_forms i j) :=
        ContinuousLinearMap.map_finset_sum φ Finset.univ (fun i => ∑ j ∈ Finset.univ,
        ((f_bilin x) (b i) (b j)) • e_forms i j)
    rw [h_expand]
    apply Finset.sum_congr rfl
    intro i _
    have h_expand_inner : φ (∑ j ∈ Finset.univ, ((f_bilin x) (b i) (b j)) • e_forms i j) =
                          ∑ j ∈ Finset.univ, φ (((f_bilin x) (b i) (b j)) • e_forms i j) :=
      ContinuousLinearMap.map_finset_sum φ Finset.univ (fun j =>
        ((f_bilin x) (b i) (b j)) • e_forms i j)
    rw [h_expand_inner]
    apply Finset.sum_congr rfl
    intro j _
    rw [ContinuousLinearMap.map_smul]
    rw [smul_eq_mul]
    rw [← h_f_decomp]
  have h_goal : ContDiffWithinAt ℝ n (fun x => φ (f_bilin x)) s_set x₀_pt := by
    simp only [h_phi_f]
    apply ContDiffWithinAt.sum
    intro i _
    apply ContDiffWithinAt.sum
    intro j _
    have h_term_smooth : ContDiffWithinAt ℝ n (fun x => f_bilin x (b i) (b j)) s_set x₀_pt :=
      h_comp (b i) (b j)
    have h_const : ContDiffWithinAt ℝ n (fun x => φ (e_forms i j)) s_set x₀_pt :=
      contDiffWithinAt_const
    exact ContDiffWithinAt.mul h_term_smooth h_const
  exact h_goal

/--
A bilinear form `f_bilin : X → E → E → F` is continuously differentiable of order `n_level`
at a point `x₀_pt` within a set `s_set` if and only if for all vectors `v w : E`, the function
`x ↦ f_bilin x v w` is continuously differentiable of order `n_level` at `x₀_pt` within `s_set`.

This provides an equivalence between the continuous differentiability of a bilinear map
and the continuous differentiability of all its partial evaluations.
-/
theorem contDiffWithinAt_bilinear_iff {n_level : WithTop ℕ∞} :
    (∀ (v w : E), ContDiffWithinAt ℝ n_level (fun x => f_bilin x v w) s_set x₀_pt) ↔
    (ContDiffWithinAt ℝ n_level f_bilin s_set x₀_pt) := by
  constructor
  · intro h; exact contDiffWithinAt_bilinear_apply_iff_forall_coord h
  · intro h; exact contDiffWithinAt_eval_bilinear_apply h

/--
A bilinear form `f_bilin : X → E → E → F` is continuously differentiable of order `n_level`
on a set `s` if and only if for all vectors `v w : E`, the function `x ↦ f_bilin x v w`
is continuously differentiable of order `n_level` on `s`.

This extends `contDiffWithinAt_bilinear_iff` from a single point to an entire set.
-/
theorem contDiffOn_bilinear_iff {n_level : WithTop ℕ∞} (s : Set X) :
    (∀ (v w : E), ContDiffOn ℝ n_level (fun x => f_bilin x v w) s) ↔
    (ContDiffOn ℝ n_level f_bilin s) := by
  simp only [ContDiffOn, contDiffWithinAt_bilinear_iff (n_level := n_level)]
  constructor
  · intro h x hx
    apply contDiffWithinAt_bilinear_apply_iff_forall_coord
    intro v w
    exact h v w x hx
  · intro h v w x hx
    exact contDiffWithinAt_eval_bilinear_apply (h x hx) v w

end Manifold.ChartSmoothness
