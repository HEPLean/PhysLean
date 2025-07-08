/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import Mathlib.Analysis.Distribution.FourierSchwartz
/-!

# Schwartz submodule of the Hilbert space

This can be used to define e.g.
the rigged Hilbert space.

-/

namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory

/-- The submodule of the Hilbert space spanned by Schwartz maps. -/
def schwartzSubmodule : Submodule ℂ HilbertSpace :=
  Submodule.map (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume) ⊤

@[inherit_doc schwartzSubmodule]
scoped notation "Φ" => schwartzSubmodule

/-- The linear equivalence between the Schwartz submodule
  of the Hilbert space and the module of Schwartz maps. -/
def schwartzSubmoduleEquiv : schwartzSubmodule ≃ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun ψ := Classical.choose ψ.2
  invFun ψ := ⟨SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume ψ, by use ψ; simp⟩
  left_inv ψ := by
    have h1 := (Classical.choose_spec ψ.2).2
    simp only [Submodule.top_coe, Set.mem_univ, SchwartzMap.toLpCLM_apply, true_and] at h1
    ext1
    simp only [Submodule.top_coe, Set.mem_univ, SchwartzMap.toLpCLM_apply, true_and]
    exact h1
  right_inv ψ := by
    let ψ' : schwartzSubmodule :=
      ⟨SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume ψ, by use ψ; simp⟩
    change Classical.choose ψ'.2 = ψ
    apply SchwartzMap.injective_toLp 2
    dsimp
    change (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume) (Classical.choose ψ'.2) = _
    rw [(Classical.choose_spec ψ'.2).2]
    rfl
  map_add' ψ1 ψ2 := by
    let ψ1' := Classical.choose ψ1.2
    let ψ2' := Classical.choose ψ2.2
    apply SchwartzMap.injective_toLp 2
    change (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume)
      (Classical.choose (ψ1 + ψ2).2) = (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume) ψ1' +
      (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume) ψ2'
    rw [(Classical.choose_spec ψ1.2).2, (Classical.choose_spec ψ2.2).2,
        (Classical.choose_spec (ψ1 + ψ2).2).2]
    rfl
  map_smul' a ψ := by
    let ψ' := Classical.choose ψ.2
    apply SchwartzMap.injective_toLp 2
    change (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume) (Classical.choose (a • ψ).2) =
      a • (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume) (Classical.choose ψ.2)
    rw [(Classical.choose_spec (a • ψ).2).2, (Classical.choose_spec ψ.2).2]
    rfl

@[simp]
lemma schwartzMap_toLpCLM_mem_schwartzSubmodule (ψ : SchwartzMap ℝ ℂ) :
    ψ.toLp 2 volume ∈ schwartzSubmodule := by
  use ψ
  simp

/-- The inclusion of the Hilbert space into the dual of the submodule
  of Schwartz maps. -/
def inclDualSchwartzSubmodule: HilbertSpace →ₛₗ[starRingEnd ℂ] Module.Dual ℂ Φ :=
  toBra.domRestrict₂ Φ

/-- The inclusion of the Hilbert space into the dual of the submodule
  of Schwartz maps is injective. -/
@[sorryful]
lemma inclDualSchwartzSubmodule_injective : Function.Injective inclDualSchwartzSubmodule := by
  sorry

open InnerProductSpace

lemma schwartzSubmodule_coe_ae_schwartzSubmoduleEquiv (ψ : schwartzSubmodule) :
    ψ.1 =ᶠ[ae volume] (schwartzSubmoduleEquiv ψ) := by
  simp only [schwartzSubmoduleEquiv, Submodule.top_coe, Set.mem_univ, SchwartzMap.toLpCLM_apply,
    true_and, LinearEquiv.coe_mk, AddHom.coe_mk]
  rw [← (Classical.choose_spec ψ.2).2]
  simpa using SchwartzMap.coeFn_toLp _ 2 volume

lemma inner_schwartzSubmodule (ψ1 ψ2 : schwartzSubmodule) :
    ⟪ψ1, ψ2⟫_ℂ = ∫ x : ℝ, starRingEnd ℂ ((schwartzSubmoduleEquiv ψ1) x) *
      (schwartzSubmoduleEquiv ψ2) x := by
  simp only [Submodule.coe_inner]
  apply MeasureTheory.integral_congr_ae
  have h1 : ψ1.1 =ᶠ[ae volume] (schwartzSubmoduleEquiv ψ1) :=
    schwartzSubmodule_coe_ae_schwartzSubmoduleEquiv ψ1
  have h2 : ψ2.1 =ᶠ[ae volume] (schwartzSubmoduleEquiv ψ2) :=
    schwartzSubmodule_coe_ae_schwartzSubmoduleEquiv ψ2
  filter_upwards [h1, h2] with _ h1 h2
  rw [h1, h2]
  simp
  ring

end HilbertSpace
end
end OneDimension
end QuantumMechanics
