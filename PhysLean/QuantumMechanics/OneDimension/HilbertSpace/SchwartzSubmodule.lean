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
    change  (SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume)
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

/-- The inclusion of the Hilbert space into the dual of the submodule
  of Schwartz maps. -/
def inclDualSchwartzSubmodule: HilbertSpace →ₛₗ[starRingEnd ℂ] Module.Dual ℂ Φ :=
  toBra.domRestrict₂ Φ

/-- The invlusion of the Hilbert space into the dual of the submodule
  of Schwartz maps is injective. -/
@[sorryful]
lemma inclDualSchwartzSubmodule_injective : Function.Injective inclDualSchwartzSubmodule := by
  sorry

end HilbertSpace
end
end OneDimension
end QuantumMechanics
