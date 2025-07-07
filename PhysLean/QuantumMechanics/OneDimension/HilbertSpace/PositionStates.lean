/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.SchwartzSubmodule
/-!

# Position states

We define plane waves as a member of the dual of the
Schwartz submodule of the Hilbert space.

-/
namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory

/-- Position state as a member of the dual of the
  Schwartz submodule of the Hilbert space. -/
def positionState (x : ℝ) : Module.Dual ℂ Φ := by
  refine (?_ : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ) ∘ₗ schwartzSubmoduleEquiv
  exact
  { toFun ψ := ψ x,
    map_add' ψ1 ψ2 := by simp
    map_smul' a ψ := by simp
  }

lemma positionState_apply (x : ℝ) (ψ : schwartzSubmodule) :
    positionState x ψ = schwartzSubmoduleEquiv ψ x := rfl

/-- Two elements of the `schwartzSubmodule` are equal if they
  are equal on all position states. -/
lemma eq_of_eq_positionState {ψ1 ψ2 : schwartzSubmodule}
    (h : ∀ x, positionState x ψ1 = positionState x ψ2) :
    ψ1 = ψ2 := by
  apply schwartzSubmoduleEquiv.injective
  ext x
  exact h x

end HilbertSpace
end
end OneDimension
end QuantumMechanics
