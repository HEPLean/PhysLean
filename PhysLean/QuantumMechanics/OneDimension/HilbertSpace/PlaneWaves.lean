/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.SchwartzSubmodule
/-!

# Plane waves

We define plane waves as a member of the dual of the
Schwartz submodule of the Hilbert space.

-/

namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory

/-- Plane waves as a member of the dual of the
  Schwartz submoudle of the Hilbert space.

  For a given `k` this corresponds to the plane wave
  `exp (2π I k x)`. -/
def planewaveFunctional (k : ℝ) : Module.Dual ℂ Φ := by
  refine (?_ : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ) ∘ₗ schwartzSubmoduleEquiv
  refine (?_ : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ) ∘ₗ (SchwartzMap.fourierTransformCLM ℂ).toLinearMap
  exact
  { toFun ψ := ψ k,
    map_add' ψ1 ψ2 := by simp
    map_smul' a ψ := by simp
  }

open FourierTransform in
lemma planewaveFunctional_apply (k : ℝ) (ψ : schwartzSubmodule) :
    planewaveFunctional k ψ = 𝓕 (schwartzSubmoduleEquiv ψ) k := rfl

end HilbertSpace
end
end OneDimension
end QuantumMechanics
