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

TODO "G4FRT" "Update the definition of `planewaveFunctional` to use the
  live in `NormedSpace.Dual` instead of `Module.Dual`."

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

/-- Two elements of the Schwartz submodule are equal if and only if they are equal on
  all applications of `planewaveFunctional`. -/
lemma eq_of_eq_planewaveFunctional {ψ1 ψ2 : schwartzSubmodule}
    (h : ∀ k, planewaveFunctional k ψ1 = planewaveFunctional k ψ2) :
    ψ1 = ψ2 := by
  apply schwartzSubmoduleEquiv.injective
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext k
  exact h k

end HilbertSpace
end
end OneDimension
end QuantumMechanics
