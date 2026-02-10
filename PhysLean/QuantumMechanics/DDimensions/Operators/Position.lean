/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Position vector operator

In this module we define:
- The position operator on Schwartz maps, component-wise.

-/

namespace QuantumMechanics
noncomputable section
open Space
open ContDiff SchwartzMap

/-- Component `i` of the position operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator {d : ℕ} (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ coordCLM i)

@[inherit_doc positionOperator]
macro "𝐱[" i:term "]" : term => `(positionOperator $i)

lemma positionOperator_apply_fun {d : ℕ} (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = (fun x ↦ x i * ψ x) := by
  unfold positionOperator
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rw [Function.comp_apply, smul_eq_mul]
    rw [coordCLM_apply, coord_apply]
  · fun_prop

lemma positionOperator_apply {d : ℕ} (i : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐱[i] ψ x = x i * ψ x := by rw [positionOperator_apply_fun]

end
end QuantumMechanics
