/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.Operators.Position
import PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
/-!

# Commutation relations

The commutation relations between different operators.

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace SchwartzMap

/-!

## Commutation relation between position and momentum operators

-/

lemma positionOperatorSchwartz_commutation_momentumOperatorSchwartz
    (ψ : 𝓢(ℝ, ℂ)) : positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = (Complex.I * ℏ) • ψ := by
  ext x
  simp [momentumOperatorSchwartz_apply, positionOperatorSchwartz_apply,
    positionOperatorSchwartz_apply_fun]
  rw [deriv_fun_mul]
  have h1 : deriv Complex.ofReal x = 1 := by
    change deriv Complex.ofRealCLM x = _
    simp
  rw [h1]
  ring
  · change DifferentiableAt ℝ Complex.ofRealCLM x
    fun_prop
  · exact SchwartzMap.differentiableAt ψ

lemma positionOperatorSchwartz_momentumOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    = momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    + (Complex.I * ℏ) • ψ := by
  rw [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz]
  simp

lemma momentumOperatorSchwartz_positionOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - (Complex.I * ℏ) • ψ := by
  rw [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz]
  simp

end
end OneDimension
end QuantumMechanics
