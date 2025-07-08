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
open HilbertSpace

/-!

## Commutation relation betwen position and momentum operators

-/

lemma positionOperatorSchwartz_commutation_momentumOperatorSchwartz
    (ψ : schwartzSubmodule) : positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = (Complex.I * ℏ) • ψ := by
  apply schwartzSubmoduleEquiv.injective
  simp only [map_sub, map_smul]
  ext x
  simp [schwartzSubmoduleEquiv_momentumOperatorSchwartz_apply,
    schwartzSubmoduleEquiv_positionOperatorSchwartz]
  rw [deriv_fun_mul]
  have h1 : deriv Complex.ofReal x = 1 := by
    change deriv Complex.ofRealCLM x = _
    simp
  rw [h1]
  ring
  · change DifferentiableAt ℝ Complex.ofRealCLM x
    fun_prop
  · exact SchwartzMap.differentiableAt (schwartzSubmoduleEquiv ψ)

lemma positionOperatorSchwartz_momentumOperatorSchwartz_eq (ψ : schwartzSubmodule) :
    positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    = momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    + (Complex.I * ℏ) • ψ := by
  rw [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz]
  simp

lemma momentumOperatorSchwartz_positionOperatorSchwartz_eq (ψ : schwartzSubmodule) :
    momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - (Complex.I * ℏ) • ψ := by
  rw [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz]
  simp

end
end OneDimension
end QuantumMechanics
