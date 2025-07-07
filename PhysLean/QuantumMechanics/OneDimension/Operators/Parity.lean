/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
/-!

# Parity operator

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section

namespace HilbertSpace
open MeasureTheory

/-!

## The parity operator on functions

-/

/-- The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that
  `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperator : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun ψ := fun x => ψ (-x)
  map_add' ψ1 ψ2 := by
    funext x
    simp
  map_smul' a ψ1 := by
    funext x
    simp

/-!

## The parity operator on Schwartz maps

-/

/-- The parity operator on the Schwartz submodule is defined as the linear map from
  `schwartzSubmodule` to itself, such that `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperatorSchwartz : schwartzSubmodule →ₗ[ℂ] schwartzSubmodule := by
  refine schwartzSubmoduleEquiv.symm.toLinearMap ∘ₗ
    (SchwartzMap.compCLM ℂ (g := (fun x => - x : ℝ → ℝ)) ⟨?_, ?_⟩ ?_).toLinearMap ∘ₗ
    schwartzSubmoduleEquiv.toLinearMap
  · fun_prop
  · intro n
    simp
    use 1, 1
    intro x
    simp
    erw [iteratedFDeriv_neg_apply]
    simp
    match n with
    | 0 => simp
    | 1 =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
    | .succ (.succ n) =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
      rw [iteratedFDeriv_const_of_ne]
      simp
      apply add_nonneg
      · exact zero_le_one' ℝ
      · exact abs_nonneg x
      simp
  · simp
    use 1, 1
    intro x
    simp

/-- The unbounded parity operator, whose domain is Schwartz maps. -/
def parityOperatorUnbounded : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := schwartzSubmodule
  toFun := SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume ∘ₗ
    schwartzSubmoduleEquiv.toLinearMap ∘ₗ parityOperatorSchwartz

lemma parityOperatorUnbounded_mem_schwartzSubmodule (ψ : schwartzSubmodule) :
    parityOperatorUnbounded ψ ∈ schwartzSubmodule := by
  simp [parityOperatorUnbounded]

lemma parityOperatorUnbounded_apply_eq_parityOperatorUnbounded (ψ : schwartzSubmodule) :
    parityOperatorSchwartz ψ = ⟨parityOperatorUnbounded ψ,
      parityOperatorUnbounded_mem_schwartzSubmodule ψ⟩ := by
  ext1
  change _ = (schwartzSubmoduleEquiv.symm (schwartzSubmoduleEquiv (parityOperatorSchwartz ψ))).1
  simp

end HilbertSpace
end
end OneDimension
end QuantumMechanics
