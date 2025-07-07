/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Meta.TODO.Basic
/-!

# Position operator

In this module we define:
- The momentum operator on functions `ℝ → ℂ`
- The momentum operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that plane waves are generalized eigenvectors of the momentum operator.

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace

/-!

## The position operator on functions `ℝ → ℂ`

-/

/-- The position operator is defined as the linear map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `x * ψ`. -/
def positionOperator :  (ℝ → ℂ) →ₗ[ℂ] ℝ → ℂ where
  toFun ψ := fun x ↦ x * ψ x
  map_add' ψ1 ψ2 := by
    funext x
    simp
    ring
  map_smul' a ψ1 := by
    funext x
    simp
    ring
/-!

## The position operator on Schwartz maps

-/

private lemma norm_iteratedFDeriv_ofRealCLM {x} (i : ℕ) :
   ‖iteratedFDeriv ℝ i Complex.ofRealCLM x‖ = if i = 0 then |x| else if i = 1 then 1 else 0  := by
  match i with
  | 0 =>
    simp [iteratedFDeriv_zero_eq_comp]
  | .succ i =>
    induction i with
    | zero =>
      simp [iteratedFDeriv_succ_eq_comp_right]
      rw [@ContinuousLinearMap.norm_def]
      apply ContinuousLinearMap.opNorm_eq_of_bounds
      · simp
      · intro x
        simp
      · intro N hN h
        simpa using h 1
    | succ i ih =>

      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
      rw [iteratedFDeriv_succ_eq_comp_right]

      conv_lhs =>
        enter [1, 2, 3, y]
        rw [fderiv_const_apply Complex.ofRealCLM]
      conv_lhs =>
        enter [1, 2]
        change iteratedFDeriv ℝ i 0
      simp
      have h1 : iteratedFDeriv ℝ i (0 : ℝ → ℝ →L[ℝ] ℝ →L[ℝ] ℂ) x = 0 := by
        change iteratedFDeriv ℝ i (fun x => 0) x = 0
        rw [iteratedFDeriv_zero_fun ]
        rfl
      rw [h1]
      exact ContinuousMultilinearMap.opNorm_zero

open ContDiff

/-- The position operator on the Schwartz submodule is defined as the linear map from
  `schwartzSubmodule` to itself, such that `ψ` is taken to `fun x => x * ψ (x)`. -/
def positionOperatorSchwartz : schwartzSubmodule →ₗ[ℂ] schwartzSubmodule where
  toFun ψ := schwartzSubmoduleEquiv.symm ⟨fun x => x * (schwartzSubmoduleEquiv ψ x),
      by
        apply ContDiff.mul
        · change ContDiff ℝ _ Complex.ofRealCLM
          fun_prop
        · exact SchwartzMap.smooth (schwartzSubmoduleEquiv ψ) ⊤
        , by
        intro k n
        obtain ⟨C1, hC1⟩ := (schwartzSubmoduleEquiv ψ).decay' k (n - 1)
        obtain ⟨C2, hC2⟩ := (schwartzSubmoduleEquiv ψ).decay' (k + 1) n
        use  n * C1 + C2
        intro x
        trans ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) * ‖iteratedFDeriv ℝ i (fun (x : ℝ) => (x : ℂ)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun x => schwartzSubmoduleEquiv ψ x) x‖
        apply mul_le_mul_of_nonneg'
        · exact Preorder.le_refl (‖x‖ ^ k)
        · apply norm_iteratedFDeriv_mul_le  (N := ∞)
          · change ContDiff ℝ ∞ Complex.ofRealCLM
            fun_prop
          · exact SchwartzMap.smooth (schwartzSubmoduleEquiv ψ) ⊤
          · exact right_eq_inf.mp rfl
        · exact ContinuousMultilinearMap.opNorm_nonneg _
        · refine pow_nonneg ?_ k
          exact norm_nonneg x
        conv_lhs =>
          enter [2, 2, i, 1, 2]
          change ‖iteratedFDeriv ℝ i Complex.ofRealCLM x‖
          rw [norm_iteratedFDeriv_ofRealCLM i]
        match n with
        | 0 =>
          simp
          have hC3x := hC2 x
          simp at hC3x
          refine le_trans ?_ hC3x
          apply le_of_eq
          ring_nf
          rfl
        | .succ n =>
          rw [Finset.sum_range_succ', Finset.sum_range_succ']
          simp
          trans (↑n + 1) * (|x| ^ k * ‖iteratedFDeriv ℝ n (fun x => (schwartzSubmoduleEquiv ψ) x) x‖)
            + (|x| ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) (fun x => (schwartzSubmoduleEquiv ψ) x) x‖)
          · apply le_of_eq
            ring
          apply add_le_add _ (hC2 x)
          apply mul_le_mul_of_nonneg_left (hC1 x)
          refine Left.add_nonneg ?_ ?_
          · exact Nat.cast_nonneg' n
          · exact zero_le_one' ℝ⟩
  map_add' ψ1 ψ2 := by
    simp [mul_add]
    rfl
  map_smul' a ψ := by
    simp only [neg_mul, map_smul, neg_smul, RingHom.id_apply]
    conv_lhs =>
      enter [2, 1, x]
      change  ↑x • a • ( schwartzSubmoduleEquiv ψ) x
      rw [smul_comm]
    rfl

/-- The unbounded position operator, whose domain is Schwartz maps. -/
def positionOperatorUnbounded : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := schwartzSubmodule
  toFun := SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume ∘ₗ
    schwartzSubmoduleEquiv.toLinearMap ∘ₗ positionOperatorSchwartz

lemma positionOperatorUnbounded_mem_schwartzSubmodule (ψ : schwartzSubmodule) :
    positionOperatorUnbounded ψ ∈ schwartzSubmodule := by
  simp [positionOperatorUnbounded]

lemma positionOperatorSchwartz_apply_eq_positionOperatorUnbounded (ψ : schwartzSubmodule) :
    positionOperatorSchwartz ψ = ⟨positionOperatorUnbounded ψ,
      positionOperatorUnbounded_mem_schwartzSubmodule ψ⟩ := by
  ext1
  change _ = (schwartzSubmoduleEquiv.symm (schwartzSubmoduleEquiv (positionOperatorSchwartz ψ))).1
  simp

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma positionStates_generalized_eigenvector_positionOperatorSchwartz
    (x : ℝ) (ψ : schwartzSubmodule) :
    positionState x (positionOperatorSchwartz ψ) = x * positionState x ψ := by
  simp only [positionOperatorSchwartz, LinearPMap.mk_apply, LinearMap.coe_mk, AddHom.coe_mk,
    positionState_apply]
  change (schwartzSubmoduleEquiv (schwartzSubmoduleEquiv.symm _)) x = _
  simp only [LinearEquiv.apply_symm_apply]
  rfl

end
end OneDimension
end QuantumMechanics
