/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
import PhysLean.QuantumMechanics.OneDimension.Operators.Unbounded
/-!

# Position operator

In this module we define:
- The position operator on functions `ℝ → ℂ`
- The position operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that position wavefunctions are generalized eigenvectors of the position operator.

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
def positionOperator : (ℝ → ℂ) →ₗ[ℂ] ℝ → ℂ where
  toFun ψ := fun x ↦ x * ψ x
  map_add' ψ1 ψ2 := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' a ψ1 := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
/-!

## The position operator on Schwartz maps

-/

private lemma norm_iteratedFDeriv_ofRealCLM {x} (i : ℕ) :
    ‖iteratedFDeriv ℝ i Complex.ofRealCLM x‖ = if i = 0 then |x| else if i = 1 then 1 else 0 := by
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
      simp only [Nat.succ_eq_add_one, ContinuousLinearMap.fderiv, Function.comp_apply,
        LinearIsometryEquiv.norm_map, Nat.add_eq_zero, one_ne_zero, and_false, and_self, ↓reduceIte,
        Nat.add_eq_right]
      rw [iteratedFDeriv_succ_eq_comp_right]
      conv_lhs =>
        enter [1, 2, 3, y]
        rw [fderiv_const_apply Complex.ofRealCLM]
      conv_lhs =>
        enter [1, 2]
        change iteratedFDeriv ℝ i 0
      simp only [Nat.succ_eq_add_one, Function.comp_apply, LinearIsometryEquiv.norm_map]
      have h1 : iteratedFDeriv ℝ i (0 : ℝ → ℝ →L[ℝ] ℝ →L[ℝ] ℂ) x = 0 := by
        change iteratedFDeriv ℝ i (fun x => 0) x = 0
        rw [iteratedFDeriv_zero_fun]
        rfl
      rw [h1]
      exact ContinuousMultilinearMap.opNorm_zero

open ContDiff

open SchwartzMap

/-- The parity operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => x * ψ x`. -/
def positionOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  refine mkCLM (fun ψ ↦ fun x => x * ψ x) ?_ ?_ ?_ ?_
  · intro ψ1 ψ2 x
    simp [mul_add]
  · intro c ψ x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  · intro ψ
    simp only
    apply ContDiff.mul
    · change ContDiff ℝ _ Complex.ofRealCLM
      fun_prop
    · exact SchwartzMap.smooth ψ ⊤
  · intro (k, n)
    use {(k, n - 1), (k + 1, n)}
    simp only [Real.norm_eq_abs, Finset.sup_insert, schwartzSeminormFamily_apply,
      Finset.sup_singleton, Seminorm.coe_sup, Pi.sup_apply]
    use n + 1
    refine ⟨by linarith, ?_⟩
    intro ψ x
    trans ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) *
      ‖iteratedFDeriv ℝ i (fun (x : ℝ) => (x : ℂ)) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (fun x => ψ x) x‖
    · apply mul_le_mul_of_nonneg'
      · exact Preorder.le_refl (‖x‖ ^ k)
      · apply norm_iteratedFDeriv_mul_le (N := ∞)
        · change ContDiff ℝ ∞ Complex.ofRealCLM
          fun_prop
        · exact SchwartzMap.smooth (ψ) ⊤
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
      simp only [Real.norm_eq_abs, zero_add, Finset.range_one, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul, Finset.sum_singleton, ↓reduceIte, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_zero, norm_iteratedFDeriv_zero, CharP.cast_eq_zero, ge_iff_le]
      trans (SchwartzMap.seminorm ℂ (k + 1) 0) ψ
      · apply le_trans ?_ (ψ.le_seminorm ℝ _ _ x)
        simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
        ring_nf
        rfl
      exact le_max_right ((SchwartzMap.seminorm ℂ k (0 - 1)) ψ)
        ((SchwartzMap.seminorm ℂ (k + 1) 0) ψ)
    | .succ n =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Real.norm_eq_abs, Nat.succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false,
        and_self, ↓reduceIte, Nat.add_eq_right, mul_zero, zero_mul, Finset.sum_const_zero,
        zero_add, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, mul_one, Nat.reduceAdd,
        Nat.add_one_sub_one, Nat.choose_zero_right, one_mul, Nat.sub_zero, ge_iff_le]
      trans (↑n + 1) * (|x| ^ k * ‖iteratedFDeriv ℝ n (fun x => (ψ) x) x‖)
            + (|x| ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) (fun x => (ψ) x) x‖)
      · apply le_of_eq
        ring
      trans (↑n + 1) * (SchwartzMap.seminorm ℂ k (n) ψ)
            + (SchwartzMap.seminorm ℂ (k + 1) (n + 1) ψ)
      · apply add_le_add _ _
        apply mul_le_mul_of_nonneg_left _
        refine Left.add_nonneg ?_ ?_
        · exact Nat.cast_nonneg' n
        · exact zero_le_one' ℝ
        · exact ψ.le_seminorm ℝ k n x
        · exact ψ.le_seminorm ℝ (k + 1) (n + 1) x
      · by_cases h1 :((SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ) <
          ((SchwartzMap.seminorm ℂ k n) ψ)
        · rw [max_eq_left_of_lt h1]
          trans (↑n + 1) * (SchwartzMap.seminorm ℂ k n) ψ + (SchwartzMap.seminorm ℂ k n) ψ
          apply add_le_add
          · simp
          · exact le_of_lt h1
          apply le_of_eq
          ring
        · simp at h1
          rw [max_eq_right h1]
          trans (↑n + 1) * (SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ +
            (SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ
          · apply add_le_add
            · apply mul_le_mul_of_nonneg_left _
              · linarith
              · exact h1
            · simp
          · apply le_of_eq
            ring

lemma positionOperatorSchwartz_apply_fun (ψ : 𝓢(ℝ, ℂ)) :
    (positionOperatorSchwartz ψ) = fun x => x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl

@[simp]
lemma positionOperatorSchwartz_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (positionOperatorSchwartz ψ) x = x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl

/-- The unbounded position operator, whose domain is Schwartz maps. -/
def positionOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM positionOperatorSchwartz

/-!

## Generalized eigenvectors of the momentum operator

-/

lemma positionStates_generalized_eigenvector_positionOperatorUnbounded (x : ℝ) :
    positionOperatorUnbounded.IsGeneralizedEigenvector (positionState x) x := by
  dsimp [positionOperatorUnbounded]
  rw [UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff]
  intro ψ
  simp [positionState_apply]

/-!

## Position operator is self adjoint

-/

lemma positionOperatorUnbounded_isSelfAdjoint :
    positionOperatorUnbounded.IsSelfAdjoint := by
  intro ψ1 ψ2
  dsimp [positionOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  congr
  funext x
  simp only [positionOperatorSchwartz_apply, map_mul, Complex.conj_ofReal]
  ring

end
end OneDimension
end QuantumMechanics
