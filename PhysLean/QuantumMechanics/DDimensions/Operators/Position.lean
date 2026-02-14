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

/-
Some helper lemmas for computing the iterated derivatives of `fun (x : Space d) ↦ (x i : ℂ)`,
generalized from `ℂ` to any `RCLike`.
-/

private lemma norm_fderiv_ofReal_coord {M} [RCLike M] {d : ℕ} {i : Fin d} {x : Space d}:
    ‖fderiv ℝ (RCLike.ofRealCLM (K := M) ∘L coordCLM i) x‖ = 1 := by
  rw [ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.norm_def]
  simp only [ContinuousLinearMap.coe_comp', RCLike.ofRealCLM_apply, Function.comp_apply,
    norm_algebraMap', Real.norm_eq_abs]
  conv_lhs =>
    enter [1, 1, c, 2, 2]
    rw [Space.coordCLM_apply, Space.coord_apply]

  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_
  · use 1
    simp only [Set.mem_setOf_eq, zero_le_one, one_mul, true_and]
    exact fun x => abs_eval_le_norm x i
  · intro c
    rw [Set.mem_setOf_eq, and_imp]
    intro hc h
    have h' : ∃ (x : Space d), |x i| = ‖x‖ ∧ 0 < |x i| := by
      use (basis i)
      rw [basis_self, abs_one, OrthonormalBasis.norm_eq_one]
      simp only [zero_lt_one, and_self]
    rcases h' with ⟨x2, hx2, hx2'⟩
    apply one_le_of_le_mul_right₀ hx2'
    apply le_of_le_of_eq (h x2) (congrArg (HMul.hMul c) (Eq.symm hx2))
  · intro w hw
    use 1
    simp only [Set.mem_setOf_eq, zero_le_one, one_mul, true_and]
    exact ⟨fun x => abs_eval_le_norm x i, hw⟩

private lemma iteratedFDeriv_succ_succ_ofReal_coord_eq_zero {M} [RCLike M] {d : ℕ} {i : Fin d} :
    ∀ n : ℕ, iteratedFDeriv ℝ n.succ.succ (RCLike.ofRealCLM (K := M) ∘L coordCLM i) = 0 := by
  intro n
  induction n with
  | zero =>
    ext x _
    rw [iteratedFDeriv_succ_apply_right]
    conv_lhs =>
      enter [1, 1, 3, y]
      change fderiv ℝ (RCLike.ofRealCLM ∘L coordCLM i) y
      rw [ContinuousLinearMap.fderiv]
    simp only [Nat.reduceAdd, iteratedFDeriv_one_apply, fderiv_fun_const, Pi.zero_apply,
      Fin.isValue, ContinuousLinearMap.zero_apply, Fin.reduceLast, Nat.succ_eq_add_one,
      ContinuousMultilinearMap.zero_apply]
  | succ n hn =>
    ext x _
    rw [iteratedFDeriv_succ_apply_left]
    rw [hn]
    simp only [fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      ContinuousMultilinearMap.zero_apply, Nat.succ_eq_add_one]

private lemma norm_iteratedFDeriv_ofRealCLM_coord {M} [RCLike M] (n : ℕ) {d : ℕ} (i : Fin d)
    (x : Space d) : ‖iteratedFDeriv ℝ n (RCLike.ofRealCLM (K := M) ∘L coordCLM i) x‖ =
    if n = 0 then |x i| else if n = 1 then 1 else 0 := by
  match n with
  | 0 =>
    simp only [ContinuousLinearMap.coe_comp', RCLike.ofRealCLM_apply, norm_iteratedFDeriv_zero,
      Function.comp_apply, norm_algebraMap', Real.norm_eq_abs, ↓reduceIte]
    rw [coordCLM_apply, coord_apply]
  | 1 =>
    simp only [ContinuousLinearMap.coe_comp', one_ne_zero, ↓reduceIte]
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
    exact norm_fderiv_ofReal_coord
  | .succ (.succ n) =>
    rw [iteratedFDeriv_succ_succ_ofReal_coord_eq_zero]
    simp only [Nat.succ_eq_add_one, Pi.zero_apply, norm_zero, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, and_self, ↓reduceIte, Nat.add_eq_right]

/-- Component `i` of the position operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator {d : ℕ} (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := by
  refine SchwartzMap.mkCLM (fun ψ x ↦ x i * ψ x) ?hadd ?hsmul ?hsmooth ?hbound
  -- hadd
  · intro ψ1 ψ2 x
    simp only [SchwartzMap.add_apply]
    ring

  -- hsmul
  · intro c ψ x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

  -- hsmooth
  · intro ψ
    exact ContDiff.smul (eval_contDiff i) (smooth ψ ⊤)

  -- hbound
  · intro (k, n)
    use {(k, n - 1), (k + 1, n)}
    use n + 1
    refine ⟨by linarith, ?_⟩
    intro ψ x
    simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
      Seminorm.coe_sup, Pi.sup_apply]

    trans ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1), (n.choose j)
      * ‖iteratedFDeriv ℝ j (fun x ↦ (x i : ℂ)) x‖
      * ‖iteratedFDeriv ℝ (n - j) ψ x‖
    · apply (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg x) k))
      have hcd : ContDiff ℝ ∞ (fun (x : Space d) ↦ (x i : ℂ)) := by
        apply ContDiff.fun_comp
        · change ContDiff ℝ ∞ RCLike.ofRealCLM
          fun_prop
        · fun_prop
      apply norm_iteratedFDeriv_mul_le (N := ∞) hcd (SchwartzMap.smooth ψ ⊤) x ENat.LEInfty.out

    have h' : (fun x ↦ ↑(x i)) = RCLike.ofRealCLM (K := ℂ) ∘L coordCLM i := by
      ext x
      simp only [ContinuousLinearMap.coe_comp', RCLike.ofRealCLM_apply, Complex.coe_algebraMap,
        Function.comp_apply, Complex.ofReal_inj]
      rw [Space.coordCLM_apply, Space.coord_apply]
    rw [h']
    conv_lhs =>
      enter [2, 2, j]
      rw [norm_iteratedFDeriv_ofRealCLM_coord]

    match n with
      | 0 =>
        simp only [zero_add, Finset.range_one, mul_ite, mul_one, mul_zero,
          ite_mul, zero_mul, Finset.sum_singleton, ↓reduceIte, Nat.choose_self, Nat.cast_one,
          one_mul, Nat.sub_zero, norm_iteratedFDeriv_zero, CharP.cast_eq_zero]
        trans (SchwartzMap.seminorm ℝ (k + 1) 0) ψ
        · apply le_trans ?_ (ψ.le_seminorm _ _ _ x)
          rw [norm_iteratedFDeriv_zero, ← mul_assoc, pow_add]
          apply (mul_le_mul_of_nonneg_right ?_ (norm_nonneg (ψ x)))
          apply (mul_le_mul_of_nonneg_left ?_ ?_)
          · simp only [pow_one, abs_eval_le_norm]
          · apply pow_nonneg (norm_nonneg _)
        · exact le_max_right _ _
      | .succ n =>
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self,
          ↓reduceIte, Nat.add_eq_right, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
          Nat.choose_one_right, Nat.cast_add, Nat.cast_one, mul_one, Nat.reduceAdd,
          Nat.add_one_sub_one, Nat.choose_zero_right, one_mul, Nat.sub_zero,
          add_tsub_cancel_right, ge_iff_le]

        trans (↑n + 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n ψ x‖)
          + (‖x‖ ^ k * |x i| * ‖iteratedFDeriv ℝ (n + 1) ψ x‖)
        · apply le_of_eq
          ring

        trans (↑n + 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n ψ x‖)
          + (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) ψ x‖)
        · apply add_le_add_right
          apply mul_le_mul_of_nonneg_right
          · rw [pow_add, pow_one]
            apply mul_le_mul_of_nonneg_left
            · exact abs_eval_le_norm x i
            · exact pow_nonneg (norm_nonneg x) k
          · exact ContinuousMultilinearMap.opNorm_nonneg _

        trans (↑n + 1) * (SchwartzMap.seminorm ℂ k (n) ψ)
          + (SchwartzMap.seminorm ℂ (k + 1) (n + 1) ψ)
        · apply add_le_add _ (ψ.le_seminorm _ _ _ _)
          apply mul_le_mul_of_nonneg_left (ψ.le_seminorm _ _ _ _)
          exact Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)

        by_cases h : (SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ < (SchwartzMap.seminorm ℂ k n) ψ
        · rw [max_eq_left_of_lt h]
          trans (↑n + 1) * (SchwartzMap.seminorm ℂ k n) ψ + (SchwartzMap.seminorm ℂ k n) ψ
          · apply (add_le_add (by linarith) (le_of_lt h))
          apply le_of_eq
          ring
        · rw [not_lt] at h
          rw [max_eq_right h]
          trans (↑n + 1) * (SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ
            + (SchwartzMap.seminorm ℂ (k + 1) (n + 1)) ψ
          · apply (add_le_add ?_ (Std.IsPreorder.le_refl _))
            apply mul_le_mul_of_nonneg_left h
            linarith
          apply le_of_eq
          ring

@[inherit_doc positionOperator]
macro "𝐱[" i:term "]" : term => `(positionOperator $i)

lemma positionOperator_apply_fun {d : ℕ} (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = (fun x ↦ x i * ψ x) := rfl

lemma positionOperator_apply {d : ℕ} (i : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐱[i] ψ x = x i * ψ x := rfl

end
end QuantumMechanics
