/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.Mathematics.KroneckerDelta
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
/-!

# Commutation relations

-/

namespace QuantumMechanics
noncomputable section
open Constants
open KroneckerDelta
open SchwartzMap ContinuousLinearMap

private lemma ite_cond_symm (i j : Fin d) :
    (if i = j then A else B) = (if j = i then A else B) :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

lemma lie_leibniz_left {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel]

lemma lie_leibniz_right {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A, B ∘L C⁆ = B ∘L ⁅A, C⁆ + ⁅A, B⁆ ∘L C := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel']

/-
## Position / position commutators
-/

/-- Position operators commute: `[xᵢ, xⱼ] = 0`. -/
lemma position_commutation_position {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply, positionOperator_apply]
  ring

/-
## Momentum / momentum commutators
-/

/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
lemma momentum_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply, momentumOperator_apply_fun]
  rw [Space.deriv_const_smul _ ?_, Space.deriv_const_smul _ ?_]
  · rw [Space.deriv_commute _ (ψ.smooth _), sub_self]
  · exact Space.deriv_differentiable (ψ.smooth _) i
  · exact Space.deriv_differentiable (ψ.smooth _) j

lemma momentum_momentum_eq {d : ℕ} (i j : Fin d) : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [← sub_eq_zero]
  exact momentum_commutation_momentum i j

lemma momentumSqr_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅momentumOperatorSqr (d := d), 𝐩[i]⁆ = 0 := by
  dsimp only [Bracket.bracket, momentumOperatorSqr]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  conv_lhs =>
    enter [2, j]
    simp only [ContinuousLinearMap.mul_def]
    rw [comp_assoc]
    rw [momentum_momentum_eq j i, ← comp_assoc]
    rw [momentum_momentum_eq j i, comp_assoc]
    rw [sub_self]
  rw [Finset.sum_const_zero]

/-
## Position / momentum commutators
-/

/-- The canonical commutation relations: `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙`. -/
lemma position_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐩[j]⁆ =
    (Complex.I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  dsimp only [Bracket.bracket, kronecker_delta]
  ext ψ x
  simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, coe_id', id_eq, smul_eq_mul,
    coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply]
  rw [positionOperator_apply, momentumOperator_apply_fun]
  rw [momentumOperator_apply, positionOperator_apply]
  simp only [neg_mul, Pi.smul_apply, smul_eq_mul, mul_neg, sub_neg_eq_add]

  have h : (fun x ↦ ↑(x i) * ψ x) = (fun (x : Space d) ↦ x i) • ψ := rfl
  rw [h]
  rw [Space.deriv_smul (by fun_prop) (SchwartzMap.differentiableAt ψ)]
  rw [Space.deriv_component, ite_cond_symm j i]
  simp only [mul_add, Complex.real_smul, ite_smul, one_smul, zero_smul, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  ring

lemma position_position_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i] ∘L 𝐱[j], 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐱[j] + (Complex.I * ℏ * δ[j,k]) • 𝐱[i] := by
  rw [lie_leibniz_left]
  rw [position_commutation_momentum, position_commutation_momentum]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [id_comp, comp_id]
  rw [add_comm]

lemma position_commutation_momentum_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i], 𝐩[j] ∘L 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐩[j] + (Complex.I * ℏ * δ[i,j]) • 𝐩[k] := by
  rw [lie_leibniz_right]
  rw [position_commutation_momentum, position_commutation_momentum]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [id_comp, comp_id]

lemma position_commutation_momentumSqr {d : ℕ} (i : Fin d) : ⁅𝐱[i], 𝐩²⁆ =
    (2 * Complex.I * ℏ) • 𝐩[i] := by
  unfold momentumOperatorSqr
  rw [lie_sum]
  simp only [position_commutation_momentum_momentum]
  dsimp only [kronecker_delta]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-
## Angular momentum / position commutators
-/

lemma angularMomentum_commutation_position {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐱[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐱[j] - (Complex.I * ℏ * δ[j,k]) • 𝐱[i] := by
  unfold angularMomentumOperator
  rw [sub_lie]
  rw [lie_leibniz_left, lie_leibniz_left]
  rw [position_commutation_position, position_commutation_position]
  rw [← lie_skew, position_commutation_momentum]
  rw [← lie_skew, position_commutation_momentum]
  dsimp only [kronecker_delta]
  rw [ite_cond_symm k i, ite_cond_symm k j]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smul, comp_id, zero_comp,
    add_zero, add_comm, sub_neg_eq_add, ← sub_eq_add_neg]

/-
## Angular momentum / momentum commutators
-/

lemma angularMomentum_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐩[j] - (Complex.I * ℏ * δ[j,k]) • 𝐩[i] := by
  unfold angularMomentumOperator
  rw [sub_lie]
  rw [lie_leibniz_left, lie_leibniz_left]
  rw [momentum_commutation_momentum, momentum_commutation_momentum]
  rw [position_commutation_momentum, position_commutation_momentum]
  simp only [ContinuousLinearMap.smul_comp, id_comp, comp_zero, zero_add]

lemma angularMomentum_commutation_momentumSqr {d : ℕ} (i j : Fin d) :
    ⁅𝐋[i,j], momentumOperatorSqr (d := d)⁆ = 0 := by
  unfold momentumOperatorSqr
  conv_lhs =>
    rw [lie_sum]
    enter [2, k]
    rw [lie_leibniz_right]
    rw [angularMomentum_commutation_momentum]
    simp only [comp_sub, comp_smulₛₗ, RingHom.id_apply, sub_comp, smul_comp]
    rw [momentum_momentum_eq _ i, momentum_momentum_eq j _]
  dsimp only [kronecker_delta]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self, add_zero]

lemma angularMomentumSqr_commutation_momentumSqr {d : ℕ} :
    ⁅angularMomentumOperatorSqr (d := d), momentumOperatorSqr (d := d)⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  conv_lhs =>
    rw [sum_lie]
    enter [2, i]
    rw [sum_lie]
    enter [2, j]
    rw [smul_lie, lie_leibniz_left]
    rw [angularMomentum_commutation_momentumSqr]
    rw [comp_zero, zero_comp, add_zero, smul_zero]
  simp only [Finset.sum_const_zero]

/-
## Angular momentum / angular momentum commutators
-/

lemma angularMomentum_commutation_angularMomentum {d : ℕ} (i j k l : Fin d) : ⁅𝐋[i,j], 𝐋[k,l]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐋[j,l] - (Complex.I * ℏ * δ[i,l]) • 𝐋[j,k]
    - (Complex.I * ℏ * δ[j,k]) • 𝐋[i,l] + (Complex.I * ℏ * δ[j,l]) • 𝐋[i,k] := by
  nth_rw 2 [angularMomentumOperator]
  rw [lie_sub]
  rw [lie_leibniz_right, lie_leibniz_right]
  rw [angularMomentum_commutation_momentum, angularMomentum_commutation_position]
  rw [angularMomentum_commutation_momentum, angularMomentum_commutation_position]
  dsimp only [angularMomentumOperator, kronecker_delta]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  ext ψ x
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, coe_sub', Pi.sub_apply,
    ContinuousLinearMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.add_apply, smul_sub]
  ring

lemma angularMomentumSqr_commutation_angularMomentum {d : ℕ} (i j : Fin d) :
    ⁅angularMomentumOperatorSqr (d := d), 𝐋[i,j]⁆ = 0 := by
  unfold angularMomentumOperatorSqr
  conv_lhs =>
    rw [sum_lie]
    enter [2, k]
    rw [sum_lie]
    enter [2, l]
    simp only [smul_lie]
    rw [lie_leibniz_left]
    rw [angularMomentum_commutation_angularMomentum]
  dsimp only [kronecker_delta]
  simp only [comp_add, comp_sub, add_comp, sub_comp, comp_smul, smul_comp, smul_add, smul_sub,
    smul_smul, mul_ite, mul_zero, mul_one, ← mul_assoc]
  simp only [ite_smul, zero_smul]

  -- Split into individual terms to do one of the sums, then recombine
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

  ext ψ x
  simp only [angularMomentumOperator_antisymm _ i, angularMomentumOperator_antisymm j _,
    neg_comp, comp_neg, neg_neg, smul_neg, sub_neg_eq_add]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, SchwartzMap.add_apply,
    SchwartzMap.sum_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.neg_apply,
    SchwartzMap.zero_apply]
  ring_nf
  exact Fintype.sum_eq_zero _ (congrFun rfl)

end
end QuantumMechanics
