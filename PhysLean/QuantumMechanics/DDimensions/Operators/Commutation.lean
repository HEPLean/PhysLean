/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.Position
import PhysLean.QuantumMechanics.DDimensions.Operators.Momentum
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
/-!

# Commutation relations


-/



namespace QuantumMechanics
noncomputable section
open Constants
open SchwartzMap



/-
## Position / position commutators
-/


/-- `[xᵢ, xⱼ] = 0` -/
lemma position_commutation_position {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_mul, Pi.sub_apply, sub_apply,
    Function.comp_apply, ContinuousLinearMap.zero_apply, zero_apply, positionOperator_apply]
  ring



/-
## Momentum / momentum commutators
-/


/-- `[pᵢ, pⱼ] = 0` -/
@[sorryful]
lemma momentum_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  sorry


lemma momentum_momentum_eq {d : ℕ} (i j : Fin d) : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [← sub_eq_zero]
  exact momentum_commutation_momentum i j


/-- `[𝐩², 𝐩ᵢ] = 0` -/
lemma momentumSqr_commutation_momentum {d : ℕ} (i : Fin d) : 𝐩² ∘L 𝐩[i] - 𝐩[i] ∘L 𝐩² = 0 := by
  dsimp only [momentumOperatorSqr]
  simp only [ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum]
  rw [sub_eq_zero]
  congr
  ext j ψ x
  rw [ContinuousLinearMap.comp_assoc]
  rw [momentum_momentum_eq]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [momentum_momentum_eq]
  rfl



/-
## Position / momentum commutators
-/


/-- `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙` -/
@[sorryful]
lemma position_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐩[j]⁆ =
    (Complex.I * ℏ) • (if i = j then 1 else 0) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  sorry



/-
## Angular momentum / position commutators
-/

@[sorryful]
lemma angularMomentum_commutation_position {d : ℕ} (i j k : Fin d) :
    ⁅𝐋[i,j], 𝐱[k]⁆ = (Complex.I * ℏ) • (
      (if i = k then 1 else 0) * 𝐱[j] - (if j = k then 1 else 0) * 𝐱[i]
    ) := by
  sorry


@[sorryful]
lemma angularMomentumSqr_commutation_position {d : ℕ} (i : Fin d) :
    𝐋² ∘L 𝐱[i] - 𝐱[i] ∘L 𝐋² = 0 := by
  sorry




/-
## Angular momentum / momentum commutators
-/

@[sorryful]
lemma angularMomentum_commutation_momentum {d : ℕ} (i j k : Fin d) :
    ⁅𝐋[i,j], 𝐩[k]⁆ = (Complex.I * ℏ) • (
      (if i = k then 1 else 0) * 𝐩[j] - (if j = k then 1 else 0) * 𝐩[i]
    ) := by
  sorry



/-
## Angular momentum / angular momentum commutators
-/

@[sorryful]
lemma angularMomentum_commutation_angularMomentum {d : ℕ} (i j k l : Fin d) :
    ⁅𝐋[i,j], 𝐋[k,l]⁆ = (Complex.I * ℏ) • (
        (if i = k then 1 else 0) * 𝐋[j,l]
      - (if i = l then 1 else 0) * 𝐋[j,k]
      - (if j = k then 1 else 0) * 𝐋[i,l]
      + (if j = l then 1 else 0) * 𝐋[i,k]
    ) := by
  sorry


@[sorryful]
lemma angularMomentumSqr_commutation_angularMomentum {d : ℕ} (i j : Fin d) :
    𝐋² ∘L 𝐋[i,j] - 𝐋[i,j] ∘L 𝐋² = 0 := by
  sorry




end
end QuantumMechanics
