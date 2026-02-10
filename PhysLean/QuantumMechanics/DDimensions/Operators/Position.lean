/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Position operators

In this module we define:
- The position operator on Schwartz maps, component-wise.
- The (regularized) radius operator on Schwartz maps.

-/

namespace QuantumMechanics
noncomputable section
open Space
open Function SchwartzMap ContDiff

/-
## Position vector operator
-/

/-- Component `i` of the position operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ coordCLM i)

@[inherit_doc positionOperator]
macro "𝐱[" i:term "]" : term => `(positionOperator $i)

lemma positionOperator_apply_fun (i : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = (fun x ↦ x i * ψ x) := by
  unfold positionOperator
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rw [Function.comp_apply, smul_eq_mul]
    rw [coordCLM_apply, coord_apply]
  · fun_prop

lemma positionOperator_apply (i : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐱[i] ψ x = x i * ψ x := by rw [positionOperator_apply_fun]

/-
## Radius operator
-/

/-- Power of regularized norm, `(‖x‖ ^ 2 + ε ^ 2) ^ (p / 2)` -/
private def normRegularizedPow (p : ℝ) (ε : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (p / 2)

private lemma normRegularizedPow_hasTemperateGrowth (hε : 0 < ε) :
    HasTemperateGrowth (normRegularizedPow (d := d) p ε) := by
  -- Write `normRegularizedPow` as the composition of three simple functions
  -- to take advantage of `hasTemperateGrowth_one_add_norm_sq_rpow`
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (p / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (p / 2)
  let f3 := fun (x : Space d) ↦ ε⁻¹ • x

  have h123 : normRegularizedPow (d := d) p ε = f1 ∘ f2 ∘ f3 := by
    unfold normRegularizedPow f1 f2 f3
    ext x
    simp only [Function.comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg _) ?_]
    · rw [mul_pow, mul_add, mul_one, ← mul_assoc, inv_pow, sq_abs]
      rw [IsUnit.mul_inv_cancel ?_]
      · rw [one_mul, add_comm]
      · rw [pow_two, isUnit_mul_self_iff, isUnit_iff_ne_zero]
        exact ne_of_gt hε
    · exact add_nonneg (zero_le_one' _) (sq_nonneg _)

  rw [h123]
  fun_prop

/-- The (regularized) radius operator to power `p` is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖²+ε²)^(p/2)•ψ`. -/
def radiusRegPowOperator (p : ℝ) (ε : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow p ε)

@[inherit_doc radiusRegPowOperator]
macro "𝐫[" p:term "," ε:term "]" : term => `(radiusRegPowOperator $p $ε)
macro "𝐫[" d:term ";" p:term "," ε:term "]" : term => `(radiusRegPowOperator (d := $d) $p $ε)

lemma radiusRegPowOperator_apply_fun (hε : 0 < ε) :
    𝐫[p,ε] ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (p / 2) • ψ x := by
  unfold radiusRegPowOperator
  ext x
  rw [smulLeftCLM_apply_apply]
  · unfold normRegularizedPow
    rw [comp_apply, smul_eq_mul, Complex.real_smul]
  · exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

lemma radiusRegPowOperator_apply (hε : 0 < ε) :
    𝐫[p,ε] ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (p / 2) • ψ x := by
  rw [radiusRegPowOperator_apply_fun hε]

lemma radiusPowOperator_comp_eq (p q : ℝ) (hε : 0 < ε) :
    𝐫[d;p,ε] ∘L 𝐫[q,ε] = 𝐫[p+q,ε] := by
  unfold radiusRegPowOperator
  ext ψ x
  simp only [ContinuousLinearMap.coe_comp', comp_apply]
  repeat rw [smulLeftCLM_apply_apply ?_]
  · unfold normRegularizedPow
    simp only [comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    rw [← Real.rpow_add]
    · congr
      ring
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  repeat exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

lemma radiusRegPowOperator_zero (hε : 0 < ε) :
    𝐫[0,ε] = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  rw [radiusRegPowOperator_apply, zero_div, Real.rpow_zero, one_smul]
  rfl
  exact hε

end
end QuantumMechanics
