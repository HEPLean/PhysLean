/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Meta.TODO.Basic
/-!

# Momentum operator

In this module we define the momentum operator as an `LinearPMap`
from the Hilbert space of square integrable functions to itself.
This corresponds to `momentumOperatorLinearPMap`.

We also define the momentum operator on functions `ℝ → ℂ`,
which is `momentumOperator`.
-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace

/-- The domain of the momentum operator is square integrable functions
  which are differentiable and which have a square integrable derivative. -/
def momentumOperatorLinearPMap.domain' : Submodule ℂ HilbertSpace where
  carrier ψ := ∃ ψ', ψ =ᵐ[MeasureTheory.volume] ψ' ∧
    Differentiable ℝ ψ' ∧ MemHS (fun x => - Complex.I * ℏ * deriv ψ' x)
  zero_mem' := by
    use 0
    apply And.intro
    · exact MeasureTheory.Lp.coeFn_zero ℂ 2 MeasureTheory.volume
    · simp
  add_mem' {ψ1 ψ2} h1 h2:= by
    obtain ⟨ψ1', h1', h1diff, h1hs⟩ := h1
    obtain ⟨ψ2', h2', h2diff, h2hs⟩ := h2
    use ψ1' + ψ2'
    refine ⟨?_, ?_, ?_⟩
    · trans ψ1.1 + ψ2.1
      · apply MeasureTheory.AEEqFun.coeFn_add
      · apply Filter.EventuallyEq.add
        · exact h1'
        · exact h2'
    · fun_prop
    · have h1 : (fun x => -Complex.I * ↑↑ℏ * deriv (ψ1' + ψ2') x)
          = fun x => -Complex.I * ↑↑ℏ * deriv (ψ1') x + (-Complex.I * ↑↑ℏ * deriv (ψ2') x) := by
        funext x
        simp only [neg_mul]
        rw [deriv_add]
        · ring
        · exact h1diff x
        · exact h2diff x
      rw [h1]
      exact memHS_add h1hs h2hs
  smul_mem' c ψ h := by
    obtain ⟨ψ', h', hdiff, hhs⟩ := h
    use c • ψ'
    refine ⟨?_, ?_, ?_⟩
    · trans c • ψ
      · apply MeasureTheory.AEEqFun.coeFn_smul
      · change (fun x => c • ψ x) =ᵐ[MeasureTheory.volume] fun x => c • ψ' x
        exact Filter.EventuallyEq.const_smul h' c
    · fun_prop
    · have h1 : (fun x => -Complex.I * ↑↑ℏ * deriv (c • ψ') x)
          = c • fun x => (-Complex.I * ↑↑ℏ * deriv ψ' x) := by
        funext x
        rw [deriv_const_smul]
        · simp
          ring
        · fun_prop
      rw [h1]
      exact memHS_smul hhs

/-- The momentum operator as a linear map from it's domain to the Hilbert space. -/
def momentumOperatorLinearPMap.toFun' :
    momentumOperatorLinearPMap.domain' →ₗ[ℂ] HilbertSpace where
  toFun := fun ψ => HilbertSpace.mk (Classical.choose_spec ψ.2).2.2
  map_add' ψ1 ψ2 := by
    rw [← mk_add, mk_eq_iff]
    trans (fun x => (-Complex.I * ↑↑ℏ) • (fun x => deriv (Classical.choose (ψ1 + ψ2).2) x) x)
    · simp
    symm
    trans (fun x => (-Complex.I * ↑↑ℏ) • (fun x =>
      deriv (Classical.choose ψ1.2) x + deriv (Classical.choose ψ2.2) x) x)
    · apply Eq.eventuallyEq
      funext x
      simp only [neg_mul, Pi.add_apply, smul_eq_mul]
      ring
    apply Filter.EventuallyEq.const_smul
    trans (fun x => deriv (Classical.choose ψ1.2 + Classical.choose ψ2.2) x)
    · apply Eq.eventuallyEq
      funext x
      simp only [neg_mul]
      have h1 : deriv (Classical.choose ψ1.2) x + deriv (Classical.choose ψ2.2) x
          = deriv (Classical.choose ψ1.2 + Classical.choose ψ2.2) x := by
        rw [deriv_add]
        · exact (Classical.choose_spec ψ1.2).2.1 x
        · exact (Classical.choose_spec ψ2.2).2.1 x
      trans deriv (Classical.choose ψ1.2) x + deriv (Classical.choose ψ2.2) x
      · simp
      rw [h1]
      simp
    apply Eq.eventuallyEq
    funext x
    rw [← fderiv_deriv, ← fderiv_deriv]
    congr 1
    apply Filter.EventuallyEq.fderiv_eq
    refine Filter.EventuallyEq.symm (Eq.eventuallyEq ?_)
    refine (Continuous.ae_eq_iff_eq MeasureTheory.volume ?_ ?_).mp ?_
    · apply (Classical.choose_spec (ψ1 + ψ2).2).2.1.continuous
    · have h1 := (Classical.choose_spec ψ1.2).2.1.continuous
      have h2 := (Classical.choose_spec ψ2.2).2.1.continuous
      exact Continuous.add h1 h2
    trans (ψ1 + ψ2)
    swap
    · apply Filter.EventuallyEq.add
      · exact (Classical.choose_spec ψ1.2).1
      · exact (Classical.choose_spec ψ2.2).1
    refine (Classical.choose_spec (ψ1 + ψ2).2).1.symm.trans ?_
    apply (MeasureTheory.AEEqFun.coeFn_add)
  map_smul' c ψ := by
    rw [← mk_smul, mk_eq_iff]
    apply Filter.EventuallyEq.symm (Eq.eventuallyEq ?_)
    funext x
    simp only [RingHom.id_apply, neg_mul, Pi.smul_apply, smul_eq_mul, mul_neg, SetLike.val_smul,
      neg_inj]
    trans (Complex.I * ↑↑ℏ * (c • deriv (Classical.choose ψ.2) x))
    · simp
      ring
    trans (Complex.I * ↑↑ℏ * (deriv (Classical.choose (c • ψ).2) x))
    swap
    · simp
    congr
    rw [← deriv_const_smul c ((Classical.choose_spec ψ.2).2.1 x)]
    congr
    refine (Continuous.ae_eq_iff_eq MeasureTheory.volume ?_ ?_).mp ?_
    · have h1 := (Classical.choose_spec ψ.2).2.1.continuous
      exact Continuous.const_smul h1 c
    · exact (Classical.choose_spec (c • ψ).2).2.1.continuous
    trans c • ψ
    · change (fun x => c • Classical.choose ψ.2 x) =ᵐ[MeasureTheory.volume] fun x => c • ψ.1 x
      apply Filter.EventuallyEq.const_smul
      exact (Classical.choose_spec ψ.2).1.symm
    symm
    apply (Classical.choose_spec (c • ψ).2).1.symm.trans
    simp only [SetLike.val_smul]
    apply MeasureTheory.AEEqFun.coeFn_smul

/-- The unbounded momentum operator, whose domain is square integrable functions
  which are differentiable and which have a square integrable derivative. -/
def momentumOperatorLinearPMap : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := momentumOperatorLinearPMap.domain'
  toFun := momentumOperatorLinearPMap.toFun'

/-- The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `- i ℏ ψ'`. -/
def momentumOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x ↦ - Complex.I * ℏ * deriv ψ x

TODO "GPZWI" "Make API connecting the `momentumOperator` to `momentumOperatorLinearPMap`
  for one-dimensional QM."

end
end OneDimension
end QuantumMechanics
