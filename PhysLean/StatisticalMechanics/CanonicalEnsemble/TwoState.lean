/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.Meta.Informal.Basic
/-!

# Two-state canonical ensemble

This module contains the definitions and properties related to the two-state
canonical ensemble.

-/

namespace FiniteCanonicalEnsemble

open Temperature
open Real

TODO "EVJNH" "Generalize the results for the two-state canonical ensemble so that the two
  states have arbitary energies, rather than one state having energy `0`."

/-- The canonical ensemble corresponding to state system, with one state of energy
  `E` and the other state of energy `0`. -/
def twoState (E : ℝ) : FiniteCanonicalEnsemble (Fin 2) := fun | 0 => 0 | 1 => E

lemma twoState_partitionFunction_apply_eq_one_add_exp (E : ℝ) (T : Temperature) :
    (twoState E).partitionFunction T = 1 + exp (- β T * E) := by
  simp [partitionFunction, twoState]

lemma twoState_partitionFunction_apply_eq_cosh (E : ℝ) (T : Temperature) :
    (twoState E).partitionFunction T = 2 * exp (- β T * E / 2) * cosh (β T * E / 2) := by
  rw [twoState_partitionFunction_apply_eq_one_add_exp, Real.cosh_eq]
  field_simp
  simp [mul_add, ← Real.exp_add, mul_assoc]
  field_simp
  simp [add_mul]
  exact Lean.Grind.CommRing.mul_comm (rexp (-(T.β * E))) 2

lemma twoState_partitionFunctionβ_eq (E : ℝ) :
    (twoState E).partitionFunctionβ = fun β => 2 * exp (- β * E / 2) * cosh (β * E / 2) := by
  funext β
  simp [partitionFunctionβ, twoState, Real.cosh_eq]
  field_simp
  simp [mul_add, ← Real.exp_add, mul_assoc]
  field_simp
  simp [add_mul]
  exact Lean.Grind.CommRing.mul_comm (rexp (-(β * E))) 2

lemma twoState_meanEnergy_eq (E : ℝ) (T : Temperature) :
    (twoState E).meanEnergy T = E / 2 * (1 - tanh (β T * E / 2)) := by
  rw [meanEnergy_eq_logDeriv_partitionFunctionβ, twoState_partitionFunctionβ_eq]
  simp? [logDeriv] says simp only [logDeriv, neg_mul, Pi.div_apply]
  field_simp
  have h1 : deriv (fun β => 2 * rexp (-(β * E) / 2) * cosh (β * E / 2)) T.β
      = 2 * (- E /2) * exp (-(T.β * E) / 2) * cosh (T.β * E / 2) +
        2 * (E /2) * exp (-(T.β * E) / 2) * sinh (T.β * E / 2) := by
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [deriv_const_mul _ (by fun_prop)]
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, deriv.neg', differentiableAt_id, differentiableAt_const, deriv_mul,
      deriv_id'', one_mul, deriv_const', mul_zero, add_zero]
    rw [_root_.deriv_cosh (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_id, differentiableAt_const, deriv_mul, deriv_id'',
      one_mul, deriv_const', mul_zero, add_zero]
    field_simp
    ring
  rw [h1, Real.tanh_eq_sinh_div_cosh]
  field_simp [Real.sinh_eq, Real.cosh_eq]
  ring_nf

/-- A simplification of the `entropy` of the two-state canonical ensemble. -/
informal_lemma twoState_entropy_eq where
  tag := "EVJJI"
  deps := [``twoState, ``entropy]

/-- A simplification of the `helmholtzFreeEnergy` of the two-state canonical ensemble. -/
informal_lemma twoState_helmholtzFreeEnergy_eq where
  tag := "EVMPR"
  deps := [``twoState, ``helmholtzFreeEnergy]

end FiniteCanonicalEnsemble
