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

namespace CanonicalEnsemble

open Temperature
open Real MeasureTheory

TODO "EVJNH" "Generalize the results for the two-state canonical ensemble so that the two
  states have arbitary energies, rather than one state having energy `0`."

/-- The canonical ensemble corresponding to state system, with one state of energy
  `E` and the other state of energy `0`. -/
noncomputable def twoState (E : ℝ) : CanonicalEnsemble (Fin 2) where
  energy := fun | 0 => 0 | 1 => E
  μ := Measure.count
  energy_measurable := by fun_prop

instance {E} : IsFinite (twoState E) where
  μ_eq_count := by rfl

lemma twoState_partitionFunction_apply_eq_one_add_exp (E : ℝ) (T : Temperature) :
    (twoState E).partitionFunction T = 1 + exp (- β T * E) := by
  rw [partitionFunction_of_fintype, twoState]
  simp

lemma twoState_partitionFunction_apply_eq_cosh (E : ℝ) (T : Temperature) :
    (twoState E).partitionFunction T = 2 * exp (- β T * E / 2) * cosh (β T * E / 2) := by
  rw [twoState_partitionFunction_apply_eq_one_add_exp, Real.cosh_eq]
  field_simp
  simp [mul_add, ← Real.exp_add, mul_assoc]
  field_simp
  simp [add_mul]
  exact Lean.Grind.CommRing.mul_comm (rexp (-(T.β * E))) 2

@[simp]
lemma twoState_energy_fst (E : ℝ) : (twoState E).energy 0 = 0 := by
  rfl

@[simp]
lemma twoState_energy_snd (E : ℝ) : (twoState E).energy 1 = E := by
  rfl

lemma twoState_probability_snd (E : ℝ) (T : Temperature) :
    (twoState E).probability T 1 = 1/2 * (1 - tanh (β T * E / 2)) := by
  simp [probability]
  rw [twoState_partitionFunction_apply_eq_cosh]
  field_simp
  trans 2 * rexp (-(↑T.β * E) / 2) *
    (cosh (↑T.β * E / 2) - tanh (↑T.β * E / 2) * cosh (↑T.β * E / 2))
  swap
  · ring
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

lemma twoState_meanEnergy_eq (E : ℝ) (T : Temperature) :
    (twoState E).meanEnergy T = E / 2 * (1 - tanh (β T * E / 2)) := by
  calc
    _ = ∑ i : Fin 2, (twoState E).energy i * (twoState E).probability T i :=
      meanEnergy_of_fintype (twoState E) T
    _ = E * (twoState E).probability T 1 := by simp [twoState]
  rw [twoState_probability_snd]
  ring

/-- A simplification of the `entropy` of the two-state canonical ensemble. -/
informal_lemma twoState_entropy_eq where
  tag := "EVJJI"
  deps := [``twoState, ``entropy]

/-- A simplification of the `helmholtzFreeEnergy` of the two-state canonical ensemble. -/
informal_lemma twoState_helmholtzFreeEnergy_eq where
  tag := "EVMPR"
  deps := [``twoState]

end CanonicalEnsemble
