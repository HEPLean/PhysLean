/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
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
  dof := 0
  μ := Measure.count
  energy_measurable := by fun_prop

instance {E} : IsFinite (twoState E) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

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

/-- Probability of the excited (energy `E`) state in closed form. -/
lemma twoState_probability_snd (E : ℝ) (T : Temperature) :
    (twoState E).probability T 1 = 1 / 2 * (1 - Real.tanh (β T * E / 2)) := by
  have h_basic :
      (twoState E).probability T 1 =
        Real.exp (-β T * E) / (1 + Real.exp (-β T * E)) := by
    --  The mathematical partition function of `twoState` is `1 + e^{-βE}`.
    have hZ :
        (twoState E).mathematicalPartitionFunction T =
          1 + Real.exp (-β T * E) := by
      rw [mathematicalPartitionFunction_of_fintype]
      simp [twoState, Fin.sum_univ_two]
    simp [probability, hZ]
  set x : ℝ := β T * E with hx
  have h_sym :
      Real.exp (-x) / (1 + Real.exp (-x)) =
        Real.exp (-x / 2) / (Real.exp (x / 2) + Real.exp (-x / 2)) := by
    calc
      _ = (Real.exp (-x) * Real.exp (x / 2)) / ((1 + Real.exp (-x)) * Real.exp (x / 2)) := by
        field_simp; ring_nf
      _ = _ := by
        congr
        · rw [← Real.exp_add]; ring_nf
        · rw [add_mul, one_mul, ← Real.exp_add]; ring_nf
  have h_tanh (y : ℝ) :
      1 / 2 * (1 - Real.tanh y) = Real.exp (-y) / (Real.exp y + Real.exp (-y)) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
  have h_half :
      Real.exp (-x / 2) / (Real.exp (x / 2) + Real.exp (-x / 2)) =
        1 / 2 * (1 - Real.tanh (x / 2)) := by
    rw [h_tanh]
    ring_nf
  calc
    (twoState E).probability T 1
        = Real.exp (-x) / (1 + Real.exp (-x)) := by rw [hx, h_basic]; ring_nf
    _ = Real.exp (-x / 2) / (Real.exp (x / 2) + Real.exp (-x / 2)) := h_sym
    _ = 1 / 2 * (1 - Real.tanh (x / 2)) := h_half
    _ = 1 / 2 * (1 - Real.tanh (β T * E / 2)) := by rw [hx]

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
  deps := [``twoState, ``thermodynamicEntropy]

/-- A simplification of the `helmholtzFreeEnergy` of the two-state canonical ensemble. -/
informal_lemma twoState_helmholtzFreeEnergy_eq where
  tag := "EVMPR"
  deps := [``twoState]

end CanonicalEnsemble
