/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PhysLean.StatisticalMechanics.Temperature
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Meta.Linters.Sorry
import Mathlib.Analysis.SpecialFunctions.Log.Summable
/-!

# Canonical ensemble

A canonical ensemble describes a system in thermal equilibrium with a heat bath at a
fixed temperature.

In this file we define the canonical ensemble, its partition function, the
probability of being in a given microstate, the mean energy, the entropy and
the Helmholtz free energy.

We also define the addition of two canonical ensembles, and prove results related
to the properties of additions of canonical ensembles.

## References

- https://www.damtp.cam.ac.uk/user/tong/statphys/statmechhtml/S1.html#E23

-/

/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
  and a map `ι → ℝ` which associates which each microstate an energy. -/
def CanonicalEnsemble (ι : Type) : Type := ι → ℝ

namespace CanonicalEnsemble
open Real Temperature

variable {ι ι1 : Type} (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

/-- The addition of two `CanonicalEnsemble`. -/
instance {ι1 ι2 : Type} : HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
    (CanonicalEnsemble (ι1 × ι2)) where
  hAdd := fun 𝓒1 𝓒2 => fun (i : ι1 × ι2) => 𝓒1 i.1 + 𝓒2 i.2

/-- Scalar multiplication of `CanonicalEnsemble`, defined such that
  `nsmul n 𝓒` is `n` coppies of the canonical ensemble `𝓒`. -/
def nsmul (n : ℕ) (𝓒1 : CanonicalEnsemble ι) : CanonicalEnsemble (Fin n → ι) :=
  fun f => ∑ i, 𝓒1 (f i)

lemma nsmul_eq (n : ℕ) (𝓒1 : CanonicalEnsemble ι) : nsmul n 𝓒1 = fun f => ∑ i, 𝓒1 (f i) := rfl

set_option linter.unusedVariables false in
/-- The microstates of a the canonical ensemble -/
@[nolint unusedArguments]
abbrev microstates {ι : Type} (𝓒 : CanonicalEnsemble ι) : Type := ι

/-!

## The energy of the microstates

-/
/-- The energy of associated with a mircrostate of the canonical ensemble. -/
abbrev energy (𝓒 : CanonicalEnsemble ι) : microstates 𝓒 → ℝ := 𝓒

@[simp]
lemma energy_add_apply (i : microstates (𝓒 + 𝓒1)) :
    (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2 := by
  simp [energy]
  rfl

@[simp]
lemma energy_nsmul_apply (n : ℕ) (f : Fin n → microstates 𝓒) :
    (nsmul n 𝓒).energy f = ∑ i, 𝓒.energy (f i) := by
  simp [energy, nsmul]

/-!

## The partition function of the canonical ensemble

-/

TODO "G5AM2" "Generalize the parition function to non-finite types of
  microstates."

/-- The partition function of the canonical ensemble. -/
noncomputable def partitionFunction [Fintype ι] (T : Temperature) : ℝ :=
  ∑ i, exp (- β T * 𝓒.energy i)

lemma partitionFunction_add [Fintype ι] [Fintype ι1] :
    (𝓒 + 𝓒1).partitionFunction T = 𝓒.partitionFunction T * 𝓒1.partitionFunction T := by
  simp [partitionFunction]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  congr
  funext i
  rw [Finset.mul_sum]
  congr
  funext j
  rw [← Real.exp_add]
  congr
  simp [energy]
  ring

/-- The partition function of `n` copies of a canonical ensemble. -/
@[simp]
lemma partitionFunction_nsmul [Fintype ι] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).partitionFunction T = (𝓒.partitionFunction T) ^ n := by
  simp only [partitionFunction, energy_nsmul_apply, neg_mul]
  rw [Fintype.sum_pow]
  congr
  funext f
  rw [← Real.exp_sum]
  congr
  simp [Finset.mul_sum]

lemma partitionFunction_pos [Fintype ι] [Nonempty ι] (T : Temperature) :
    0 < partitionFunction 𝓒 T := by
  rw [partitionFunction]
  apply Finset.sum_pos
  · intro i hi
    exact exp_pos (-T.β * 𝓒.energy i)
  · simp

@[simp]
lemma partitionFunction_neq_zero [Fintype ι] [Nonempty ι] (T : Temperature) :
    partitionFunction 𝓒 T ≠ 0:= by
  have h1 := partitionFunction_pos 𝓒 T
  exact Ne.symm (ne_of_lt h1)

/-- The partition function of the canonical ensemble as a function of `β` -/
noncomputable def partitionFunctionβ [Fintype ι] (β : ℝ) : ℝ :=
  ∑ i, exp (- β * 𝓒.energy i)

lemma partitionFunctionβ_def [Fintype ι]:
    partitionFunctionβ 𝓒 = fun β => ∑ i, exp (- β * 𝓒.energy i) := by rfl

@[fun_prop]
lemma partitionFunctionβ_differentiable [Fintype ι] :
    Differentiable ℝ 𝓒.partitionFunctionβ := by
  rw [partitionFunctionβ_def]
  fun_prop

lemma partitionFunction_eq_partitionFunctionβ [Fintype ι] (T : Temperature) :
    partitionFunction 𝓒 T = partitionFunctionβ 𝓒 (β T) := by
  simp [partitionFunction, partitionFunctionβ, β]

/-!

## The probability of being in a given microstate
-/

/-- The probability of been in a given microstate. -/
noncomputable def probability [Fintype ι] (i : microstates 𝓒) (T : Temperature) : ℝ :=
  exp (- β T * 𝓒.energy i) / partitionFunction 𝓒 T

/-- Probability of a microstate in a canonical ensemble is less then or equal to `1`. -/
lemma probability_le_one [Fintype ι] [Nonempty ι] (i : microstates 𝓒) (T : Temperature) :
    𝓒.probability i T ≤ 1 := by
  rw [probability]
  rw [div_le_one]
  · simp [partitionFunction]
    apply Finset.single_le_sum (f := fun x => exp (-(T.β * 𝓒.energy x)))
    · intro i _
      exact exp_nonneg (-(T.β * 𝓒.energy i))
    · simp
  · exact partitionFunction_pos 𝓒 T

/-- Probability of a microstate in a canonical ensemble is non-negative. -/
lemma probability_nonneg [Fintype ι] [Nonempty ι] (i : microstates 𝓒) (T : Temperature) :
    0 ≤ 𝓒.probability i T := by
  rw [probability]
  apply div_nonneg
  · exact exp_nonneg (-T.β * 𝓒.energy i)
  · exact le_of_lt (partitionFunction_pos 𝓒 T)

lemma probability_neq_zero [Fintype ι] [Nonempty ι] (i : microstates 𝓒) (T : Temperature) :
    probability 𝓒 i T ≠ 0 := by
  rw [probability]
  field_simp

@[simp]
lemma probability_add [Fintype ι] [Fintype ι1]
    (i : microstates (𝓒 + 𝓒1)) (T : Temperature) :
    (𝓒 + 𝓒1).probability i T = 𝓒.probability i.1 T * 𝓒1.probability i.2 T := by
  simp [probability]
  rw [partitionFunction_add 𝓒 𝓒1]
  field_simp
  congr
  rw [← Real.exp_add]
  ring_nf

/-- The probability of a microstate in `n` copies of a canonical ensemble is
  equal to the product of the probability of the corresponding individual microstates. -/
@[simp]
lemma probability_nsmul [Fintype ι] (n : ℕ)
    (f : microstates (nsmul n 𝓒)) (T : Temperature) :
    (nsmul n 𝓒).probability f T = ∏ i, 𝓒.probability (f i) T := by
  simp [probability, nsmul]
  congr
  rw [← Real.exp_sum]
  congr
  simp [Finset.mul_sum]

@[simp]
lemma sum_probability_eq_one [Fintype ι] [Nonempty ι] (T : Temperature) :
    ∑ i, probability 𝓒 i T = 1 := by
  simp [probability]
  rw [← Finset.sum_div]
  field_simp
  rw [partitionFunction]
  ring_nf

/-!

## The mean energy of the canonical ensemble

-/

/-- The mean energy of the canonical ensemble. -/
noncomputable def meanEnergy [Fintype ι] (T : Temperature) : ℝ :=
  ∑ i, 𝓒.energy i * probability 𝓒 i T

@[simp]
lemma meanEnergy_add [Fintype ι] [Nonempty ι] (𝓒1 : CanonicalEnsemble ι1) [Fintype ι1]
    [Nonempty ι1]
    (T : Temperature) :
    (𝓒 + 𝓒1).meanEnergy T = 𝓒.meanEnergy T + 𝓒1.meanEnergy T := by
  simp [meanEnergy]
  conv_lhs =>
    enter [2, x]
    rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp only
    congr
    funext i
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only
    congr
    funext i
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp

/-- The mean energy of `n` copies of a canonical ensemble is equal
  to `n` times the mean energy of the canonical ensemble.

  Note, can't make this `SMul` since the target type depends on the
  value of `n`. -/
lemma meanEnergy_nsmul [Fintype ι] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).meanEnergy T = n * 𝓒.meanEnergy T := by
  sorry

lemma meanEnergy_eq_logDeriv_partitionFunctionβ [Fintype ι] (T : Temperature) :
    meanEnergy 𝓒 T = - logDeriv (partitionFunctionβ 𝓒) (β T) := by
  rw [logDeriv_apply]
  nth_rewrite 1 [partitionFunctionβ_def]
  rw [deriv_fun_sum]
  · simp [meanEnergy]
    rw [@neg_div]
    simp only [neg_neg]
    rw [Finset.sum_div]
    congr
    funext i
    simp [probability]
    rw [partitionFunction_eq_partitionFunctionβ 𝓒 T]
    ring
  · intro i
    fun_prop

open Constants

/-!

## Entropy

-/

/-- The entropy of the canonical ensemble. -/
noncomputable def entropy [Fintype ι] (T : Temperature) : ℝ :=
  - kB * ∑ i, probability 𝓒 i T * log (probability 𝓒 i T)

/-- Entropy is addative on adding canonical ensembles. -/
@[simp]
lemma entropy_add [Fintype ι] [Nonempty ι] (𝓒1 : CanonicalEnsemble ι1) [Fintype ι1]
    [Nonempty ι1] (T : Temperature) :
    (𝓒 + 𝓒1).entropy T = 𝓒.entropy T + 𝓒1.entropy T := by
  simp [entropy]
  conv_lhs =>
    enter [1, 2, 2, x]
    rw [log_mul (probability_neq_zero 𝓒 x.1 T) (probability_neq_zero 𝓒1 x.2 T)]
    rw [mul_add]
  rw [Finset.sum_add_distrib, mul_add, neg_add]
  congr 1
  · simp
    left
    rw [Fintype.sum_prod_type]
    simp only
    congr
    funext i
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    simp
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [neg_inj, mul_eq_mul_left_iff, NNReal.coe_eq_zero]
    left
    congr
    funext i
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    simp

/-- The entropy of `n` copies of a canonical ensemble is equal
  to `n` times the entropy of the canonical ensemble. -/
@[sorryful]
lemma entropy_nsmul [Fintype ι] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).entropy T = n * 𝓒.entropy T := sorry

/-!

## Helmholtz free energy

-/

/-- The (Helmholtz) free energy of the canonical ensemble. -/
noncomputable def helmholtzFreeEnergy [Fintype ι] (T : Temperature) : ℝ :=
  𝓒.meanEnergy T - T * 𝓒.entropy T

/-- The Helmholtz free energy is addative. -/
@[simp]
lemma helmholtzFreeEnergy_add [Fintype ι] [Nonempty ι]
    [Fintype ι1] [Nonempty ι1] (T : Temperature) :
    (𝓒 + 𝓒1).helmholtzFreeEnergy T = 𝓒.helmholtzFreeEnergy T + 𝓒1.helmholtzFreeEnergy T := by
  simp [helmholtzFreeEnergy]
  ring

/-- The free energy of `n` copies of a canonical ensemble is equal
  to `n` times the entropy of the canonical ensemble. -/
@[sorryful]
lemma helmholtzFreeEnergy_nsmul [Fintype ι] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).helmholtzFreeEnergy T = n * 𝓒.helmholtzFreeEnergy T := sorry

end CanonicalEnsemble
