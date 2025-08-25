/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Basic
/-!

# Finite canonical ensemble

A canonical ensemble describes a system in thermal equilibrium with a heat bath at a
fixed temperature.

In this file we define the canonical ensemble, its partition function, the
probability of being in a given microstate, the mean energy, the entropy and
the Helmholtz free energy.

We also define the addition of two canonical ensembles, and prove results related
to the properties of additions of canonical ensembles.

## References

- https://www.damtp.cam.ac.uk/user/tong/statphys/statmechhtml/S1.html#E23

## Implementation note

This file only deals with finite canonical ensembles.
When the more general theory of canonical ensembles is implemented,
this file should be modified.

-/

namespace CanonicalEnsemble

open Real Temperature MeasureTheory

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  [MeasurableSingletonClass ι1] (𝓒1 : CanonicalEnsemble ι1)

/-- A finite `CanonicalEnsemble` is one which has a finite
  type of microstates and the counting measure on them. -/
class IsFinite [Fintype ι] : Prop where
  μ_eq_count : 𝓒.μ = Measure.count

instance [IsFinite 𝓒] [IsFinite 𝓒1] : IsFinite (𝓒 + 𝓒1) where
  μ_eq_count := by
    rw [μ_add]
    rw [IsFinite.μ_eq_count, IsFinite.μ_eq_count]
    refine Measure.prod_eq ?_
    intro s t hs ht
    rw [Measure.count_apply, Measure.count_apply, Measure.count_apply]
    rw [← ENat.toENNReal_mul]
    congr
    simp [Set.encard, ENat.card_congr (Equiv.Set.prod ..)]
    · exact ht
    · exact hs
    · exact MeasurableSet.prod hs ht

instance [IsFinite 𝓒] (e : ι1 ≃ᵐ ι) : IsFinite (congr 𝓒 e) where
  μ_eq_count := by
    simp [congr]
    rw [IsFinite.μ_eq_count]
    refine Measure.ext_iff.mpr ?_
    intro s hs
    rw [@MeasurableEquiv.map_apply]
    rw [Measure.count_apply, Measure.count_apply]
    simp

    rw [@MeasurableEquiv.preimage_symm]
    rw [← Set.Finite.cast_ncard_eq, ← Set.Finite.cast_ncard_eq,]
    congr 1
    change (e.toEmbedding '' s).ncard = _
    rw [Set.ncard_map]
    · exact Set.toFinite s
    · exact Set.toFinite (⇑e '' s)
    · exact hs
    · exact (MeasurableEquiv.measurableSet_preimage e.symm).mpr hs

instance [IsFinite 𝓒] (n : ℕ) : IsFinite (nsmul n 𝓒) where
  μ_eq_count := by
    induction n with
    | zero =>
      rw [@Measure.ext_iff_singleton]
      simp [nsmul]
      rw [← Set.univ_pi_singleton]
      simp
    | succ n ih =>
      rw [nsmul_succ]
      haveI : IsFinite (nsmul n 𝓒) := ⟨ih⟩
      rw [IsFinite.μ_eq_count]
      exact Pi.instFintype

instance [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μ) := by
  rw [IsFinite.μ_eq_count]
  infer_instance

/-- In the finite (counting) case a nonempty index type gives a nonzero measure. -/
instance [IsFinite 𝓒] [Nonempty ι] : NeZero 𝓒.μ := by
  classical
  refine ⟨?_⟩
  intro hμ
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hone : 𝓒.μ {i₀} = 1 := by
    simp [IsFinite.μ_eq_count (𝓒:=𝓒)]
  simp_all only [Measure.coe_zero, Pi.zero_apply, zero_ne_one]

/--
Entropy of the finite canonical ensemble (Shannon entropy). -/
noncomputable def entropy (T : Temperature) : ℝ :=
  𝓒.differentialEntropy T

omit [Fintype ι] [MeasurableSingletonClass ι] in
@[simp] lemma entropy_eq_differentialEntropy (T : Temperature) :
    𝓒.entropy T = 𝓒.differentialEntropy T := rfl

lemma partitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.partitionFunction T = ∑ i, exp (- β T * 𝓒.energy i) := by
  rw [partitionFunction_eq_integral]
  rw [MeasureTheory.integral_fintype]
  simp [IsFinite.μ_eq_count]
  · rw [IsFinite.μ_eq_count]
    exact Integrable.of_finite

@[simp]
lemma μBolt_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μBolt T).real {i} = Real.exp (- β T * 𝓒.energy i) := by
  rw [μBolt]
  simp only [neg_mul]
  rw [@measureReal_def]
  simp [IsFinite.μ_eq_count]
  exact Real.exp_nonneg _

instance {T} [IsFinite 𝓒] : IsFiniteMeasure (𝓒.μBolt T) := by
  rw [μBolt]
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact HasFiniteIntegral.of_finite

@[simp]
lemma μProd_of_fintype (T : Temperature) [IsFinite 𝓒] (i : ι) :
    (𝓒.μProd T).real {i} = 𝓒.probability T i := by
  rw [μProd]
  simp [probability]
  ring_nf
  rw [mul_comm]
  rfl

lemma meanEnergy_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.meanEnergy T = ∑ i, 𝓒.energy i * 𝓒.probability T i := by
  simp [meanEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [mul_comm]
  exact Integrable.of_finite

open Constants

lemma entropy_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.entropy T = - kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i) := by
  simp [entropy, differentialEntropy]
  rw [MeasureTheory.integral_fintype]
  simp only [μProd_of_fintype, smul_eq_mul, true_or]
  exact Integrable.of_finite

lemma probability_le_one [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    𝓒.probability T i ≤ 1 := by
  classical
  unfold probability
  have hnum_le : Real.exp (- β T * 𝓒.energy i) ≤ 𝓒.partitionFunction T := by
    rw [partitionFunction_of_fintype (𝓒:=𝓒) T]
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : ι => Real.exp (- β T * 𝓒.energy j))
        (by intro _ _; exact Real.exp_nonneg _)
        (Finset.mem_univ i))
  have hZpos :
      0 < 𝓒.partitionFunction T :=
    partitionFunction_pos (𝓒:=𝓒) (T:=T)
  have := (div_le_div_iff_of_pos_right hZpos).mpr hnum_le
  simpa [probability, div_self hZpos.ne'] using this

/-- Finite specialization of the general strict positivity of the partition function. -/
lemma partitionFunction_pos_finite [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.partitionFunction T :=
  partitionFunction_pos (𝓒:=𝓒) (T:=T)

/-- Finite specialization of probability nonnegativity. -/
lemma probability_nonneg_finite [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    0 ≤ 𝓒.probability T i :=
  probability_nonneg (𝓒:=𝓒) (T:=T) i

/-- The sum of probabilities over all microstates is 1. -/
lemma sum_probability_eq_one [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    ∑ i, 𝓒.probability T i = 1 := by
  classical
  simp_rw [probability]
  rw [← Finset.sum_div, partitionFunction_of_fintype (𝓒:=𝓒) T]
  have hZpos : 0 < 𝓒.partitionFunction T := partitionFunction_pos (𝓒:=𝓒) (T:=T)
  have hne : (∑ i, Real.exp (- β T * 𝓒.energy i)) ≠ 0 := by
    simpa [partitionFunction_of_fintype (𝓒:=𝓒) T] using hZpos.ne'
  exact div_self hne

/-- The entropy of a finite canonical ensemble is non-negative (Shannon entropy). -/
lemma entropy_nonneg [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 ≤ 𝓒.entropy T := by
  have hInt :
      Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T) := by
    classical
    simp only [probability, neg_mul, Integrable.of_finite]
  refine differentialEntropy_nonneg_of_prob_le_one (𝓒:=𝓒) (T:=T) hInt
    (probability_le_one (𝓒:=𝓒) (T:=T))

end CanonicalEnsemble
