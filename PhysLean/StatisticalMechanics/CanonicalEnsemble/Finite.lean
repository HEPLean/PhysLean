/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Lemmas
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

open Real Temperature MeasureTheory Constants
open scoped Temperature CanonicalEnsemble

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)

variable {ι1 : Type} [Fintype ι1] [MeasurableSpace ι1]
  [MeasurableSingletonClass ι1] (𝓒1 : CanonicalEnsemble ι1)

/-- A finite `CanonicalEnsemble` is one whose microstates form a finite type
and whose measure is the counting measure. For such systems, the state space is
inherently discrete and dimensionless, so we require `dof = 0` and
`phaseSpaceUnit = 1`. -/
class IsFinite (𝓒 : CanonicalEnsemble ι) [Fintype ι] : Prop where
  μ_eq_count : 𝓒.μ = Measure.count
  dof_eq_zero : 𝓒.dof = 0
  phase_space_unit_eq_one : 𝓒.phaseSpaceunit = 1

instance [IsFinite 𝓒] [IsFinite 𝓒1] : IsFinite (𝓒 + 𝓒1) where
  μ_eq_count := by
    rw [μ_add]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒), IsFinite.μ_eq_count (𝓒:=𝓒1)]
    refine Measure.prod_eq ?_
    intro s t hs ht
    rw [Measure.count_apply, Measure.count_apply, Measure.count_apply]
    rw [← ENat.toENNReal_mul]
    congr
    simp [Set.encard, ENat.card_congr (Equiv.Set.prod ..)]
    · exact ht
    · exact hs
    · exact MeasurableSet.prod hs ht
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒), IsFinite.dof_eq_zero (𝓒:=𝓒1)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (e : ι1 ≃ᵐ ι) : IsFinite (congr 𝓒 e) where
  μ_eq_count := by
    simp [congr]
    rw [IsFinite.μ_eq_count (𝓒:=𝓒)]
    refine Measure.ext_iff.mpr ?_
    intro s hs
    rw [@MeasurableEquiv.map_apply]
    rw [Measure.count_apply, Measure.count_apply]
    simp only [ENat.toENNReal_inj]
    rw [@MeasurableEquiv.preimage_symm]
    rw [← Set.Finite.cast_ncard_eq, ← Set.Finite.cast_ncard_eq]
    congr 1
    change (e.toEmbedding '' s).ncard = _
    rw [Set.ncard_map]
    · exact Set.toFinite s
    · exact Set.toFinite (⇑e '' s)
    · exact hs
    · exact (MeasurableEquiv.measurableSet_preimage e.symm).mpr hs
  dof_eq_zero := by
    simp [IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

instance [IsFinite 𝓒] (n : ℕ) : IsFinite (nsmul n 𝓒) where
  μ_eq_count := by
    induction n with
    | zero =>
      classical
      haveI : Subsingleton (Fin 0 → ι) := ⟨by intro f g; funext i; exact Fin.elim0 i⟩
      have h_cases :
          ∀ s : Set (Fin 0 → ι), s = ∅ ∨ s = Set.univ := by
        intro s; classical
        by_cases hne : s.Nonempty
        · right
          ext x; constructor
          · intro _; trivial
          · intro _; obtain ⟨y, hy⟩ := hne
            have : x = y := Subsingleton.elim _ _
            simpa [this] using hy
        · left
          ext x; constructor
          · intro hx; exact (hne ⟨x, hx⟩).elim
          · intro hx; cases hx
      refine Measure.ext (fun s _ => ?_)
      rcases h_cases s with hs | hs
      · subst hs
        simp [CanonicalEnsemble.nsmul, IsFinite.μ_eq_count (𝓒:=𝓒)]
      · subst hs
        simp [CanonicalEnsemble.nsmul, IsFinite.μ_eq_count (𝓒:=𝓒)]
    | succ n ih =>
      classical
      haveI : IsFinite (nsmul n 𝓒) := {
        μ_eq_count := ih
        dof_eq_zero := by
          simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
        phase_space_unit_eq_one := by
          simp [CanonicalEnsemble.phase_space_unit_nsmul,
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
      }
      letI : Fintype (Fin (n+1) → ι) := inferInstance
      have h :
        ((𝓒 + nsmul n 𝓒).congr
            (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0)).μ
          = Measure.count := by erw [IsFinite.μ_eq_count]; aesop
      rw [← h]; rw [← @nsmul_succ]
  dof_eq_zero := by
    simp [CanonicalEnsemble.dof_nsmul, IsFinite.dof_eq_zero (𝓒:=𝓒)]
  phase_space_unit_eq_one := by
    simp [CanonicalEnsemble.phase_space_unit_nsmul,
      IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]

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

/-- The Shannon entropy of a finite canonical ensemble.
This is defined by the formula `S = -k_B ∑ pᵢ log pᵢ`. It is proven to be
equivalent to the `differentialEntropy` and the `thermodynamicEntropy` for systems
satisfying the `IsFinite` property. -/
noncomputable def shannonEntropy (T : Temperature) : ℝ :=
  -kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i)

lemma mathematicalPartitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.mathematicalPartitionFunction T = ∑ i, exp (- β T * 𝓒.energy i) := by
  rw [mathematicalPartitionFunction_eq_integral]
  rw [MeasureTheory.integral_fintype]
  simp [IsFinite.μ_eq_count]
  · rw [IsFinite.μ_eq_count]
    exact Integrable.of_finite

lemma partitionFunction_of_fintype [IsFinite 𝓒] (T : Temperature) :
    𝓒.partitionFunction T = ∑ i, exp (- T.β * 𝓒.energy i) := by
  simp [partitionFunction, mathematicalPartitionFunction_of_fintype,
        IsFinite.dof_eq_zero, IsFinite.phase_space_unit_eq_one]

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

omit [MeasurableSingletonClass ι] in
lemma entropy_of_fintype (T : Temperature) :
    𝓒.shannonEntropy T = - kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i) := by
  simp [shannonEntropy]

lemma probability_le_one [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    𝓒.probability T i ≤ 1 := by
  classical
  unfold probability
  have hnum_le :
      Real.exp (- T.β * 𝓒.energy i) ≤ 𝓒.mathematicalPartitionFunction T := by
    rw [mathematicalPartitionFunction_of_fintype (𝓒:=𝓒) T]
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : ι => Real.exp (- β T * 𝓒.energy j))
        (by intro _ _; exact Real.exp_nonneg _)
        (Finset.mem_univ i))
  have hZpos :
      0 < 𝓒.mathematicalPartitionFunction T := by
    classical
    rw [mathematicalPartitionFunction_of_fintype (𝓒:=𝓒) T]
    obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < Real.exp (- β T * 𝓒.energy j₀) := Real.exp_pos _
    have hle :
        Real.exp (- β T * 𝓒.energy j₀)
          ≤ ∑ j, Real.exp (- β T * 𝓒.energy j) := by
      have := (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : ι => Real.exp (- β T * 𝓒.energy j))
        (by intro _ _; exact Real.exp_nonneg _)
        (Finset.mem_univ j₀))
      simpa using this
    exact lt_of_lt_of_le hterm_pos hle
  have := (div_le_div_iff_of_pos_right hZpos).mpr hnum_le
  simpa [div_self hZpos.ne'] using this

/-- Finite specialization: strict positivity of the mathematical partition function. -/
lemma mathematicalPartitionFunction_pos_finite
    [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.mathematicalPartitionFunction T := by
  simpa using (CanonicalEnsemble.mathematicalPartitionFunction_pos (𝓒:=𝓒) T)

/-- Finite specialization: strict positivity of the (physical) partition function. -/
lemma partitionFunction_pos_finite [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 < 𝓒.partitionFunction T := by
  simpa [partitionFunction, IsFinite.dof_eq_zero (𝓒:=𝓒),
        IsFinite.phase_space_unit_eq_one (𝓒:=𝓒), pow_zero]
    using mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)

/-- Finite specialization: non-negativity (indeed positivity) of probabilities. -/
lemma probability_nonneg_finite [IsFinite 𝓒] [Nonempty ι] (T : Temperature) (i : ι) :
    0 ≤ 𝓒.probability T i := by
  classical
  unfold probability
  have hZpos := mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
  exact div_nonneg (Real.exp_nonneg _) hZpos.le

/-- The sum of probabilities over all microstates is 1. -/
lemma sum_probability_eq_one [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    ∑ i, 𝓒.probability T i = 1 := by
  classical
  simp_rw [probability]
  rw [← Finset.sum_div]
  have hZdef := mathematicalPartitionFunction_of_fintype (𝓒:=𝓒) T
  have hZpos := mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
  have hZne : 𝓒.mathematicalPartitionFunction T ≠ 0 := hZpos.ne'
  simp [hZdef]
  simp_all only [neg_mul, ne_eq, not_false_eq_true, div_self]

/-- The entropy of a finite canonical ensemble (Shannon entropy) is non-negative. -/
lemma entropy_nonneg [IsFinite 𝓒] [Nonempty ι] (T : Temperature) :
    0 ≤ 𝓒.shannonEntropy T := by
  classical
  unfold shannonEntropy
  set p : ι → ℝ := fun i => 𝓒.probability T i
  have h_term_le_zero :
      ∀ i : ι, p i * Real.log (p i) ≤ 0 := by
    intro i
    have hp_le_one : p i ≤ 1 := probability_le_one (𝓒:=𝓒) (T:=T) i
    have hp_pos : 0 < p i := by
      have num_pos : 0 < Real.exp (- T.β * 𝓒.energy i) := Real.exp_pos _
      have denom_pos : 0 < 𝓒.mathematicalPartitionFunction T :=
        mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
      have : 0 < Real.exp (- T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T :=
        div_pos num_pos denom_pos
      simpa [p, probability] using this
    have hlog_le_zero : Real.log (p i) ≤ 0 := by
      have hlog_le : Real.log (p i) ≤ Real.log 1 :=
      log_le_log hp_pos hp_le_one
      simpa [Real.log_one] using hlog_le
    have hp_nonneg : 0 ≤ p i := hp_pos.le
    have := mul_le_mul_of_nonneg_left hlog_le_zero hp_nonneg
    simpa using this
  have h_sum_le_zero :
      ∑ i, p i * Real.log (p i) ≤ 0 :=
    Fintype.sum_nonpos h_term_le_zero
  have hkBpos : 0 < (kB : ℝ) := kB_pos
  have : 0 ≤ (kB : ℝ) * (-(∑ i, p i * Real.log (p i))) :=
    mul_nonneg hkBpos.le (neg_nonneg.mpr h_sum_le_zero)
  simpa [p, shannonEntropy, mul_comm, mul_left_comm, mul_assoc, neg_mul,
        sub_eq_add_neg] using this

lemma shannonEntropy_eq_differentialEntropy [IsFinite 𝓒] (T : Temperature) :
    𝓒.shannonEntropy T = 𝓒.differentialEntropy T := by
  simp [shannonEntropy, differentialEntropy, integral_fintype, μProd_of_fintype]

/-- In the finite, nonempty case the thermodynamic and Shannon entropies coincide.
All semi-classical correction factors vanish (`dof = 0`, `phaseSpaceUnit = 1`),
so the absolute thermodynamic entropy reduces to the discrete Shannon form. -/
theorem thermodynamicEntropy_eq_shannonEntropy [IsFinite 𝓒]
    (T : Temperature) :-- (hT : 0 < T.val) :
    𝓒.thermodynamicEntropy T = 𝓒.shannonEntropy T := by
  have h_thermo_eq_diff :
      𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
    unfold CanonicalEnsemble.thermodynamicEntropy
      CanonicalEnsemble.differentialEntropy
    have h_log :
        (fun i => Real.log (𝓒.physicalProbability T i))
          = (fun i => Real.log (𝓒.probability T i)) := by
      funext i
      simp [CanonicalEnsemble.physicalProbability,
            IsFinite.dof_eq_zero (𝓒:=𝓒),
            IsFinite.phase_space_unit_eq_one (𝓒:=𝓒)]
    simp_all only [physicalProbability_def]
  have h_shannon :
      𝓒.shannonEntropy T = 𝓒.differentialEntropy T :=
    (shannonEntropy_eq_differentialEntropy (𝓒:=𝓒) T)
  calc
    𝓒.thermodynamicEntropy T
        = 𝓒.differentialEntropy T := h_thermo_eq_diff
    _ = 𝓒.shannonEntropy T := h_shannon.symm

end CanonicalEnsemble
