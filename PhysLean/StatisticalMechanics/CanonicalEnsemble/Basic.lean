/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.Temperature
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Meta.Linters.Sorry
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Prod
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

open MeasureTheory
open Real Temperature

/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
  and a map `ι → ℝ` which associates which each microstate an energy. -/
structure CanonicalEnsemble (ι : Type) [MeasurableSpace ι] : Type where
  /-- The energy of associated with a mircrostate of the canonical ensemble. -/
  energy : ι → ℝ
  energy_measurable : Measurable energy
  /-- The measure on the indexing set of microstates. -/
  μ : MeasureTheory.Measure ι := by volume_tac
  [μ_sigmaFinite : SigmaFinite μ]

namespace CanonicalEnsemble
open Real Temperature

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

instance : SigmaFinite 𝓒.μ := 𝓒.μ_sigmaFinite

@[ext]
lemma ext {𝓒 𝓒' : CanonicalEnsemble ι} (h : 𝓒.energy = 𝓒'.energy) (hμ : 𝓒.μ = 𝓒'.μ) :
    𝓒 = 𝓒' := by
  cases 𝓒
  cases 𝓒'
  simp_all

@[fun_prop]
lemma energy_measurable' : Measurable 𝓒.energy := 𝓒.energy_measurable

/-- The addition of two `CanonicalEnsemble`. -/
noncomputable instance {ι1 ι2 : Type} [MeasurableSpace ι1] [MeasurableSpace ι2] :
    HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
    (CanonicalEnsemble (ι1 × ι2)) where
  hAdd := fun 𝓒1 𝓒2 => {
    energy := fun (i : ι1 × ι2) => 𝓒1.energy i.1 + 𝓒2.energy i.2,
    μ := 𝓒1.μ.prod 𝓒2.μ,
    energy_measurable := by fun_prop
  }

/-- The canonical ensemble with no microstates. -/
def empty : CanonicalEnsemble Empty where
  energy := isEmptyElim
  μ := 0
  energy_measurable := by fun_prop

/-- Given a measurable equivalence `e : ι1 ≃ᵐ ι` and a canonical ensemble
  `CanonicalEnsemble ι` the corresponding canonical ensemble `CanonicalEnsemble ι1`. -/
noncomputable def congr (e : ι1 ≃ᵐ ι) : CanonicalEnsemble ι1 where
  energy := fun i => 𝓒.energy (e i)
  μ := 𝓒.μ.map e.symm
  energy_measurable := by
    apply Measurable.comp
    · fun_prop
    · exact MeasurableEquiv.measurable e
  μ_sigmaFinite := MeasurableEquiv.sigmaFinite_map e.symm

@[simp]
lemma congr_energy_comp_symmm (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).energy ∘ e.symm = 𝓒.energy := by
  funext i
  simp [congr]

/-- Scalar multiplication of `CanonicalEnsemble`, defined such that
  `nsmul n 𝓒` is `n` coppies of the canonical ensemble `𝓒`. -/
noncomputable def nsmul (n : ℕ) (𝓒1 : CanonicalEnsemble ι) : CanonicalEnsemble (Fin n → ι) where
  energy := fun f => ∑ i, 𝓒1.energy (f i)
  μ := MeasureTheory.Measure.pi fun _ => 𝓒1.μ
  energy_measurable := by fun_prop

set_option linter.unusedVariables false in
/-- The microstates of a the canonical ensemble -/
@[nolint unusedArguments]
abbrev microstates (𝓒 : CanonicalEnsemble ι) : Type := ι

/-!

## The measure

-/

lemma μ_add : (𝓒 + 𝓒1).μ = 𝓒.μ.prod 𝓒1.μ := rfl

lemma μ_nsmul (n : ℕ) : (nsmul n 𝓒).μ = MeasureTheory.Measure.pi fun _ => 𝓒.μ := rfl

lemma μ_nsmul_zero_eq : (nsmul 0 𝓒).μ = Measure.pi (fun _ => 0) := by
  simp [nsmul, μ_nsmul]
  congr
  funext x
  exact Fin.elim0 x

/-!

## The energy of the microstates

-/

@[simp]
lemma energy_add_apply (i : microstates (𝓒 + 𝓒1)) :
    (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2 := rfl

lemma energy_nsmul_eq (n : ℕ) (𝓒1 : CanonicalEnsemble ι) :
    (nsmul n 𝓒1).energy = fun f => ∑ i, 𝓒1.energy (f i) := rfl

@[simp]
lemma energy_nsmul_apply (n : ℕ) (f : Fin n → microstates 𝓒) :
    (nsmul n 𝓒).energy f = ∑ i, 𝓒.energy (f i) := rfl

@[simp]
lemma energy_congr_apply (e : ι1 ≃ᵐ ι) (i : ι1) :
    (𝓒.congr e).energy i = 𝓒.energy (e i) := by rfl

/-!

## induction for nsmul

-/

open MeasureTheory

lemma nsmul_succ (n : ℕ) [SigmaFinite 𝓒.μ] : nsmul n.succ 𝓒 = (𝓒 + nsmul n 𝓒).congr
    (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0) := by
  ext1
  · ext x
    simp only [Nat.succ_eq_add_one, energy_nsmul_apply, energy_congr_apply,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero, Fin.consEquiv_symm_apply,
      energy_add_apply]
    exact Fin.sum_univ_succAbove (fun i => 𝓒.energy (x i)) 0
  · refine Eq.symm (MeasureTheory.MeasurePreserving.map_eq ?_)
    refine MeasurePreserving.symm _ ?_
    exact MeasureTheory.measurePreserving_piFinSuccAbove (n := n) (fun _ => 𝓒.μ) 0

/-!

## Non zero nature of the measure

-/

instance [NeZero 𝓒.μ] [NeZero 𝓒1.μ] : NeZero (𝓒 + 𝓒1).μ := by
  simp [μ_add]
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  have h1 : (𝓒.μ.prod (𝓒1.μ)) Set.univ =
      (𝓒.μ Set.univ) * (𝓒1.μ Set.univ) := by
    rw [← @Measure.prod_prod]
    simp
  rw [h1]
  exact NeZero.pos (𝓒.μ Set.univ * 𝓒1.μ Set.univ)

instance μ_neZero_congr [NeZero 𝓒.μ] (e : ι1 ≃ᵐ ι) :
    NeZero (𝓒.congr e).μ := by
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  simp only [Measure.measure_univ_pos, ne_eq]
  refine (Measure.map_ne_zero_iff ?_).mpr ?_
  · fun_prop
  · exact Ne.symm (NeZero.ne' _)

instance [NeZero 𝓒.μ] (n : ℕ) : NeZero (nsmul n 𝓒).μ := by
  induction n with
  | zero =>
    rw [μ_nsmul_zero_eq]
    rw [@neZero_iff]
    simp only [ne_eq]
    refine Measure.measure_univ_ne_zero.mp ?_
    simp
  | succ n ih =>
    rw [nsmul_succ]
    infer_instance

/-!

## The Boltzmann measure
-/

/-- The Boltzmann measure on the space of microstates. -/
noncomputable def μBolt (T : Temperature) : MeasureTheory.Measure ι :=
  𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β T * 𝓒.energy i)))

instance (T : Temperature) : SigmaFinite (𝓒.μBolt T) :=
  inferInstanceAs
    (SigmaFinite (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β T * 𝓒.energy i)))))

@[simp]
lemma μBolt_add (T : Temperature) :
    (𝓒 + 𝓒1).μBolt T = (𝓒.μBolt T).prod (𝓒1.μBolt T) := by
  rw [μBolt, μBolt, μBolt, MeasureTheory.prod_withDensity]
  congr
  funext i
  rw [← ENNReal.ofReal_mul, ← Real.exp_add]
  simp only [energy_add_apply, neg_mul]
  ring_nf
  · exact exp_nonneg (-T.β * 𝓒.energy i.1)
  · fun_prop
  · fun_prop

lemma μBolt_congr (e : ι1 ≃ᵐ ι) (T : Temperature) : (𝓒.congr e).μBolt T =
    (𝓒.μBolt T).map e.symm := by
  simp [congr, μBolt]
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  rw [lintegral_map, lintegral_map, lintegral_withDensity_eq_lintegral_mul₀]
  congr
  funext i
  simp only [Pi.mul_apply, MeasurableEquiv.apply_symm_apply]
  repeat fun_prop

lemma μBolt_nsmul [SigmaFinite 𝓒.μ] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).μBolt T = MeasureTheory.Measure.pi fun _ => (𝓒.μBolt T) := by
  induction n with
  | zero =>
    simp [nsmul, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ, μBolt_congr]
    rw [μBolt_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μBolt T) 0

lemma μBolt_ne_zero_of_μ_ne_zero (T : Temperature) (h : 𝓒.μ ≠ 0) :
    𝓒.μBolt T ≠ 0 := by
  simp [μBolt] at ⊢ h
  rw [Measure.ext_iff'] at ⊢ h
  simp only [Measure.coe_zero, Pi.zero_apply]
  have hs : {x | ENNReal.ofReal (rexp (-(↑T.β * 𝓒.energy x))) ≠ 0} = Set.univ := by
    ext i
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exp_pos _
  conv =>
    enter [1, s]
    rw [MeasureTheory.withDensity_apply_eq_zero' (by fun_prop), hs]
    simp
  simpa using h

instance (T : Temperature) [NeZero 𝓒.μ] : NeZero (𝓒.μBolt T) := by
  refine { out := ?_ }
  apply μBolt_ne_zero_of_μ_ne_zero
  exact Ne.symm (NeZero.ne' 𝓒.μ)

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)] :
    IsFiniteMeasure ((𝓒 + 𝓒1).μBolt T) := by
  simp only [μBolt_add]
  exact Measure.prod.instIsFiniteMeasure (𝓒.μBolt T) (𝓒1.μBolt T)

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] (n : ℕ) :
    IsFiniteMeasure ((nsmul n 𝓒).μBolt T) := by
  simp [μBolt_nsmul]
  exact MeasureTheory.Measure.pi.instIsFiniteMeasure (fun _ => 𝓒.μBolt T)

/-!

## The partition function of the canonical ensemble

-/

/-- The partition function of the canonical ensemble. -/
noncomputable def partitionFunction (T : Temperature) : ℝ := (𝓒.μBolt T).real Set.univ

lemma partitionFunction_eq_integral (T : Temperature) :
    partitionFunction 𝓒 T = ∫ i, exp (- T.β * 𝓒.energy i) ∂𝓒.μ := by
  trans ∫ i, 1 ∂𝓒.μBolt T
  · simp only [integral_const, smul_eq_mul, mul_one]
    rfl
  rw [μBolt]
  erw [integral_withDensity_eq_integral_smul]
  congr
  funext x
  simp [HSMul.hSMul, SMul.smul]
  · exact exp_nonneg _
  · fun_prop

lemma partitionFunction_add {T : Temperature} :
    (𝓒 + 𝓒1).partitionFunction T = 𝓒.partitionFunction T * 𝓒1.partitionFunction T := by
  simp only [partitionFunction, μBolt_add]
  rw [← measureReal_prod_prod]
  congr
  exact Eq.symm Set.univ_prod_univ

@[simp]
lemma partitionFunction_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).partitionFunction T = 𝓒.partitionFunction T := by
  rw [partitionFunction_eq_integral, partitionFunction_eq_integral]
  simp [congr]
  rw [integral_map_equiv]
  simp

/-- The partition function of `n` copies of a canonical ensemble. -/
lemma partitionFunction_nsmul (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).partitionFunction T = (𝓒.partitionFunction T) ^ n := by
  simp only [partitionFunction, μBolt_nsmul]
  rw [measureReal_def, Measure.pi_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_nonneg, measureReal_nonneg]
  rfl

lemma partitionFunction_nonneg (T : Temperature) :
    0 ≤ partitionFunction 𝓒 T := by
  simp [partitionFunction]

lemma paritionFunction_eq_zero_iff (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    partitionFunction 𝓒 T = 0 ↔ 𝓒.μ = 0 := by
  simp [partitionFunction]
  rw [measureReal_def]
  rw [ENNReal.toReal_eq_zero_iff]
  simp only [measure_ne_top, or_false]
  rw [μBolt]
  rw [MeasureTheory.withDensity_apply_eq_zero']
  simp only [neg_mul, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.inter_univ]
  let s : Set ι := {x | 0 < rexp (-(T.β * 𝓒.energy x))}
  have h : s = Set.univ := by
    ext i
    simp [s]
    exact exp_pos (-(T.β * 𝓒.energy i))
  change 𝓒.μ s = 0 ↔ 𝓒.μ = 0
  rw [h]
  simp only [Measure.measure_univ_eq_zero, s]
  fun_prop

open NNReal Constants

lemma partitionFunction_comp_ofβ_apply (β : ℝ≥0) :
    𝓒.partitionFunction (ofβ β) =
    (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β * 𝓒.energy i)))).real Set.univ := by
  simp only [partitionFunction, μBolt, β_ofβ, neg_mul]

/-!

## The probability measure

-/

/-- The probability of a given microstate in a canonical ensemble. -/
noncomputable def probability (T : Temperature) (i : ι) : ℝ :=
  (exp (- T.β * 𝓒.energy i)) / partitionFunction 𝓒 T

lemma probability_add {T : Temperature} (i : ι × ι1) :
    (𝓒 + 𝓒1).probability T i = 𝓒.probability T i.1 * 𝓒1.probability T i.2 := by
  simp [probability, partitionFunction_add, mul_add, Real.exp_add]
  ring

@[simp]
lemma probability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).probability T i = 𝓒.probability T (e i) := by
  simp [probability]

lemma probability_nsmul (n : ℕ) (T : Temperature) (f : Fin n → ι) :
    (nsmul n 𝓒).probability T f = ∏ i, 𝓒.probability T (f i) := by
  induction n with
  | zero =>
    simp [probability, partitionFunction_nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    rw [probability_congr]
    rw [probability_add]
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_symm_apply]
    rw [ih]
    exact Eq.symm (Fin.prod_univ_succAbove (fun i => 𝓒.probability T (f i)) 0)

/-- The probability measure associated with the Boltzmann distribution of a
  canonical ensemble. -/
noncomputable def μProd (T : Temperature) : MeasureTheory.Measure ι :=
  (𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T

instance (T : Temperature) : SigmaFinite (𝓒.μProd T) :=
  inferInstanceAs (SigmaFinite ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T))

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
  [NeZero 𝓒.μ] : IsProbabilityMeasure (𝓒.μProd T) := inferInstanceAs <|
  IsProbabilityMeasure ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)

lemma μProd_add {T : Temperature} [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)] : (𝓒 + 𝓒1).μProd T = (𝓒.μProd T).prod (𝓒1.μProd T) := by
  rw [μProd, μProd, μProd, μBolt_add]
  rw [MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right]
  rw [smul_smul]
  congr
  trans ((𝓒.μBolt T) Set.univ * (𝓒1.μBolt T) Set.univ)⁻¹
  swap
  · by_cases h : (𝓒.μBolt T) Set.univ = 0
    · simp [h]
    by_cases h1 : (𝓒1.μBolt T) Set.univ = 0
    · simp [h1]
    rw [ENNReal.mul_inv]
    · simp
    · simp
  · rw [← @Measure.prod_prod]
    simp

lemma μProd_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).μProd T = (𝓒.μProd T).map e.symm := by
  simp [μProd, μBolt_congr]
  congr 2
  rw [MeasurableEquiv.map_apply]
  simp

lemma μProd_nsmul (n : ℕ) (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    (nsmul n 𝓒).μProd T = MeasureTheory.Measure.pi fun _ => 𝓒.μProd T := by
  induction n with
  | zero =>
    simp [nsmul, μProd, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ]
    rw [μProd_congr]
    rw [μProd_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μProd T) 0

/-!

## Integrability of energy

-/

@[fun_prop]
lemma integrable_energy_add (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) (h1 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    Integrable (𝓒 + 𝓒1).energy ((𝓒 + 𝓒1).μProd T) := by
  rw [μProd_add]
  refine Integrable.add'' ?_ ?_
  · have h1 : (fun (i : ι × ι1) => 𝓒.energy i.1)
      = fun (i : ι × ι1) => 𝓒.energy i.1 * (fun (i : ι1) => 1) i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := 𝓒.energy) (g := (fun (i : ι1) => 1))
    · fun_prop
    · fun_prop
  · have h1 : (fun (i : ι × ι1) => 𝓒1.energy i.2)
      = fun (i : ι × ι1) => (fun (i : ι) => 1) i.1 * 𝓒1.energy i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := (fun (i : ι) => 1)) (g := 𝓒1.energy)
    · fun_prop
    · fun_prop

@[fun_prop]
lemma integrable_energy_congr (T : Temperature) (e : ι1 ≃ᵐ ι)
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (𝓒.congr e).energy ((𝓒.congr e).μProd T) := by
  simp [μProd_congr]
  refine (integrable_map_equiv e.symm (𝓒.congr e).energy).mpr ?_
  simp only [congr_energy_comp_symmm]
  exact h

@[fun_prop]
lemma integrable_energy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (nsmul n 𝓒).energy ((nsmul n 𝓒).μProd T) := by
  induction n with
  | zero =>
    simp [nsmul, μProd_nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    apply integrable_energy_congr
    apply integrable_energy_add
    · exact h
    · exact ih

/-!

## The mean energy

-/

/-- The mean energy of the canonical ensemble at temperature `T`. -/
noncomputable def meanEnergy (T : Temperature) : ℝ := ∫ i, 𝓒.energy i ∂𝓒.μProd T

lemma meanEnergy_add {T : Temperature}
    [IsFiniteMeasure (𝓒1.μBolt T)] [IsFiniteMeasure (𝓒.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T))
    (h2 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    (𝓒 + 𝓒1).meanEnergy T = 𝓒.meanEnergy T + 𝓒1.meanEnergy T := by
  rw [meanEnergy]
  simp only [energy_add_apply]
  rw [μProd_add]
  rw [MeasureTheory.integral_prod]
  simp only
  conv_lhs =>
    enter [2, x]
    rw [integral_add (integrable_const _) h2]
    rw [integral_const]
    simp
  rw [integral_add h1 (integrable_const _)]
  rw [integral_const]
  simp
  rfl
  · simpa [μProd_add] using integrable_energy_add 𝓒 𝓒1 T h1 h2

lemma meanEnergy_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).meanEnergy T = 𝓒.meanEnergy T := by
  simp [meanEnergy, μProd_congr]
  refine MeasurePreserving.integral_comp' ?_ 𝓒.energy
  refine { measurable := ?_, map_eq := ?_ }
  · exact MeasurableEquiv.measurable e
  · exact MeasurableEquiv.map_map_symm e

lemma meanEnergy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T)) :
    (nsmul n 𝓒).meanEnergy T = n * 𝓒.meanEnergy T := by
  induction n with
  | zero =>
    simp [nsmul, meanEnergy, μProd_nsmul]
  | succ n ih =>
    rw [nsmul_succ, meanEnergy_congr, meanEnergy_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
    · exact h1
    · exact integrable_energy_nsmul 𝓒 n T h1

/-!

## The entropy

-/

/-- The entropy of the Canonical ensemble. -/
noncomputable def entropy (T : Temperature) : ℝ :=
  - kB * ∫ i, log (probability 𝓒 T i) ∂𝓒.μProd T

end CanonicalEnsemble
