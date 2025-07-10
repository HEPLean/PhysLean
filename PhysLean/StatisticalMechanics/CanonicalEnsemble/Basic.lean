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

/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
  and a map `ι → ℝ` which associates which each microstate an energy. -/
structure CanonicalEnsemble (ι : Type) [MeasurableSpace ι] : Type where
  /-- The energy of associated with a mircrostate of the canonical ensemble. -/
  energy : ι → ℝ
  energy_measurable : Measurable energy
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
    simp
    exact Fin.sum_univ_succAbove (fun i => 𝓒.energy (x i)) 0
  · refine Eq.symm (MeasureTheory.MeasurePreserving.map_eq ?_)
    refine MeasurePreserving.symm _ ?_
    exact MeasureTheory.measurePreserving_piFinSuccAbove (n := n) (fun _ => 𝓒.μ) 0

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
lemma μBolt_add [SFinite 𝓒.μ] [SFinite 𝓒1.μ] (T : Temperature) :
    (𝓒 + 𝓒1).μBolt T = (𝓒.μBolt T).prod (𝓒1.μBolt T) := by
  rw [μBolt, μBolt, μBolt, MeasureTheory.prod_withDensity]
  congr
  funext i
  rw [← ENNReal.ofReal_mul, ← Real.exp_add]
  simp
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
  simp
  let s : Set ι := {x | 0 < rexp (-(T.β * 𝓒.energy x))}
  have h : s = Set.univ := by
    ext i
    simp [s]
    exact exp_pos (-(T.β * 𝓒.energy i))
  change 𝓒.μ s = 0 ↔ 𝓒.μ = 0
  rw [h]
  simp
  fun_prop

open NNReal Constants

lemma partitionFunction_comp_ofβ_apply (β : ℝ≥0) :
    𝓒.partitionFunction (ofβ β) =
    (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β * 𝓒.energy i)))).real Set.univ := by
  simp only [partitionFunction, μBolt, β_ofβ, neg_mul]

@[sorryful]
lemma paritionFunction_hasFDerivAt (T : Temperature) (hT : T.1 ≠ 0) :
    let F' : ℝ → ι → ℝ →L[ℝ] ℝ := fun T i => rexp (-(1 / (kB * T)) * 𝓒.energy i) •
    (fderiv ℝ (fun T => (- (1 / (kB * T)) * 𝓒.energy i)) T)
    HasFDerivAt (𝕜 := ℝ)
      (fun T => (𝓒.partitionFunction ∘ Real.toNNReal) T) (∫ (i :ι), F' T i ∂𝓒.μ) T := by
  refine HasFDerivAt.congr_of_eventuallyEq
    (f := fun T => ∫ i, exp (- (1 / (kB * T)) * 𝓒.energy i) ∂𝓒.μ) ?_ ?_
  have h0 (i : ι) : HasFDerivAt (𝕜 := ℝ) (fun T => (- (1 / (kB * T)) * 𝓒.energy i))
    (fderiv ℝ (fun T => (- (1 / (kB * T)) * 𝓒.energy i)) T.toReal) T.toReal := by
    refine DifferentiableAt.hasFDerivAt ?_
    refine DifferentiableAt.fun_mul ?_ ?_
    · refine differentiableAt_fun_neg_iff.mpr ?_
      refine DifferentiableAt.fun_div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · simp_all
        apply And.intro
        · exact kB_neq_zero
        · simpa [Temperature.toReal] using hT
    · fun_prop
  let F' : ℝ → ι → ℝ →L[ℝ] ℝ := fun T i => rexp (-(1 / (kB * T)) * 𝓒.energy i) •
    (fderiv ℝ (fun T => (- (1 / (kB * T)) * 𝓒.energy i)) T)
  have h (i : ι) : HasFDerivAt (𝕜 := ℝ) (fun (T : ℝ) => rexp (-(1 / (kB * T)) * 𝓒.energy i))
    (F' T.toReal i) T.toReal := HasFDerivAt.exp (h0 i)
  let F : ℝ → ι → ℝ := fun T i => exp (- (1 / (kB * T)) * 𝓒.energy i)
  change HasFDerivAt (𝕜 := ℝ) (fun T => ∫ i, F T i ∂𝓒.μ) (∫ (i :ι), F' T i ∂𝓒.μ) T
  · sorry
  · sorry

end CanonicalEnsemble
