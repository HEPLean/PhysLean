/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Basic
/-!
# Canonical Ensemble: Thermodynamic Identities and Relations

This file develops relations between the *mathematical* objects defined in
`Basic.lean` and the *physical* thermodynamic quantities, together with
calculus identities for the canonical ensemble.

## Contents Overview

1. Helmholtz Free Energies
   * `mathematicalHelmholtzFreeEnergy`
   * Relation to physical `helmholtzFreeEnergy` with semi–classical correction.

2. Entropy Relations
   * Pointwise logarithm of (mathematical / physical) Boltzmann probabilities.
   * Key identity:
       `differentialEntropy = kB * β * meanEnergy + kB * log Z_math`
   * Fundamental link:
       `thermodynamicEntropy = differentialEntropy - kB * dof * log h`
     (semi–classical correction term).
   * Specializations removing the correction when `dof = 0` or `phaseSpaceUnit = 1`.

3. Fundamental Thermodynamic Identity
   * Proof of `F = U - T S_thermo`.
   * Equivalent rearrangements giving entropy from energies and free energy.
   * Discrete / normalized specialization (no correction).

4. Mean energy as
       `U = - d/dβ log Z_math`
     and likewise with the physical partition function (constant factor cancels).

## Design Notes

* All derivative statements are given as `derivWithin` on `Set.Ioi 0`, matching the physical
  domain β > 0.
* Assumptions (finiteness, integrability) are parameterized to keep lemmas reusable.
* Semi–classical correction appears systematically as
    `kB * dof * log phaseSpaceUnit`.

## References

Same references as `Basic.lean` (Landau–Lifshitz; Tong), especially the identities
`F = U - T S` and `U = -∂_β log Z`.

-/
set_option linter.unusedVariables.funArgs false

namespace CanonicalEnsemble

open MeasureTheory Real Temperature Constants

open scoped Constants ENNReal

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

/-- An intermediate potential defined from the mathematical partition function. See
`helmholtzFreeEnergy` for the physical thermodynamic quantity. -/
noncomputable def mathematicalHelmholtzFreeEnergy (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T)

/-- The relationship between the physical Helmholtz Free Energy and the Helmholtz Potential. -/
lemma helmholtzFreeEnergy_eq_helmholtzMathematicalFreeEnergy_add_correction (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.helmholtzFreeEnergy T = 𝓒.mathematicalHelmholtzFreeEnergy T +
      kB * T.val * 𝓒.dof * Real.log (𝓒.phaseSpaceunit) := by
  have hZ_pos := mathematicalPartitionFunction_pos 𝓒 T
  have h_pow_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  simp_rw [helmholtzFreeEnergy, mathematicalHelmholtzFreeEnergy, partitionFunction,
    Real.log_div hZ_pos.ne' h_pow_pos.ne']
  have h_log_pow : Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof)
      = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    simp
  simp [sub_eq_add_neg, h_log_pow, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

/-- General identity: S_diff = kB β ⟨E⟩ + kB log Z_math.
This connects the differential entropy to the mean energy and the mathematical partition function.
Integrability of `log (probability …)` follows from the pointwise formula. -/
lemma differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.differentialEntropy T = kB * (T.β : ℝ) * 𝓒.meanEnergy T +
      kB * Real.log (𝓒.mathematicalPartitionFunction T) := by
  set Z := 𝓒.mathematicalPartitionFunction T
  have hZpos := mathematicalPartitionFunction_pos 𝓒 T
  have h_log_prob : ∀ i, Real.log (𝓒.probability T i) =
      - (T.β : ℝ) * 𝓒.energy i - Real.log Z := by
    intro i
    have : 0 < Z := hZpos
    rw [probability, Real.log_div (exp_pos _).ne' this.ne', Real.log_exp]
  unfold differentialEntropy
  rw [integral_congr_ae (ae_of_all _ h_log_prob)]
  have h_split :
      (fun i => - (T.β : ℝ) * 𝓒.energy i - Real.log Z)
        = (fun i => (- (T.β : ℝ)) * 𝓒.energy i + (- Real.log Z)) := by
    funext i; ring
  simp_rw [h_split]
  have h_int1 : Integrable (fun _ : ι => - Real.log Z) (𝓒.μProd T) :=
    (integrable_const _)
  have h_intE : Integrable (fun i => (- (T.β : ℝ)) * 𝓒.energy i) (𝓒.μProd T) :=
    (hE.const_mul _)
  rw [integral_add h_intE h_int1,
      integral_const_mul, meanEnergy, integral_const]
  simp [mul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_comm, mul_left_comm, mul_assoc, differentialEntropy, probability,
       mul_comm, mul_left_comm, mul_assoc]

/-- Pointwise logarithm of the Boltzmann probability. -/
lemma log_probability
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    Real.log (𝓒.probability T i)
      = - (β T) * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunction T) := by
  have hZpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  unfold probability
  simp [Real.log_div, hZpos.ne', Real.log_exp, sub_eq_add_neg]

/--  Auxiliary identity: `kB · β = 1 / T`.
`β` is defined as `1 / (kB · T)` (see `Temperature.β`). -/
@[simp]
private lemma kB_mul_beta (T : Temperature) (hT : 0 < T.val) :
    (kB : ℝ) * (T.β : ℝ) = 1 / T.val := by
  have hkB : (kB : ℝ) ≠ 0 := kB_neq_zero
  have hT0 : (T.val : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT)
  field_simp [Temperature.β, hkB, hT0]
  rw [mul_div_mul_left (↑T.val) T.toReal hkB]
  erw [propext (div_eq_one_iff_eq hT0)]

/-- Fundamental relation between thermodynamic and differential entropy:
`S_thermo = S_diff - kB * dof * log h`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_sub_correction
    (T : Temperature)
    (hE : Integrable 𝓒.energy (𝓒.μProd T))
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T
      = 𝓒.differentialEntropy T
        - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  classical
  have hZpos := 𝓒.mathematicalPartitionFunction_pos (T:=T)
  have h_log_prob_point :
      ∀ i, Real.log (𝓒.probability T i)
        = (- (T.β : ℝ)) * 𝓒.energy i
            - Real.log (𝓒.mathematicalPartitionFunction T) := by
    intro i
    have : 0 < 𝓒.mathematicalPartitionFunction T := hZpos
    unfold probability
    simp [Real.log_div (Real.exp_pos _).ne' this.ne', Real.log_exp, sub_eq_add_neg,
          mul_comm, mul_left_comm, mul_assoc]
  have h_log_phys_pt :
      ∀ i, Real.log (𝓒.physicalProbability T i)
        = Real.log (𝓒.probability T i)
            + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit :=
    𝓒.log_physicalProbability (T:=T)
  have h_int_log_prob :
      Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T) := by
    have h_intE :
        Integrable (fun i => (- (T.β : ℝ)) * 𝓒.energy i) (𝓒.μProd T) :=
      hE.const_mul _
    have h_intC :
        Integrable (fun _ : ι => - Real.log (𝓒.mathematicalPartitionFunction T))
          (𝓒.μProd T) := integrable_const _
    have h_eq :
        (fun i => Real.log (𝓒.probability T i))
          =
        (fun i => (- (T.β : ℝ)) * 𝓒.energy i
              + (- Real.log (𝓒.mathematicalPartitionFunction T))) := by
      funext i
      simp [h_log_prob_point i, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [h_eq] using h_intE.add h_intC
  have h_int_const :
      Integrable (fun _ : ι =>
          (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) (𝓒.μProd T) :=
    integrable_const _
  have h_int_rewrite :
      ∫ i, Real.log (𝓒.physicalProbability T i) ∂ 𝓒.μProd T
        =
      ∫ i, (Real.log (𝓒.probability T i)
              + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) ∂ 𝓒.μProd T := by
    simp_all only [neg_mul, physicalProbability_def, integrable_add_iff_integrable_right']
  have h_int_const_eval :
      ∫ _i, (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit ∂ 𝓒.μProd T
        = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    simp [integral_const]
  unfold thermodynamicEntropy differentialEntropy
  rw [h_int_rewrite,
      integral_add h_int_log_prob h_int_const,
      h_int_const_eval]
  have : -kB *
          (∫ i, Real.log (𝓒.probability T i) ∂ 𝓒.μProd T +
            (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit)
        =
        (-kB * ∫ i, Real.log (𝓒.probability T i) ∂ 𝓒.μProd T)
          - kB * (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    ring
  simp [this, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]

/-- No semiclassical correction when `dof = 0`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_dof_zero
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (h0 : 𝓒.dof = 0)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
  have h :=
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction
      (T:=T) (hE:=hE)
  simp_all

/-- No semiclassical correction when `phase_space_unit = 1`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_phase_space_unit_one
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (h1 : 𝓒.phaseSpaceunit = 1)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
  have h' :=
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction
      (T:=T) (hE:=hE)
  simp_all
/-

## Thermodynamic Identities

-/

/-!

## The Fundamental Thermodynamic Identity

-/

/-- The Helmholtz free energy `F` is related to the mean energy `U` and the absolute
thermodynamic entropy `S` by the identity `F = U - TS`. This theorem shows that the
statistically-defined quantities in this framework correctly satisfy this principle of
thermodynamics. -/
theorem helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
    (T : Temperature) (hT : 0 < T.val)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.helmholtzFreeEnergy T
      = 𝓒.meanEnergy T - T.val * 𝓒.thermodynamicEntropy T := by
  classical
  have hSdiff :=
    𝓒.differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ
      (T:=T) (hE:=hE)
  have hScorr :=
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction
      (T:=T) (hE:=hE)
  have hkβ : (kB : ℝ) * (T.β : ℝ) = 1 / T.val :=
    kB_mul_beta T hT
  have hTne : (T.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hS_form :
      𝓒.thermodynamicEntropy T
        = kB * (T.β : ℝ) * 𝓒.meanEnergy T
            + kB * Real.log (𝓒.mathematicalPartitionFunction T)
            - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
    calc
      𝓒.thermodynamicEntropy T
          = 𝓒.differentialEntropy T
              - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := hScorr
      _ = (kB * (T.β : ℝ) * 𝓒.meanEnergy T
              + kB * Real.log (𝓒.mathematicalPartitionFunction T))
            - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
              simp [hSdiff]
      _ = _ := by
              simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
                    mul_comm, mul_left_comm, mul_assoc]
  have hkβT : T.val * (kB * (T.β : ℝ)) = 1 := by
    simp [hkβ, hTne]
  have h_rhs :
      𝓒.meanEnergy T - T.val * 𝓒.thermodynamicEntropy T
        = -kB * T.val *
            (Real.log (𝓒.mathematicalPartitionFunction T)
              - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) := by
    have := hS_form
    calc
      𝓒.meanEnergy T - T.val * 𝓒.thermodynamicEntropy T
          = 𝓒.meanEnergy T -
              T.val *
                (kB * (T.β : ℝ) * 𝓒.meanEnergy T
                  + kB * Real.log (𝓒.mathematicalPartitionFunction T)
                  - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit) := by
                rw [this]
      _ = 𝓒.meanEnergy T
            - T.val * (kB * (T.β : ℝ)) * 𝓒.meanEnergy T
            - T.val * kB * Real.log (𝓒.mathematicalPartitionFunction T)
            + T.val * kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
              ring
      _ = 𝓒.meanEnergy T - 1 * 𝓒.meanEnergy T
            - T.val * kB * Real.log (𝓒.mathematicalPartitionFunction T)
            + T.val * kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
              simp [hkβT, mul_comm, mul_left_comm, mul_assoc]
      _ = -kB * T.val *
            (Real.log (𝓒.mathematicalPartitionFunction T)
              - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) := by
              simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
              ring
  have hZpos := 𝓒.mathematicalPartitionFunction_pos T
  have hhpos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hF_rewrite :
      𝓒.helmholtzFreeEnergy T
        = -kB * T.val *
            (Real.log (𝓒.mathematicalPartitionFunction T)
              - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) := by
    have h_log_pow :
        Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof)
          = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by simp
    simp [helmholtzFreeEnergy, partitionFunction,
          Real.log_div hZpos.ne' hhpos.ne',
          Real.log_pow, h_log_pow,
          sub_eq_add_neg,
          mul_add, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  rw [hF_rewrite, h_rhs]

/-- **Theorem: Helmholtz identity with semi–classical correction term**.
Physical identity (always true for `T > 0`):
  (U - F)/T   = S_thermo
and:
  S_thermo = S_diff - kB * dof * log h.
Hence:
  S_diff = (U - F)/T + kB * dof * log h.
This theorem gives the correct relation for the (mathematical / differential) entropy.
(Removing the correction is only valid in normalized discrete cases
with `dof = 0` (or `phaseSpaceUnit = 1`).) -/
theorem differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.differentialEntropy T
      = (𝓒.meanEnergy T - 𝓒.helmholtzFreeEnergy T) / T.val
        + kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  classical
  have hS :=
    differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ (𝓒:=𝓒) (T:=T) hE
  set E := 𝓒.meanEnergy T
  set Zmath := 𝓒.mathematicalPartitionFunction T
  set Zphys := 𝓒.partitionFunction T
  have Tne : (T.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hkβ : kB * (T.β : ℝ) = 1 / (T.val : ℝ) := by
    unfold Temperature.β
    change kB * (1 / (kB * (T.val : ℝ))) = 1 / (T.val : ℝ)
    field_simp [Constants.kB_neq_zero, Tne]
  have hS' :
      𝓒.differentialEntropy T = E / T.val + kB * Real.log Zmath := by
    rw [hS, hkβ]
    simp [E, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hZdef : Zmath = Zphys * 𝓒.phaseSpaceunit ^ 𝓒.dof := by
    unfold Zmath Zphys partitionFunction
    have hne : (𝓒.phaseSpaceunit ^ 𝓒.dof) ≠ 0 :=
      pow_ne_zero _ (ne_of_gt 𝓒.hPos)
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne]
  have hpow_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hZmath_pos :
      0 < Zmath := (mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T))
  have hZphys_pos :
      0 < Zphys := by
    have : Zphys = Zmath / 𝓒.phaseSpaceunit ^ 𝓒.dof := by
      simp [Zphys, partitionFunction, div_eq_mul_inv]
      exact Or.symm (Or.inr rfl)
    have hden_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := hpow_pos
    simp [this, hZmath_pos, hden_pos]
  have hlog :
      Real.log Zmath
        = Real.log Zphys + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    have hx : 0 < Zphys := hZphys_pos
    have hy : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := hpow_pos
    have hlog_pow :
        Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof)
          = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
      simp
    calc
      Real.log Zmath
          = Real.log (Zphys * 𝓒.phaseSpaceunit ^ 𝓒.dof) := by simp [hZdef, mul_comm,
            mul_left_comm, mul_assoc]
      _ = Real.log Zphys + Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof) := by
        have hx0 : Zphys ≠ 0 := ne_of_gt hx
        have hy0 : 𝓒.phaseSpaceunit ^ 𝓒.dof ≠ 0 := ne_of_gt hy
        simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.log_mul hx0 hy0)
      _ = Real.log Zphys + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by simp [hlog_pow]
  have hS_phys :
      𝓒.differentialEntropy T
        = E / T.val + kB * Real.log Zphys
          + kB * (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    rw [hS', hlog]
    ring
  have hEF :
      (E - 𝓒.helmholtzFreeEnergy T) / T.val
        = E / T.val + kB * Real.log Zphys := by
    simp [sub_eq_add_neg, division_def, mul_add,
      add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc, E, Zphys, Tne]
  calc
    𝓒.differentialEntropy T
        = (E / T.val + kB * Real.log Zphys)
            + kB * (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
              simp [hS_phys, add_comm, add_left_comm, add_assoc]
    _ = (E - 𝓒.helmholtzFreeEnergy T) / T.val
            + kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
              rw [hEF]

/-- Discrete / normalized specialization of the previous theorem.
If either `dof = 0` (no semiclassical correction) or `phaseSpaceUnit = 1`
(so `log h = 0`), the correction term vanishes and we recover the bare Helmholtz identity
for the (differential) entropy. -/
lemma differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (hNorm : 𝓒.dof = 0 ∨ 𝓒.phaseSpaceunit = 1) :
    𝓒.differentialEntropy T
      = (𝓒.meanEnergy T - 𝓒.helmholtzFreeEnergy T) / T.val := by
  have hmain :=
    differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction
      (𝓒:=𝓒) (T:=T) hT hE
  rcases hNorm with hDof | hUnit
  · simp [hmain, hDof]
  · simp [hmain, hUnit]

/-- Chain rule convenience lemma for `log ∘ f` on a set. -/
lemma hasDerivWithinAt_log_comp
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t)) ((f x)⁻¹ * f') s x :=
  (Real.hasDerivAt_log hx).comp_hasDerivWithinAt x hf

/-- A version rewriting the derivative value with `1 / f x`. -/
lemma hasDerivWithinAt_log_comp'
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t))
      ((1 / f x) * f') s x := by
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc]
    using (hasDerivWithinAt_log_comp (f:=f) (f':=f') (s:=s) (x:=x) hf hx)

lemma integral_bolt_eq_integral_mul_exp
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (φ : ι → ℝ) :
    ∫ x, φ x ∂ 𝓒.μBolt T
      = ∫ x, φ x * Real.exp (-T.β * 𝓒.energy x) ∂ 𝓒.μ := by
  unfold μBolt
  set f : ι → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-T.β * 𝓒.energy x))
  have hf_meas : Measurable f := by
    fun_prop
  have hf_lt_top : ∀ᵐ x ∂ 𝓒.μ, f x < ∞ := by
    simp [f]
  have h :=
    integral_withDensity_eq_integral_toReal_smul
      (μ := 𝓒.μ) hf_meas hf_lt_top φ
  have h_toReal : ∀ x, (f x).toReal = Real.exp (-T.β * 𝓒.energy x) := by
    intro x
    have h_nonneg : (0 : ℝ) ≤ Real.exp (-T.β * 𝓒.energy x) :=
      (Real.exp_pos _).le
    simpa [f, h_nonneg] using ENNReal.toReal_ofReal h_nonneg
  have h' :
    (∫ x, φ x ∂ 𝓒.μ.withDensity f) =
      ∫ x, φ x * Real.exp (-T.β * 𝓒.energy x) ∂ 𝓒.μ := by
    simpa [h_toReal, smul_eq_mul, mul_comm] using h
  simpa [f, mul_comm] using h'

set_option linter.unusedVariables false in
/--  A specialization of `integral_bolt_eq_integral_mul_exp`
to the energy observable. -/
lemma integral_energy_bolt
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    ∫ x, 𝓒.energy x ∂ 𝓒.μBolt T
      = ∫ x, 𝓒.energy x * Real.exp (-T.β * 𝓒.energy x) ∂ 𝓒.μ := by
  exact integral_bolt_eq_integral_mul_exp 𝓒 T 𝓒.energy

/-- The mean energy can be expressed as a ratio of integrals. -/
lemma meanEnergy_eq_ratio_of_integrals
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.meanEnergy T =
      (∫ i, 𝓒.energy i * Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) /
        (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := by
  classical
  unfold meanEnergy μProd
  have h_scale :
      ∫ x, 𝓒.energy x ∂ ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)
        = ((𝓒.μBolt T Set.univ)⁻¹).toReal * ∫ x, 𝓒.energy x ∂ 𝓒.μBolt T := by
    simp
  have h_energy_bolt_raw :=
    integral_energy_bolt (𝓒:=𝓒) (T:=T)
  have h_den :
      (𝓒.μBolt T Set.univ).toReal
        = ∫ x, Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ := by
    simpa [CanonicalEnsemble.mathematicalPartitionFunction]
      using (mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=T))
  have h_inv_toReal :
      ((𝓒.μBolt T Set.univ)⁻¹).toReal
        = 1 / (𝓒.μBolt T Set.univ).toReal := by
    simp [one_div, ENNReal.toReal_inv]
  calc
    ∫ x, 𝓒.energy x ∂ ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)
        = ((𝓒.μBolt T Set.univ)⁻¹).toReal * ∫ x, 𝓒.energy x ∂ 𝓒.μBolt T := h_scale
    _ = ((𝓒.μBolt T Set.univ)⁻¹).toReal *
          (∫ x, 𝓒.energy x * Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ) := by
          simp [h_energy_bolt_raw]
    _ = (1 / (𝓒.μBolt T Set.univ).toReal) *
          (∫ x, 𝓒.energy x * Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ) := by
          simp [h_inv_toReal]
    _ = (∫ x, 𝓒.energy x * Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ) /
          (∫ x, Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ) := by
          simp [h_den, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The mean energy is the negative derivative of the logarithm of the
(mathematical) partition function with respect to β = 1/(kB T).
see: Tong (§1.3.2, §1.3.3), L&L (§31, implicitly, and §36)
Here the derivative is a `derivWithin` over `Set.Ioi 0`
since `β > 0`. -/
lemma meanEnergy_eq_neg_deriv_log_mathZ_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.meanEnergy T =
      - (derivWithin
          (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ))
          (Set.Ioi 0) (T.β : ℝ)) := by
  classical
  set f : ℝ → ℝ := fun β => ∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ
  have hβ_pos : 0 < (T.β : ℝ) := beta_pos T hT_pos
  have hZpos : 0 < f (T.β : ℝ) := by
    have hZ := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
    have hEq : f (T.β : ℝ) = 𝓒.mathematicalPartitionFunction T := by
      simp [f, mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=T)]
    simpa [hEq] using hZ
  have h_log :
      HasDerivWithinAt
        (fun β : ℝ => Real.log (f β))
        ((1 / f (T.β : ℝ)) *
            (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ))
        (Set.Ioi 0) (T.β : ℝ) := by
    have h₁ :=
      CanonicalEnsemble.hasDerivWithinAt_log_comp'
        (hf := h_deriv) (hx := (ne_of_gt hZpos))
    simpa [f] using h₁
  have h_mean_ratio :
      𝓒.meanEnergy T =
        (∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) /
          (∫ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) := by
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc]
      using meanEnergy_eq_ratio_of_integrals (𝓒:=𝓒) (T:=T)
  have h_mem : (T.β : ℝ) ∈ Set.Ioi (0:ℝ) := hβ_pos
  have hUD : UniqueDiffWithinAt ℝ (Set.Ioi (0:ℝ)) (T.β : ℝ) :=
    isOpen_Ioi.uniqueDiffWithinAt h_mem
  have h_deriv_log :
      derivWithin (fun β : ℝ => Real.log (f β)) (Set.Ioi 0) (T.β : ℝ)
        = (1 / f (T.β : ℝ)) *
            (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) :=
    h_log.derivWithin hUD
  have h_f_eval :
      f (T.β : ℝ) = ∫ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ := rfl
  have h_ratio :
      (∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) /
          (∫ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)
        = (1 / f (T.β : ℝ)) *
            (∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) := by
    simp [h_f_eval, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  calc
    𝓒.meanEnergy T = _ := h_mean_ratio
    _ = (1 / f (T.β : ℝ)) *
            (∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) := h_ratio
    _ = - ((1 / f (T.β : ℝ)) *
            (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)) := by ring
    _ = - (derivWithin
            (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ))
            (Set.Ioi 0) (T.β : ℝ)) := by
          rw [h_deriv_log]

open Set

open scoped Topology Filter ENNReal Constants

-- we keep this linter here and below for potential use where stronger assumptions ae needed
set_option linter.unusedVariables false in

/-- Helper: equality (on `Set.Ioi 0`) between the β–parametrized logarithm of the
physical partition function and the β–parametrized logarithm of the *mathematical*
partition function up to the (β–independent) semiclassical correction. This is used only
to identify derivatives (the correction drops).
We add the hypothesis `h_fin` giving finiteness of the Boltzmann measure for every β > 0
(as needed to ensure the mathematical partition function is strictly positive). -/
private lemma log_phys_eq_log_math_sub_const_on_Ioi
    (𝓒 : CanonicalEnsemble ι) [NeZero 𝓒.μ]
    (h_fin :
      ∀ β > 0,
        IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β))))
    (h_const :
        (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit =
        (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := rfl) :
    Set.EqOn
      (fun β : ℝ =>
        Real.log (𝓒.partitionFunction (Temperature.ofβ (Real.toNNReal β))))
      (fun β : ℝ =>
        Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit)
      (Set.Ioi (0 : ℝ)) := by
  intro β hβ
  have hβpos : 0 < β := hβ
  have hβnn : Real.toNNReal β = β := by
    simp [Real.toNNReal, hβpos.le]
  have _inst : IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β))) :=
    h_fin β hβpos
  have hZpos :
      0 < 𝓒.mathematicalPartitionFunction (Temperature.ofβ (Real.toNNReal β)) := by
    simpa [hβnn] using
      (mathematicalPartitionFunction_pos (𝓒:=𝓒)
        (T:=Temperature.ofβ (Real.toNNReal β)))
  have h_pow_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have h_log_pow :
      Real.log (𝓒.phaseSpaceunit ^ 𝓒.dof)
        = (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    simp
  have :
      Real.log (𝓒.partitionFunction (Temperature.ofβ (Real.toNNReal β))) =
        -( (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit)
          + Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ) := by
    have h_integral_pos : 0 < ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ := by
      have h_eq : ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ =
        ∫ i, Real.exp (-(Real.toNNReal β).val * 𝓒.energy i) ∂ 𝓒.μ := by
        simp [hβnn]
      rw [h_eq]
      simp [mathematicalPartitionFunction_eq_integral
        (𝓒:=𝓒) (T:=Temperature.ofβ (Real.toNNReal β))] at hZpos
      simp [hZpos]
    have h_beta_eq : (Temperature.ofβ (Real.toNNReal β)).β = Real.toNNReal β := by
      simp_all only [gt_iff_lt, mem_Ioi, coe_toNNReal', sup_eq_left, log_pow, neg_mul, β_ofβ]
    rw [partitionFunction_def,
        mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=Temperature.ofβ (Real.toNNReal β)),
        h_beta_eq,
        hβnn,
        Real.log_div h_integral_pos.ne' h_pow_pos.ne',
        h_log_pow]
    ring
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

set_option linter.unusedVariables false in
/-- Derivative equality needed in `meanEnergy_eq_neg_deriv_log_Z_of_beta`.
Adds `h_fin` (finiteness of the Boltzmann measure for every β > 0). -/
private lemma derivWithin_log_phys_eq_derivWithin_log_math
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h_integrable :
        ∀ β > 0, Integrable (fun i => Real.exp (-β * 𝓒.energy i)) 𝓒.μ)
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β)))) :
    derivWithin
      (fun β : ℝ => Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))))
      (Set.Ioi 0) (T.β : ℝ)
    =
    derivWithin
      (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ))
      (Set.Ioi 0) (T.β : ℝ) := by
  classical
  set C : ℝ := (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit
  have h_eq :
      Set.EqOn
        (fun β : ℝ =>
          Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))))
        (fun β : ℝ =>
          Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ) - C)
        (Set.Ioi (0:ℝ)) :=
    log_phys_eq_log_math_sub_const_on_Ioi (𝓒:=𝓒) (h_fin:=h_fin) rfl
  have h_const_deriv :
      derivWithin (fun _ : ℝ => C) (Set.Ioi 0) (T.β : ℝ) = 0 := by
    simp
  set F_phys :=
    fun β : ℝ => Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))) with hF_phys
  set F_math :=
    fun β : ℝ =>
      Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ) with hF_math
  have h_eq' :
      Set.EqOn F_phys (fun β => F_math β - C) (Set.Ioi (0:ℝ)) := by
    simpa [F_phys, F_math] using h_eq
  have h_mem : (T.β : ℝ) ∈ Set.Ioi (0:ℝ) := beta_pos T hT_pos
  have h_congr :
      derivWithin F_phys (Set.Ioi 0) (T.β : ℝ)
        = derivWithin (fun β => F_math β - C) (Set.Ioi 0) (T.β : ℝ) := by
    apply derivWithin_congr
    · exact h_eq
    · exact h_eq h_mem
  have h_sub :
      derivWithin (fun β => F_math β - C) (Set.Ioi 0) (T.β : ℝ)
        = derivWithin F_math (Set.Ioi 0) (T.β : ℝ) := by
    simp [F_math, sub_eq_add_neg, h_const_deriv]; rw [@derivWithin_add_const]
  simpa [F_phys, F_math] using h_congr.trans h_sub

set_option linter.unusedVariables false in
/-- The mean energy can also be expressed as the negative derivative of the logarithm of the
*physical* partition function with respect to β. This follows from the fact that the physical and
mathematical partition functions differ only by a constant factor, which vanishes upon
differentiation. -/
theorem meanEnergy_eq_neg_deriv_log_Z_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h_integrable :
        ∀ β > 0, Integrable (fun i => Real.exp (-β * 𝓒.energy i)) 𝓒.μ)
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β))))
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.meanEnergy T =
      - (derivWithin
          (fun β : ℝ => Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))))
          (Set.Ioi 0) (T.β : ℝ)) := by
  have h_math :=
    𝓒.meanEnergy_eq_neg_deriv_log_mathZ_of_beta T hT_pos h_deriv
  have h_dw :=
    derivWithin_log_phys_eq_derivWithin_log_math
      (𝓒:=𝓒) (T:=T) hT_pos h_integrable h_fin
  rw [h_dw]; exact h_math

end CanonicalEnsemble
