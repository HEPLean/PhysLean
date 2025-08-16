/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.BoltzmannMachine.Core

open Finset Matrix NeuralNetwork State ENNReal Real
open PMF MeasureTheory ProbabilityTheory.Kernel Set

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
  [Fintype U] [Nonempty U] [Coe R ℝ]

noncomputable instance : Fintype ((BoltzmannMachine R U).State) := by
  -- States are functions from U to {-1, 1} with a predicate
  let binaryType := {x : R | x = -1 ∨ x = 1}
  have binaryFintype : Fintype binaryType := by
    apply Fintype.ofList [⟨-1, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩]
    intro ⟨x, hx⟩
    simp only [List.mem_singleton, List.mem_cons]
    cases hx with
    | inl h =>
      left
      apply Subtype.ext
      exact h
    | inr h =>
      right
      left
      apply Subtype.ext
      exact h
  let f : ((BoltzmannMachine R U).State) → (U → binaryType) := fun s u =>
    ⟨s.act u, by
      unfold binaryType
      have h := s.hp u
      cases h with
      | inl h_pos => right; exact h_pos
      | inr h_neg => left; exact h_neg⟩
  have f_inj : Function.Injective f := by
    intro s1 s2 h_eq
    apply @NeuralNetwork.ext
    intro u
    have h := congr_fun h_eq u
    have hval : (f s1 u).val = (f s2 u).val := congr_arg Subtype.val h
    exact hval
  exact Fintype.ofInjective f f_inj

noncomputable instance : Fintype (StateBM R U) := by
  dsimp [StateBM]
  exact inferInstance

namespace BoltzmannMachine

instance (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U] :
  MeasurableSpace ((BoltzmannMachine R U).State) := ⊤

instance : MeasurableSpace (StateBM R U) := inferInstance

instance : DiscreteMeasurableSpace (StateBM R U) :=
  show DiscreteMeasurableSpace ((BoltzmannMachine R U).State) from inferInstance

/--
The Gibbs transition kernel for a Boltzmann Machine.
Given a current state `s`, it returns a probability measure over the next possible states,
determined by the `BoltzmannMachine.gibbsSamplingStep` function.
-/
noncomputable def gibbsTransitionKernelBM (p : ParamsBM R U) :
    ProbabilityTheory.Kernel (StateBM R U) (StateBM R U) where
  toFun := fun state => (BoltzmannMachine.gibbsSamplingStep p state).toMeasure
  -- For discrete state spaces, any function to measures is measurable
  measurable' := Measurable.of_discrete

/-- The Gibbs transition kernel for a Boltzmann Machine is a Markov Kernel
(preserves probability)-/
instance isMarkovKernel_gibbsTransitionKernelBM (p : ParamsBM R U) :
   ProbabilityTheory.IsMarkovKernel (gibbsTransitionKernelBM p) where
  isProbabilityMeasure := by
    intro s
    simp only [gibbsTransitionKernelBM]
    exact PMF.toMeasure.isProbabilityMeasure (BoltzmannMachine.gibbsSamplingStep p s)

/--
The unnormalized Boltzmann density function for a Boltzmann Machine state.
$ρ(s) = e^{-E(s)/T}$.
-/
noncomputable def boltzmannDensityFnBM (p : ParamsBM R U) (s : StateBM R U) : ENNReal :=
  -- Break this into steps to help type inference
  let energy_val : R := BoltzmannMachine.energy p s
  let energy_real : ℝ := (↑energy_val : ℝ)
  let temp_real : ℝ := (↑(p.T) : ℝ)
  ENNReal.ofReal (Real.exp (-energy_real / temp_real))

/--
The partition function (normalizing constant) for the Boltzmann Machine.
$Z = \sum_s e^{-E(s)/T}$.
-/
noncomputable def partitionFunctionBM (p : ParamsBM R U) : ENNReal :=
  ∑ s : StateBM R U, boltzmannDensityFnBM p s -- Sum over all states in the Fintype

/--
The partition function is positive and finite, provided T > 0.
-/
lemma partitionFunctionBM_pos_finite (p : ParamsBM R U) [Nonempty (StateBM R U)] :
    0 < partitionFunctionBM p ∧ partitionFunctionBM p < ⊤ := by
  constructor
  · -- Proof of 0 < Z
    apply ENNReal.sum_pos
    · exact Finset.univ_nonempty
    · intro s _hs
      unfold boltzmannDensityFnBM
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · -- Proof of Z < ⊤
    unfold partitionFunctionBM
    rw [sum_lt_top]
    intro s _hs
    unfold boltzmannDensityFnBM
    exact ENNReal.ofReal_lt_top

/--
The Boltzmann distribution for a Boltzmann Machine.
This is the stationary distribution for the Gibbs sampling process.
$\pi(s) = \frac{1}{Z} e^{-E(s)/T}$.
Defined as a measure with density `boltzmannDensityFnBM / partitionFunctionBM`
with respect to the counting measure on the finite state space.
-/
noncomputable def boltzmannDistributionBM (p : ParamsBM R U) [Nonempty (StateBM R U)] :
    Measure (StateBM R U) :=
  let density := fun s => boltzmannDensityFnBM p s / partitionFunctionBM p
  let Z_pos_finite := partitionFunctionBM_pos_finite p
  if hZ_zero : partitionFunctionBM p = 0 then by {
    -- This case should not happen due to Z_pos_finite.1
    exfalso; exact Z_pos_finite.1.ne' hZ_zero
  } else if hZ_top : partitionFunctionBM p = ⊤ then by {
    -- This case should not happen due to Z_pos_finite.2
    exfalso; exact Z_pos_finite.2.ne hZ_top
  } else
    @Measure.withDensity (StateBM R U) _ Measure.count density

-- Cleaner definition relying on the proof that Z is good
noncomputable def boltzmannDistributionBM' (p : ParamsBM R U) : Measure (StateBM R U) :=
  @Measure.withDensity (StateBM R U) _ Measure.count
    (fun s => boltzmannDensityFnBM p s / partitionFunctionBM p)

-- Prove it's a probability measure
instance isProbabilityMeasure_boltzmannDistributionBM
    [ Nonempty (StateBM R U)]  (p : ParamsBM R U) :
    IsProbabilityMeasure (boltzmannDistributionBM' p) := by
  constructor
  -- Need to show: μ Set.univ = 1
  have h : boltzmannDistributionBM' p Set.univ =
    ∫⁻ s, boltzmannDensityFnBM p s / partitionFunctionBM p ∂Measure.count := by
    -- For withDensity μ f, applying to a set gives integral of f over that set
    simp only [boltzmannDistributionBM', withDensity_apply]
    -- This is a discrete space, so integral becomes a sum
    simp only [MeasurableSpace.measurableSet_top, withDensity_apply, Measure.restrict_univ]
  rw [h]
  -- For counting measure on finite type, integral is sum over all elements
  rw [MeasureTheory.lintegral_count]
  -- For fintype, tsum becomes finite sum
  rw [tsum_fintype]
  have h_sum_div : ∑ s, boltzmannDensityFnBM p s / partitionFunctionBM p =
    (∑ s, boltzmannDensityFnBM p s) / partitionFunctionBM p := by
    have hpos := (partitionFunctionBM_pos_finite p).1.ne'
    have hlt := (partitionFunctionBM_pos_finite p).2.ne
    simp only [ENNReal.div_eq_inv_mul]
    rw [← mul_sum]
  rw [h_sum_div]
  -- The numerator sum is exactly the definition of the partition function
  rw [← partitionFunctionBM]
  -- So we get Z/Z = 1
  exact ENNReal.div_self (partitionFunctionBM_pos_finite p).1.ne'
    (partitionFunctionBM_pos_finite p).2.ne
