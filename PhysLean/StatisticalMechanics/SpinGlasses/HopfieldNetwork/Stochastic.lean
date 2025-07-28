/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.NNStochastic
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.StochasticAux
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas

/-
# Stochastic Hopfield Network Implementation

This file defines and proves properties related to a stochastic Hopfield network.
It includes definitions for states, neural network parameters, energy computations,
and stochastic updates using both Gibbs sampling and Metropolis-Hastings algorithms.
- Functions (`StatePMF`, `StochasticDynamics`) representing probability measures over states.
- Key stochastic update operations, including a single-neuron Gibbs update
  (`gibbsUpdateNeuron`, `gibbsUpdateSingleNeuron`) and full-network sampling steps
  (`gibbsSamplingStep`, `gibbsSamplingSteps`) that iterate these updates.
- Definitions (`metropolisDecision`, `metropolisHastingsStep`, `metropolisHastingsSteps`) for
  implementing a Metropolis-Hastings update rule in a Hopfield network.
- A simulated annealing procedure (`simulatedAnnealing`) that adaptively lowers the temperature
  to guide the network into a low-energy configuration.
- Various lemmas (such as `single_site_difference`, `updateNeuron_preserves`, and
  `gibbs_probs_sum_one`) ensuring correctness and consistency of the update schemes.
- Utility definitions and proofs, including creation of valid parameters
    (`mkArray_creates_valid_hopfield_params`),
  verification of adjacency (`all_nodes_adjacent`), total variation distance
  (`total_variation_distance`), partition function (`partitionFunction`), and more.
-/
open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U] (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State)
  [Coe R ℝ] (T : ℝ)

/-- Performs a Gibbs update on a single neuron `u` of the state `s`.
    The update probability depends on the energy change associated with flipping the neuron's state,
    parameterized by the temperature `T`. -/
noncomputable def NN.State.gibbsUpdateNeuron [Coe R ℝ] (T : ℝ) (u : U) : PMF ((HopfieldNetwork R U).State) :=
  let h_u := s.net wθ u
  let ΔE := 2 * h_u * s.act u
  let p_flip := ENNReal.ofReal (Real.exp (-(↑ΔE) / T)) / (1 + ENNReal.ofReal (Real.exp (-(↑ΔE) / T)))
  let p_flip_le_one : p_flip ≤ 1 := by
    simp only [p_flip]
    let a := ENNReal.ofReal (Real.exp (-(↑ΔE) / T))
    have h_a_nonneg : 0 ≤ a := zero_le a
    have h_denom_ne_zero : 1 + a ≠ 0 := by
      intro h
      have h1 : 0 ≤ 1 + a := zero_le (1 + a)
      have h2 : 1 + a = 0 := h
      simp_all only [zero_le, add_eq_zero, one_ne_zero, ENNReal.ofReal_eq_zero, false_and, a, ΔE, h_u, p_flip]
    have h_sum_ne_top : (1 + a) ≠ ⊤ := by
      apply ENNReal.add_ne_top.2
      constructor
      · exact ENNReal.one_ne_top
      · apply ENNReal.ofReal_ne_top
    rw [ENNReal.div_le_iff h_denom_ne_zero h_sum_ne_top]
    simp only [one_mul, h_u, ΔE, a, p_flip]
    exact le_add_self
  PMF.bind (PMF.bernoulli p_flip p_flip_le_one) $ λ should_flip =>
    PMF.pure $ if should_flip then s.Up wθ u else s

/-- Update a single neuron according to Gibbs sampling rule -/
noncomputable def NN.State.gibbsUpdateSingleNeuron (u : U) : PMF ((HopfieldNetwork R U).State) :=
  -- Calculate local field for the neuron
  let local_field := s.net wθ u
  -- Calculate probabilities based on Boltzmann distribution
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  -- Create PMF with normalized probabilities
  let total : ENNReal := probs true + probs false
  let norm_probs : Bool → ENNReal := λ b => probs b / total
  -- Convert Bool to State
  (PMF.map (λ b => if b then
              NN.State.updateNeuron s u 1 (mul_self_eq_mul_self_iff.mp rfl)
            else
              NN.State.updateNeuron s u (-1) (AffineMap.lineMap_eq_lineMap_iff.mp rfl))
    (PMF.ofFintype norm_probs (by
      have h_total : total ≠ 0 := by {
        simp [probs]
        refine ENNReal.inv_ne_top.mp ?_
        have h_exp_pos := Real.exp_pos (local_field * 1 / T)
        have h := ENNReal.ofReal_pos.mpr h_exp_pos
        simp_all only [mul_one, ENNReal.ofReal_pos, mul_ite, mul_neg, ↓reduceIte, Bool.false_eq_true, ne_eq,
          ENNReal.inv_eq_top, add_eq_zero, ENNReal.ofReal_eq_zero, not_and, not_le, isEmpty_Prop, IsEmpty.forall_iff,
          local_field, total, probs]}
      have h_total_ne_top : total ≠ ⊤ := by {simp [probs, total]}
      have h_sum : Finset.sum Finset.univ norm_probs = 1 := by
        calc Finset.sum Finset.univ norm_probs
          = (probs true)/total + (probs false)/total := Fintype.sum_bool fun b ↦ probs b / total
        _ = (probs true + probs false)/total := ENNReal.div_add_div_same
        _ = total/total := by rfl
        _ = 1 := ENNReal.div_self h_total h_total_ne_top
      exact h_sum)))

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

/-- Given a Hopfield Network's parameters, temperature, and current state, performs a single step
of Gibbs sampling by:
1. Uniformly selecting a random neuron
2. Updating that neuron's state according to the Gibbs distribution
-/
noncomputable def NN.State.gibbsSamplingStep : PMF ((HopfieldNetwork R U).State) :=
  -- Uniform random selection of neuron
  let neuron_pmf : PMF U :=
    PMF.ofFintype (λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal))
      (by
        rw [Finset.sum_const, Finset.card_univ]
        rw [ENNReal.div_eq_inv_mul]
        simp only [mul_one]
        have h : (Fintype.card U : ENNReal) ≠ 0 := by
          simp [Fintype.card_pos_iff.mpr inferInstance]
        have h_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        rw [← ENNReal.mul_inv_cancel h h_top]
        simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, ENNReal.natCast_ne_top,
          nsmul_eq_mul])
  -- Bind neuron selection with conditional update
  PMF.bind neuron_pmf $ λ u => NN.State.gibbsUpdateSingleNeuron wθ s T u

instance : Coe ℝ ℝ := ⟨id⟩

/-- Perform a stochastic update on a Pattern representation -/
noncomputable def patternStochasticUpdate
  {n : ℕ} [Nonempty (Fin n)] (weights : Fin n → Fin n → ℝ) (h_diag_zero : ∀ i : Fin n, weights i i = 0)
  (h_sym : ∀ i j : Fin n, weights i j = weights j i) (T : ℝ)
  (pattern : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) (i : Fin n) :
  PMF (NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) :=
  let wθ : Params (HopfieldNetwork ℝ (Fin n)) := {
    w := weights,
    hw := fun u v h => by
      if h_eq : u = v then
        rw [h_eq]
        exact h_diag_zero v
      else
        have h_adj : (HopfieldNetwork ℝ (Fin n)).Adj u v := by
          simp only [HopfieldNetwork]; simp only [ne_eq]
          exact h_eq
        contradiction
    hw' := by
      unfold NeuralNetwork.pw
      exact IsSymm.ext_iff.mpr fun i j ↦ h_sym j i
    σ := fun u => Vector.mk (Array.replicate
      ((HopfieldNetwork ℝ (Fin n)).κ1 u) (0 : ℝ)) rfl,
    θ := fun u => Vector.mk (Array.replicate
      ((HopfieldNetwork ℝ (Fin n)).κ2 u) (0 : ℝ)) rfl
  }
  NN.State.gibbsUpdateSingleNeuron wθ pattern T i

/-- Performs multiple steps of Gibbs sampling in a Hopfield network, starting from
    an initial state. Each step involves:
    1. First recursively applying previous steps (if any)
    2. Then performing a single Gibbs sampling step on the resulting state
    The temperature parameter T controls the randomness of the updates. -/
noncomputable def NN.State.gibbsSamplingSteps (steps : ℕ) : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps+1 => PMF.bind (gibbsSamplingSteps steps) $ λ s' =>
                NN.State.gibbsSamplingStep wθ s' T

/-- Temperature schedule for simulated annealing that decreases exponentially with each step. -/
noncomputable def temperatureSchedule (initial_temp : ℝ) (cooling_rate : ℝ) (step : ℕ) : ℝ :=
  initial_temp * Real.exp (-cooling_rate * step)

/-- Recursively applies Gibbs sampling steps with decreasing temperature according to
    the cooling schedule, terminating when the step count reaches the target number of steps. -/
noncomputable def applyAnnealingSteps (temp_schedule : ℕ → ℝ) (steps : ℕ)
  (step : ℕ) (state : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  if h : step ≥ steps then
    PMF.pure state
  else
    PMF.bind (NN.State.gibbsSamplingStep wθ state (temp_schedule step))
      (applyAnnealingSteps temp_schedule steps (step + 1))
termination_by steps - step
decreasing_by {
  have : step < steps := not_le.mp h
  have : steps - (step + 1) < steps - step := by
    rw [Nat.sub_succ]
    simp_all only [ge_iff_le, not_le, Nat.pred_eq_sub_one, tsub_lt_self_iff, tsub_pos_iff_lt, Nat.lt_one_iff,
      pos_of_gt, and_self]
  exact this
}

/-- `NN.State.simulatedAnnealing` implements the simulated annealing optimization algorithm for a Hopfield Network.
This function performs simulated annealing by starting from an initial state and gradually reducing
the temperature according to an exponential cooling schedule, allowing the system to explore the
state space and eventually settle into a low-energy configuration.
-/
noncomputable def NN.State.simulatedAnnealing
  (initial_temp : ℝ) (cooling_rate : ℝ) (steps : ℕ)
  (initial_state : (HopfieldNetwork R U).State) : PMF ((HopfieldNetwork R U).State) :=
  let temp_schedule := temperatureSchedule initial_temp cooling_rate
  applyAnnealingSteps wθ temp_schedule steps 0 initial_state

/-- Given a HopfieldNetwork with parameters `wθ` and temperature `T`, computes the acceptance probability
for transitioning from a `current` state to a `proposed` state according to the Metropolis-Hastings algorithm.

* If the energy difference (ΔE) is negative or zero, returns 1.0 (always accepts the transition)
* If the energy difference is positive, returns exp(-ΔE/T) following the Boltzmann distribution
-/
noncomputable def NN.State.acceptanceProbability
  (current : (HopfieldNetwork R U).State) (proposed : (HopfieldNetwork R U).State) : ℝ :=
  let energy_diff := proposed.E wθ - current.E wθ
  if energy_diff ≤ 0 then
    1.0  -- Always accept if energy decreases
  else
    Real.exp (-energy_diff / T)  -- Accept with probability e^(-ΔE/T) if energy increases

/-- The partition function for a Hopfield network, defined as the sum over all possible states
of the Boltzmann factor `exp(-E/T)`.
-/
noncomputable def NN.State.partitionFunction : ℝ :=
  ∑ s : (HopfieldNetwork R U).State, Real.exp (-s.E wθ / T)

/-- Metropolis-Hastings single step for Hopfield networks -/
noncomputable def NN.State.metropolisHastingsStep : PMF ((HopfieldNetwork R U).State) :=
  -- Uniform random selection of neuron
  let neuron_pmf : PMF U :=
    PMF.ofFintype (λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal))
      (by
        rw [Finset.sum_const, Finset.card_univ]
        rw [ENNReal.div_eq_inv_mul]
        simp only [mul_one]
        have h : (Fintype.card U : ENNReal) ≠ 0 := by
          simp [Fintype.card_pos_iff.mpr inferInstance]
        have h_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        rw [← ENNReal.mul_inv_cancel h h_top]
        simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, ENNReal.natCast_ne_top,
          nsmul_eq_mul])
  -- Create proposed state by flipping a randomly selected neuron
  let propose : U → PMF ((HopfieldNetwork R U).State) := λ u =>
    let flipped_state :=
      if s.act u = 1 then  -- Assuming 1 and -1 as valid activation values
        NN.State.updateNeuron s u (-1) (Or.inr rfl)
      else
        NN.State.updateNeuron s u 1 (Or.inl rfl)
    let p := NN.State.acceptanceProbability wθ T s flipped_state
    -- Make acceptance decision
    PMF.bind (NN.State.metropolisDecision p) (λ (accept : Bool) =>
      if accept then PMF.pure flipped_state else PMF.pure s)
  -- Combine neuron selection with state proposal
  PMF.bind neuron_pmf propose

/-- Multiple steps of Metropolis-Hastings algorithm for Hopfield networks -/
noncomputable def NN.State.metropolisHastingsSteps (steps : ℕ)
  : PMF ((HopfieldNetwork R U).State) :=
  match steps with
  | 0 => PMF.pure s
  | steps+1 => PMF.bind (metropolisHastingsSteps steps) $ λ s' =>
                NN.State.metropolisHastingsStep wθ s' T

/-- The Boltzmann (Gibbs) distribution over neural network states -/
noncomputable def boltzmannDistribution : ((HopfieldNetwork R U).State → ℝ) :=
  λ s => Real.exp (-s.E wθ / T) / NN.State.partitionFunction wθ T

/-- The transition probability matrix for Gibbs sampling -/
noncomputable def gibbsTransitionProb (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.gibbsSamplingStep wθ s) T s')

/-- The transition probability matrix for Metropolis-Hastings -/
noncomputable def metropolisTransitionProb (s s' : (HopfieldNetwork R U).State) : ℝ :=
  ENNReal.toReal ((NN.State.metropolisHastingsStep wθ s) T s')

/-- Total variation distance between probability distributions -/
noncomputable def total_variation_distance
  (μ ν : (HopfieldNetwork R U).State → ℝ) : ℝ :=
  (1/2) * ∑ s : (HopfieldNetwork R U).State, |μ s - ν s|

/-- For Gibbs updates, given the normalization and probabilities, the sum of normalized probabilities equals 1 -/
lemma gibbs_probs_sum_one
   (v : U) :
  let local_field := s.net wθ v
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total
  ∑ b : Bool, norm_probs b = 1 := by
  intro local_field probs total norm_probs
  have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
    simp only [Fintype.sum_bool]
    exact ENNReal.div_add_div_same
  rw [h_sum]
  have h_total_eq : probs true + probs false = total := by rfl
  rw [h_total_eq]
  have h_total_ne_zero : total ≠ 0 := by
    simp only [total, probs, ne_eq]
    intro h_zero
    have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                     ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero
    exact h1.ne' (add_eq_zero.mp h_sum_zero).1
  have h_total_ne_top : total ≠ ⊤ := by simp [total, probs]
  exact ENNReal.div_self h_total_ne_zero h_total_ne_top

/-- The function that maps boolean values to states in Gibbs sampling -/
def gibbs_bool_to_state_map
  (s : (HopfieldNetwork R U).State) (v : U) : Bool → (HopfieldNetwork R U).State :=
  λ b => if b then
    NN.State.updateNeuron s v 1 (mul_self_eq_mul_self_iff.mp rfl)
  else
    NN.State.updateNeuron s v (-1) (AffineMap.lineMap_eq_lineMap_iff.mp rfl)

/-- The total normalization constant for Gibbs sampling is positive -/
lemma gibbs_total_positive
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  probs true + probs false ≠ 0 := by
  intro probs
  simp only [ne_eq]
  intro h_zero
  have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
    apply ENNReal.ofReal_pos.mpr
    apply Real.exp_pos
  have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                   ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero
  have h_both_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) = 0 ∧
                    ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 :=
    add_eq_zero.mp h_sum_zero
  exact h1.ne' h_both_zero.1

/-- The total normalization constant for Gibbs sampling is not infinity -/
lemma gibbs_total_not_top
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  probs true + probs false ≠ ⊤ := by
  intro probs
  simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, ne_eq, ENNReal.add_eq_top,
    ENNReal.ofReal_ne_top, or_self, not_false_eq_true, probs]

/-- For a positive PMF.map application, there exists a preimage with positive probability -/
lemma pmf_map_pos_implies_preimage {α β : Type} [Fintype α] [DecidableEq β]
  {p : α → ENNReal} (h_pmf : ∑ a, p a = 1) (f : α → β) (y : β) :
  (PMF.map f (PMF.ofFintype p h_pmf)) y > 0 →
  ∃ x : α, p x > 0 ∧ f x = y := by
  intro h_pos
  simp only [PMF.map_apply] at h_pos
  simp_all only [PMF.ofFintype_apply, tsum_eq_filter_sum, gt_iff_lt, filter_sum_pos_iff_exists_pos,
    pmf_map_pos_iff_exists_pos]

/-- For states with positive Gibbs update probability, there exists a boolean variable that
    determines whether the state has activation 1 or -1 at the updated neuron -/
lemma gibbsUpdate_exists_bool (v : U) (s_next : (HopfieldNetwork R U).State) :
  (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
  ∃ b : Bool, s_next = gibbs_bool_to_state_map s v b := by
  intro h_prob_pos
  unfold NN.State.gibbsUpdateSingleNeuron at h_prob_pos
  let local_field_R := s.net wθ v
  let local_field : ℝ := ↑local_field_R
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs : Bool → ENNReal := λ b => probs b / total
  let map_fn : Bool → (HopfieldNetwork R U).State := gibbs_bool_to_state_map s v
  have h_sum_eq_1 : ∑ b : Bool, norm_probs b = 1 := by
      have h_total_ne_zero : total ≠ 0 := gibbs_total_positive local_field T
      have h_total_ne_top : total ≠ ⊤ := gibbs_total_not_top local_field T
      calc Finset.sum Finset.univ norm_probs
        = (probs true)/total + (probs false)/total :=
          Fintype.sum_bool fun b ↦ probs b / total
      _ = (probs true + probs false)/total := ENNReal.div_add_div_same
      _ = total/total := by rfl
      _ = 1 := ENNReal.div_self h_total_ne_zero h_total_ne_top
  let base_pmf := PMF.ofFintype norm_probs h_sum_eq_1
  have ⟨b, _, h_map_eq⟩ := pmf_map_pos_implies_preimage h_sum_eq_1 map_fn s_next h_prob_pos
  use b
  exact Eq.symm h_map_eq

/-- For states with positive probability under gibbsUpdateSingleNeuron,
    they must be one of exactly two possible states (with neuron v set to 1 or -1) -/
@[simp]
lemma gibbsUpdate_possible_states (v : U) (s_next : (HopfieldNetwork R U).State) :
  (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
  s_next = NN.State.updateNeuron s v 1 (mul_self_eq_mul_self_iff.mp rfl) ∨
  s_next = NN.State.updateNeuron s v (-1)
    (AffineMap.lineMap_eq_lineMap_iff.mp rfl) := by
  intro h_prob_pos
  obtain ⟨b, h_eq⟩ := gibbsUpdate_exists_bool wθ s T v s_next h_prob_pos
  cases b with
  | false =>
    right
    unfold gibbs_bool_to_state_map at h_eq
    rw [@Std.Tactic.BVDecide.Normalize.if_eq_cond] at h_eq
    exact h_eq
  | true =>
    left
    unfold gibbs_bool_to_state_map at h_eq
    rw [@Std.Tactic.BVDecide.Normalize.if_eq_cond] at h_eq
    exact h_eq

/-- Gibbs update preserves states at non-updated sites -/
@[simp]
lemma gibbsUpdate_preserves_other_neurons
  (v w : U) (h_neq : w ≠ v) :
  ∀ s_next, (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 →
    s_next.act w = s.act w := by
  intro s_next h_prob_pos
  have h_structure := gibbsUpdate_possible_states wθ s T v s_next h_prob_pos
  cases h_structure with
  | inl h_pos =>
    rw [h_pos]
    exact updateNeuron_preserves s v w 1 (mul_self_eq_mul_self_iff.mp rfl) h_neq
  | inr h_neg =>
    rw [h_neg]
    exact updateNeuron_preserves s v w (-1)
      (AffineMap.lineMap_eq_lineMap_iff.mp rfl) h_neq

/-- The probability mass function for a binary choice (true/false)
    has sum 1 when properly normalized -/
lemma pmf_binary_norm_sum_one (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total
  ∑ b : Bool, norm_probs b = 1 := by
  intro probs total norm_probs
  have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
    simp only [Fintype.sum_bool]
    exact ENNReal.div_add_div_same
  rw [h_sum]
  have h_total_ne_zero : total ≠ 0 := by
    simp only [total, probs, ne_eq]
    intro h_zero
    have h1 : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.exp_pos
    have h_sum_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) +
                      ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := h_zero
    have h_both_zero : ENNReal.ofReal (Real.exp (local_field * 1 / T)) = 0 ∧
                      ENNReal.ofReal (Real.exp (local_field * (-1) / T)) = 0 := by
      exact add_eq_zero.mp h_sum_zero
    exact h1.ne' h_both_zero.1
  have h_total_ne_top : total ≠ ⊤ := by
    simp [total, probs]
  exact ENNReal.div_self h_total_ne_zero h_total_ne_top

/-- The normalization factor in Gibbs sampling is the sum of Boltzmann
    factors for both possible states -/
lemma gibbs_normalization_factor
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  total = ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal
    (Real.exp (-local_field / T)) := by
  intro probs total
  simp only [probs, total]
  simp only [↓reduceIte, mul_one, Bool.false_eq_true, mul_neg, total, probs]

/-- The probability mass assigned to true when using Gibbs sampling -/
lemma gibbs_prob_true
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total
  norm_probs true = ENNReal.ofReal (Real.exp (local_field / T)) /
    (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal
      (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs]
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, total, probs, norm_probs]
  rw [h_total]
  congr
  simp only [↓reduceIte, mul_one, total, norm_probs, probs]

/-- The probability mass assigned to false when using Gibbs sampling -/
lemma gibbs_prob_false
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total
  norm_probs false = ENNReal.ofReal (Real.exp (-local_field / T)) /
    (ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))) := by
  intro probs total norm_probs
  simp only [norm_probs, probs]
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp [total, probs]
  rw [h_total]
  congr
  simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one, norm_probs, probs, total]


/-- Converts the ratio of Boltzmann factors to ENNReal sigmoid form. -/
@[simp]
lemma ENNReal_exp_ratio_to_sigmoid (x : ℝ) :
  ENNReal.ofReal (Real.exp x) /
  (ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x))) =
  ENNReal.ofReal (1 / (1 + Real.exp (-2 * x))) := by
  have num_pos : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
  have denom_pos : 0 < Real.exp x + Real.exp (-x) := by
    apply add_pos
    · exact Real.exp_pos x
    · exact Real.exp_pos (-x)
  have h1 : ENNReal.ofReal (Real.exp x) /
            (ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x))) =
            ENNReal.ofReal (Real.exp x / (Real.exp x + Real.exp (-x))) := by
    have h_sum : ENNReal.ofReal (Real.exp x) + ENNReal.ofReal (Real.exp (-x)) =
                 ENNReal.ofReal (Real.exp x + Real.exp (-x)) := by
      have exp_neg_pos : 0 ≤ Real.exp (-x) := le_of_lt (Real.exp_pos (-x))
      exact Eq.symm (ENNReal.ofReal_add num_pos exp_neg_pos)
    rw [h_sum]
    exact Eq.symm (ENNReal.ofReal_div_of_pos denom_pos)
  have h2 : Real.exp x / (Real.exp x + Real.exp (-x)) = 1 / (1 + Real.exp (-2 * x)) := by
    have h_denom : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
      have h_exp_diff : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
        rw [← Real.exp_add]; congr; ring
      calc Real.exp x + Real.exp (-x)
          = Real.exp x + Real.exp x * Real.exp (-2 * x) := by rw [h_exp_diff]
        _ = Real.exp x * (1 + Real.exp (-2 * x)) := by rw [mul_add, mul_one]
    rw [h_denom, div_mul_eq_div_div]
    have h_exp_ne_zero : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
    field_simp
  rw [h1, h2]

@[simp]
lemma ENNReal.div_ne_top' {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ 0) :
  a / b ≠ ⊤ := by
  intro h_top
  rw [ENNReal.div_eq_top] at h_top
  rcases h_top with (⟨_, h_right⟩ | ⟨h_left, _⟩);
  exact hb h_right; exact ha h_left

lemma gibbs_prob_positive
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  ENNReal.ofReal (Real.exp (local_field / T)) / total =
    ENNReal.ofReal (1 / (1 + Real.exp (-2 * local_field / T))) := by
  intro probs total
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, total, probs]
  rw [h_total]
  have h_temp : ∀ x, Real.exp (x / T) = Real.exp (x * (1/T)) := by
    intro x; congr; field_simp
  rw [h_temp local_field, h_temp (-local_field)]
  have h_direct :
    ENNReal.ofReal (Real.exp (local_field * (1 / T))) /
    (ENNReal.ofReal (Real.exp (local_field * (1 / T))) +
        ENNReal.ofReal (Real.exp (-local_field * (1 / T)))) =
    ENNReal.ofReal (1 / (1 + Real.exp (-2 * local_field / T))) := by
    have h := ENNReal_exp_ratio_to_sigmoid (local_field * (1 / T))
    have h_rhs : -2 * (local_field * (1 / T)) = -2 * local_field / T := by
      field_simp
    rw [h_rhs] at h
    have neg_equiv : ENNReal.ofReal (Real.exp (-(local_field * (1 / T)))) =
                    ENNReal.ofReal (Real.exp (-local_field * (1 / T))) := by
      congr; ring
    rw [neg_equiv] at h
    exact h
  exact h_direct

/-- The probability of setting a neuron to -1 under Gibbs sampling -/
lemma gibbs_prob_negative
  (local_field : ℝ) (T : ℝ) :
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  ENNReal.ofReal (Real.exp (-local_field / T)) / total =
  ENNReal.ofReal (1 / (1 + Real.exp (2 * local_field / T))) := by
  intro probs total
  have h_total : total = ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T)) := by
    simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, total, probs]
  rw [h_total]
  have h_neg2_neg : -2 * (-local_field / T) = 2 * local_field / T := by ring
  have h_neg_neg : -(-local_field / T) = local_field / T := by ring
  have h_ratio_final : ENNReal.ofReal (Real.exp (-local_field / T)) /
                       (ENNReal.ofReal (Real.exp (local_field / T)) +
                          ENNReal.ofReal (Real.exp (-local_field / T))) =
                       ENNReal.ofReal (1 / (1 + Real.exp (2 * local_field / T))) := by
    have h := ENNReal_exp_ratio_to_sigmoid (-local_field / T)
    have h_exp_neg_neg : ENNReal.ofReal (Real.exp (-(-local_field / T))) =
                         ENNReal.ofReal (Real.exp (local_field / T)) := by congr
    rw [h_exp_neg_neg] at h
    have h_comm : ENNReal.ofReal (Real.exp (-local_field / T)) +
        ENNReal.ofReal (Real.exp (local_field / T)) =
                  ENNReal.ofReal (Real.exp (local_field / T)) +
        ENNReal.ofReal (Real.exp (-local_field / T)) := by
      rw [add_comm]
    rw [h_neg2_neg] at h
    rw [h_comm] at h
    exact h
  exact h_ratio_final

-- Lemma for the probability calculation in the positive case
lemma gibbs_prob_positive_case
   (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  let norm_probs := λ b => if b then
                             ENNReal.ofReal (Real.exp (local_field / T)) / Z
                           else
                             ENNReal.ofReal (Real.exp (-local_field / T)) / Z
  (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (by
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    simp only [norm_probs]
    have h_ratio_sum : ENNReal.ofReal (Real.exp (local_field / T)) / Z +
                       ENNReal.ofReal (Real.exp (-local_field / T)) / Z =
                       (ENNReal.ofReal (Real.exp (local_field / T)) +
                        ENNReal.ofReal (Real.exp (-local_field / T))) / Z := by
      exact ENNReal.div_add_div_same
    simp only [Bool.false_eq_true]
    have h_if_true : (if True then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                      else ENNReal.ofReal (Real.exp (-local_field / T)) / Z) =
                     ENNReal.ofReal (Real.exp (local_field / T)) / Z := by simp

    have h_if_false : (if False then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                       else ENNReal.ofReal (Real.exp (-local_field / T)) / Z) =
                      ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by simp
    rw [h_if_true, h_if_false]
    rw [h_ratio_sum]
    have h_Z_ne_zero : Z ≠ 0 := by
      simp only [ne_eq, add_eq_zero, ENNReal.ofReal_eq_zero, not_and, not_le, Z, norm_probs]
      intros
      exact Real.exp_pos (-Coe.coe local_field / T)
    have h_Z_ne_top : Z ≠ ⊤ := by simp [Z]
    exact ENNReal.div_self h_Z_ne_zero h_Z_ne_top
  ))) (NN.State.updateNeuron s u 1 (Or.inl rfl)) = norm_probs true := by
  intro
  apply pmf_map_update_one

-- Lemma for the probability calculation in the negative case
lemma gibbs_prob_negative_case
   (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) +
      ENNReal.ofReal (Real.exp (-local_field / T))
  let norm_probs := λ b => if b then
                             ENNReal.ofReal (Real.exp (local_field / T)) / Z
                           else
                             ENNReal.ofReal (Real.exp (-local_field / T)) / Z
  (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (by
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    simp only [norm_probs]
    have h_ratio_sum : ENNReal.ofReal (Real.exp (local_field / T)) / Z +
                       ENNReal.ofReal (Real.exp (-local_field / T)) / Z =
                       (ENNReal.ofReal (Real.exp (local_field / T)) +
                          ENNReal.ofReal (Real.exp (-local_field / T))) / Z := by
      exact ENNReal.div_add_div_same
    simp only [Bool.false_eq_true]
    simp only [↓reduceIte, norm_probs]
    rw [h_ratio_sum]
    have h_Z_ne_zero : Z ≠ 0 := by
      simp only [Z, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h
    have h_Z_ne_top : Z ≠ ⊤ := by
      simp only [ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self, not_false_eq_true, Z,
        norm_probs]
    exact ENNReal.div_self h_Z_ne_zero h_Z_ne_top)))
    (NN.State.updateNeuron s u (-1) (Or.inr rfl)) = norm_probs false := by
  intro
  apply pmf_map_update_neg_one

/-- PMF map from boolean values to updated states preserves probability structure -/
lemma gibbsUpdate_pmf_structure
   (u : U) :
  let local_field := s.net wθ u
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  let norm_probs := λ b => probs b / total
  ∀ b : Bool, (PMF.map (gibbs_bool_to_state_map s u) (PMF.ofFintype norm_probs (by
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    have h_ratio_sum : probs true / total + probs false / total =
                      (probs true + probs false) / total := by
      exact ENNReal.div_add_div_same
    rw [h_ratio_sum]
    have h_total_ne_zero : total ≠ 0 := by
      simp only [total, probs, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h
    have h_total_ne_top : total ≠ ⊤ := by simp only [mul_ite, mul_one, mul_neg, ↓reduceIte,
      Bool.false_eq_true, ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self,
      not_false_eq_true, total, probs]
    exact ENNReal.div_self h_total_ne_zero h_total_ne_top
  ))) (gibbs_bool_to_state_map s u b) = norm_probs b := by
  intro local_field probs total norm_probs b_bool
  exact pmf_map_binary_state s u b_bool (fun b => norm_probs b) (by
    have h_sum : ∑ b : Bool, norm_probs b = norm_probs true + norm_probs false := by
      exact Fintype.sum_bool (λ b => norm_probs b)
    rw [h_sum]
    have h_ratio_sum : probs true / total + probs false / total =
                      (probs true + probs false) / total := by
      exact ENNReal.div_add_div_same
    rw [h_ratio_sum]
    have h_total_ne_zero : total ≠ 0 := by
      simp only [total, probs, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h
    have h_total_ne_top : total ≠ ⊤ := by simp only [mul_ite, mul_one, mul_neg, ↓reduceIte,
      Bool.false_eq_true, ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self,
      not_false_eq_true, total, probs]
    exact ENNReal.div_self h_total_ne_zero h_total_ne_top)

/-- The probability of updating a neuron to 1 using Gibbs sampling -/
lemma gibbsUpdate_prob_positive
   (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u 1 (Or.inl rfl)) =
    ENNReal.ofReal (Real.exp (local_field / T)) / Z := by
  intro local_field Z
  unfold NN.State.gibbsUpdateSingleNeuron
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  have h_total_eq_Z : total = Z := by
    simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, total, probs, Z]
  have h_result := pmf_map_update_one s u (fun b => probs b / total) (by
    have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
      simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false,
          not_false_eq_true,sum_insert, sum_singleton, total, probs, Z]
      exact
        ENNReal.div_add_div_same
    rw [h_sum]
    have h_total_ne_zero : total ≠ 0 := by
      simp only [total, probs, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h
    have h_total_ne_top : total ≠ ⊤ := by simp [total, probs]
    exact ENNReal.div_self h_total_ne_zero h_total_ne_top)
  rw [h_result]
  simp only [probs, mul_one_div]
  rw [h_total_eq_Z]
  simp only [if_true, mul_one]

/-- The probability of updating a neuron to -1 using Gibbs sampling -/
lemma gibbsUpdate_prob_negative
   (u : U) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (-1) (Or.inr rfl)) =
    ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
  intro local_field Z
  unfold NN.State.gibbsUpdateSingleNeuron
  let probs : Bool → ENNReal := fun b =>
    let new_act_val := if b then 1 else -1
    ENNReal.ofReal (Real.exp (local_field * new_act_val / T))
  let total := probs true + probs false
  have h_total_eq_Z : total = Z := by
    simp only [mul_ite, mul_one, mul_neg, ↓reduceIte, Bool.false_eq_true, total, probs, Z]
  have h_result := pmf_map_update_neg_one s u (fun b => probs b / total) (by
    have h_sum : ∑ b : Bool, probs b / total = (probs true + probs false) / total := by
      simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false,
          not_false_eq_true, sum_insert, sum_singleton, total, probs, Z]
      exact ENNReal.div_add_div_same
    rw [h_sum]
    have h_total_ne_zero : total ≠ 0 := by
      simp only [total, probs, ne_eq, add_eq_zero]
      intro h
      have h_exp_pos : ENNReal.ofReal (Real.exp (local_field * 1 / T)) > 0 := by
        apply ENNReal.ofReal_pos.mpr
        apply Real.exp_pos
      exact (not_and_or.mpr (Or.inl h_exp_pos.ne')) h
    have h_total_ne_top : total ≠ ⊤ := by
      simp only [mul_ite, mul_one, mul_neg, ↓reduceIte,
        Bool.false_eq_true, ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self,
        not_false_eq_true, total, probs, Z]
    exact ENNReal.div_self h_total_ne_zero h_total_ne_top)
  rw [h_result]
  simp only [probs, one_div_neg_one_eq_neg_one, one_div_neg_one_eq_neg_one]
  rw [h_total_eq_Z]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one, probs, Z, total]

/-- Computes the probability of updating a neuron to a specific value using Gibbs sampling.
- If new_val = 1: probability = exp(local_field/T)/Z
- If new_val = -1: probability = exp(-local_field/T)/Z
where Z is the normalization constant (partition function).
-/
@[simp]
lemma gibbs_update_single_neuron_prob (u : U) (new_val : R)
    (hval : (HopfieldNetwork R U).pact new_val) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u new_val hval) =
    if new_val = 1 then
      ENNReal.ofReal (Real.exp (local_field / T)) / Z
    else
      ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
  intro local_field Z
  by_cases h_val : new_val = 1
  · rw [if_pos h_val]
    have h_update_equiv := gibbs_bool_to_state_map_positive s u new_val hval h_val
    rw [h_update_equiv]
    exact gibbsUpdate_prob_positive wθ s T u
  · rw [if_neg h_val]
    have h_neg_val : new_val = -1 := hopfield_value_dichotomy new_val hval h_val
    have h_update_equiv := gibbs_bool_to_state_map_negative s u new_val hval h_neg_val
    rw [h_update_equiv]
    exact gibbsUpdate_prob_negative wθ s T u

/-- When states differ at site u, the probability of transitioning to s' by updating
    any other site v is zero -/
lemma gibbs_update_zero_other_sites (s s' : (HopfieldNetwork R U).State)
  (u v : U) (h : ∀ w : U, w ≠ u → s.act w = s'.act w) (h_diff : s.act u ≠ s'.act u) :
  v ≠ u → (NN.State.gibbsUpdateSingleNeuron wθ s T v) s' = 0 := by
  intro hv
  have h_act_diff : s'.act u ≠ s.act u := by
    exact Ne.symm h_diff
  have h_s'_diff_update : ∀ new_val hval,
    s' ≠ NN.State.updateNeuron s v new_val hval := by
    intro new_val hval
    by_contra h_eq
    have h_u_eq : s'.act u = (NN.State.updateNeuron s v new_val hval).act u := by
      rw [←h_eq]
    have h_u_preserved : (NN.State.updateNeuron s v new_val hval).act u = s.act u := by
      exact updateNeuron_preserves s v u new_val hval (id (Ne.symm hv))
    rw [h_u_preserved] at h_u_eq
    -- Use h to show contradiction
    have h_s'_neq_s : s' ≠ s := by
      by_contra h_s_eq
      rw [h_s_eq] at h_diff
      exact h_diff rfl
    have h_same_elsewhere := h v hv
    -- Now we have a contradiction: s' differs from s at u but also equals s.act u there
    exact h_act_diff h_u_eq
  by_contra h_pmf_nonzero
  have h_pos_gt_zero : (NN.State.gibbsUpdateSingleNeuron wθ s T v) s' > 0 := by
    exact (PMF.apply_pos_iff (NN.State.gibbsUpdateSingleNeuron wθ s T v) s').mpr h_pmf_nonzero
  have h_structure := gibbsUpdate_possible_states wθ s T v s' h_pos_gt_zero
  cases h_structure with
  | inl h_pos_case =>
    apply h_s'_diff_update 1 (mul_self_eq_mul_self_iff.mp rfl)
    exact h_pos_case
  | inr h_neg_case =>
    apply h_s'_diff_update (-1) (AffineMap.lineMap_eq_lineMap_iff.mp rfl)
    exact h_neg_case

/-- When calculating the transition probability sum, only the term for the
    differing site contributes -/
lemma gibbs_transition_sum_simplification (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_diff : s.act u ≠ s'.act u) :
  let neuron_pmf : PMF U := PMF.ofFintype
    (λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal))
    (by
      simp only [one_div, sum_const, card_univ, nsmul_eq_mul]
      have h_card_ne_zero : (Fintype.card U : ENNReal) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact Fintype.card_ne_zero
      have h_card_ne_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card U)
      rw [← ENNReal.mul_inv_cancel h_card_ne_zero h_card_ne_top])
  let update_prob (v : U) : ENNReal := (NN.State.gibbsUpdateSingleNeuron wθ s T v) s'
  ∑ v ∈ Finset.univ, neuron_pmf v * update_prob v = neuron_pmf u * update_prob u := by
  intro neuron_pmf update_prob
  have h_zero : ∀ v ∈ Finset.univ, v ≠ u → update_prob v = 0 := by
    intro v _ hv
    exact gibbs_update_zero_other_sites wθ T s s' u v h h_diff hv
  apply Finset.sum_eq_single u
  · intro v hv hvu
    rw [h_zero v hv hvu]
    simp only [mul_zero]
  · intro hu
    exfalso
    apply hu
    simp only [mem_univ]

@[simp]
lemma gibbs_update_preserves_other_sites (v u : U) (hvu : v ≠ u) :
  ∀ s_next, (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next > 0 → s_next.act u = s.act u := by
  intro s_next h_pos
  have h_supp : s_next ∈ PMF.support (NN.State.gibbsUpdateSingleNeuron wθ s T v) := by
    exact (PMF.apply_pos_iff (NN.State.gibbsUpdateSingleNeuron wθ s T v) s_next).mp h_pos
  have h_structure := gibbsUpdate_possible_states wθ s T v s_next h_pos
  cases h_structure with
  | inl h_pos =>
    -- Case s_next = updateNeuron s v 1
    rw [h_pos]
    exact updateNeuron_preserves s v u 1 (mul_self_eq_mul_self_iff.mp rfl) (id (Ne.symm hvu))
  | inr h_neg =>
    -- Case s_next = updateNeuron s v (-1)
    rw [h_neg]
    exact
      updateNeuron_preserves s v u (-1) (AffineMap.lineMap_eq_lineMap_iff.mp rfl) (id (Ne.symm hvu))

@[simp]
lemma uniform_neuron_prob {U : Type} [Fintype U] [Nonempty U] (u : U) :
  (1 : ENNReal) / (Fintype.card U : ENNReal) =
  PMF.ofFintype (λ _ : U => (1 : ENNReal) / (Fintype.card U : ENNReal))
    (by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      have h_card_ne_zero : (Fintype.card U : ENNReal) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact Fintype.card_ne_zero
      have h_card_ne_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [ENNReal.div_eq_inv_mul]
      rw [mul_comm]
      rw [← ENNReal.mul_inv_cancel h_card_ne_zero h_card_ne_top]
      rw [ENNReal.inv_mul_cancel_left h_card_ne_zero h_card_ne_top]
      simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
          not_false_eq_true, ENNReal.natCast_ne_top]
      rw [mul_comm]
    ) u := by
  simp only [one_div, PMF.ofFintype_apply]
