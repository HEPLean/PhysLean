/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Core
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform

/-!
# Boltzmann Machine Neural Network

This file defines Boltzmann Machines (BMs), a type of stochastic
recurrent neural network with symmetric connectivity between units and no self-connections.
This module extends the deterministic Hopfield network with stochastic dynamics: a fully‐connected,
symmetric weight network without self‐loops and binary activations `{1, ‐1}`.
We implement the Boltzmann Machine inside our `NeuralNetwork` framework, providing:

• `BoltzmannMachine` : the network instance
• `ParamsBM`, `StateBM` : parameter and state types
• `energy` / `localField` / `probNeuronIsOne` : key statistics
• `gibbsUpdateSingleNeuron` / `gibbsSamplingStep` : Gibbs sampler

## Mathematics

Boltzmann Machines have binary neurons (±1) with probability of activation determined by:
- Energy function: $E(s) = -\frac{1}{2}\sum_{u,v, u \neq v} w_{u,v}s_u s_v - \sum_u \theta_u s_u$
- Probability distribution: $P(s) \propto \exp(-E(s)/T)$ where $T$ is the temperature parameter
- Local field for neuron $u$: $L_u(s) = \sum_{v \neq u} w_{u,v}s_v + \theta_u$
- Probability of neuron $u$ being 1: $P(s_u = 1) = \frac{1}{1 + \exp(-2L_u(s)/T)}$

The network uses Gibbs sampling to generate samples from the underlying probability distribution.
-/
open Finset Matrix NeuralNetwork State ENNReal Real PMF

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U]

omit [IsStrictOrderedRing R] in
lemma BM_pact_of_HNfact (θ val : R) :
  (fun act : R => act = 1 ∨ act = -1) (HNfact θ val) := by
  unfold HNfact
  split_ifs
  · left; rfl
  · right; rfl

variable [Coe R ℝ]


/--
`BoltzmannMachine` defines a Boltzmann Machine neural network.
It extends `HopfieldNetwork` with specific properties:
- Neurons are fully connected (except to themselves).
- All neurons are both input and output neurons.
- Weights are symmetric, and self-weights are zero.
- Activation is binary (1 or -1).
-/
abbrev BoltzmannMachine (R U : Type) [Field R] [LinearOrder R]
  [IsStrictOrderedRing R] [DecidableEq U] [Nonempty U] [Fintype U] : NeuralNetwork R U :=
{ (HopfieldNetwork R U) with
  Adj := fun u v => u ≠ v,
  Ui := Set.univ, Uo := Set.univ, Uh := ∅,
  hU := by simp only [Set.univ, Set.union_self, Set.union_empty],
  hUi := Ne.symm Set.empty_ne_univ, hUo := Ne.symm Set.empty_ne_univ,
  hhio := Set.empty_inter (Set.univ ∪ Set.univ),
  pw := fun w => w.IsSymm ∧ ∀ u, w u u = 0,
  κ1 := fun _ => 0, κ2 := fun _ => 1,
  fnet := fun u w_u pred _ => HNfnet u w_u pred,
  fact := fun u (_current_act_val : R) (net_input_val : R) (θ_vec : Vector R 1) =>
    HNfact (θ_vec.get 0) net_input_val,  fout := fun _ act => act,
  pact := fun act => act = (1 : R) ∨ act = (-1 : R), -- This is the pact for BoltzmannMachine
  hpact := fun _ _ _ _ _ _ _ _ => BM_pact_of_HNfact _ _
}

/--
Parameters for a Boltzmann Machine.
-/
structure ParamsBM (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] where
  /-- The weight matrix of the Boltzmann Machine. -/
  w : Matrix U U R
  /-- Proof that the weight matrix satisfies the properties required by `BoltzmannMachine.pw`. -/
  hpw : (BoltzmannMachine R U).pw w
  /-- A function mapping each neuron to its threshold value. -/
  θ : U → R
  /-- The temperature parameter of the Boltzmann Machine. -/
  T : R
  /-- Proof that the temperature `T` is positive. -/
  hT_pos : T > 0

/--
`StateBM` is an alias for the state of a `BoltzmannMachine`.
It represents the activation values of all neurons in the network.
-/
abbrev StateBM (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  (BoltzmannMachine R U).State

namespace BoltzmannMachine

/--
Calculates the energy of a state `s` in a Boltzmann Machine.

The energy is defined as:
$$E(s) = -\frac{1}{2}\sum_{u,v, u \neq v} w_{u,v}s_u s_v - \sum_u \theta_u s_u$$
where $w$ is the weight matrix, $s$ is the state (activations), and $\theta$ are the thresholds.
-/
def energy (p : ParamsBM R U) (s : StateBM R U) : R :=
  - (1 / (2 : R)) * (∑ u, ∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act u * s.act v)
  - (∑ u, p.θ u * s.act u)

/--
Calculates the local field for a neuron `u` in a Boltzmann Machine.

The local field is the sum of weighted inputs from other neurons plus the neuron's own threshold:
$$L_u(s) = \sum_{v \neq u} w_{u,v}s_v + \theta_u$$
where $w$ is the weight matrix, $s$ is the state (activations),
and $\theta_u$ is the threshold for neuron $u$.
-/
def localField (p : ParamsBM R U) (s : StateBM R U) (u : U) : R :=
  (∑ v ∈ Finset.univ.filter (fun v' => v' ≠ u), p.w u v * s.act v) + p.θ u

/--
Calculates the probability of neuron `u` being in state `1` (activated).

The probability is given by the sigmoid function of the local field:
$$P(s_u = 1) = \frac{1}{1 + \exp(-2L_u(s)/T)}$$
where $L_u(s)$ is the local field for neuron $u$ and $T$ is the temperature.
-/
noncomputable def probNeuronIsOne (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : ℝ :=
  let L_u : ℝ := ↑(localField p s u)
  let T_R : ℝ := ↑(p.T)
  (1 : ℝ) / (1 + Real.exp (- (2 * L_u / T_R)))

/-!
## Probability of a Neuron Being One

This section defines properties related to the probability of a specific neuron being in state '1'
in a Boltzmann Machine.
-/

/-- The probability of a neuron `u` being in state '1' is always non-negative. -/
lemma probNeuronIsOne_nonneg (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : probNeuronIsOne p s u ≥ 0 := by
  simp only [probNeuronIsOne, div_nonneg_iff]
  left
  constructor
  · norm_num
  · positivity

/-- The probability of a neuron `u` being in state '1' is always less than or equal to 1. -/
lemma probNeuronIsOne_le_one (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : probNeuronIsOne p s u ≤ 1 := by
  unfold probNeuronIsOne
  apply div_le_one_of_le₀
  · have h : 0 < Real.exp (-(2 * ↑(localField p s u) / ↑p.T)) := Real.exp_pos _
    linarith
  · have h1 : 0 < Real.exp (-(2 * ↑(localField p s u) / ↑p.T)) := Real.exp_pos _
    linarith

/--
Updates a single neuron `u` in state `s` according to the Gibbs distribution.

The neuron's new state (1 or -1) is chosen probabilistically based on `probNeuronIsOne`.
Returns a probability mass function over the possible next states.
-/
noncomputable def gibbsUpdateSingleNeuron (p : ParamsBM R U)
  (s : StateBM R U) (u : U) : PMF (StateBM R U) :=
  let prob_one_R : ℝ := probNeuronIsOne p s u
  let prob_one_ennreal := ENNReal.ofReal prob_one_R
  have h_prob_ennreal_le_one : prob_one_ennreal ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (probNeuronIsOne_le_one p s u)
  PMF.bernoulli prob_one_ennreal h_prob_ennreal_le_one >>= fun takes_value_one =>
    let new_val : R := if takes_value_one then (1 : R) else (-1 : R)
    PMF.pure
      { act := fun v => if v = u then new_val else s.act v
      , hp := fun v => by
          by_cases hv : v = u
          · subst hv
            dsimp [new_val]
            split_ifs with h
            · exact Or.inl rfl
            · exact Or.inr rfl
            exact False.elim (h rfl)
          · dsimp only; simp [if_neg hv]; exact s.hp v }

/--
Performs one step of Gibbs sampling.

A neuron `u` is chosen uniformly at random from all neurons,
and then its state is updated according to `gibbsUpdateSingleNeuron`.
Returns a probability mass function over the possible next states.
-/
noncomputable def gibbsSamplingStep (p : ParamsBM R U)
  (s : StateBM R U) : PMF (StateBM R U) :=
  let neuron_pmf : PMF U := PMF.uniformOfFintype U
  neuron_pmf >>= fun u => gibbsUpdateSingleNeuron p s u

end BoltzmannMachine
