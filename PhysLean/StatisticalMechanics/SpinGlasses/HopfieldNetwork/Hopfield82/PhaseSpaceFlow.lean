/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/

import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Stochastic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Hopfield Networks: Formalization of J.J. Hopfield's 1982 Paper

This module formalizes the key mathematical concepts from J.J. Hopfield's 1982 paper
"Neural networks and physical systems with emergent collective computational abilities",
focusing on aspects that are not already covered in the main HopfieldNet formalization.

The paper introduces a model of neural networks with binary neurons and studies their collective
computational properties, particularly as content-addressable memories. The key insights include:

1. The phase space flow and stable states of the network
2. The storage capacity and pattern retrieval capabilities
3. The relationship between energy minimization and memory retrieval
4. Tolerance to noise and component failures

## Main Components

* `PhaseSpaceFlow`: Formalization of phase space flow and attractors
* `MemoryCapacity`: Relationship between memory capacity and error rates
* `MemoryConfusion`: Formalization of how similar memories can interfere
* `FaultTolerance`: Analysis of network robustness to component failures

## References

* Hopfield, J.J. (1982). Neural networks and physical systems with emergent collective
  computational abilities. Proceedings of the National Academy of Sciences, 79(8), 2554-2558.
-/

namespace Hopfield82

open NeuralNetwork State Matrix Finset Real

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]

/-! ### Phase Space Flow -/

/--
A `PhaseSpacePoint` represents a state in the phase space of the Hopfield system.
In the paper, this corresponds to the instantaneous state of all neurons (p.2554):
"A point in state space then represents the instantaneous condition of the system."
-/
abbrev PhaseSpacePoint (R U : Type)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U] :=
  (HopfieldNetwork R U).State

/-- Convert Option to Vector for threshold values --/
def optionToVector (o : Option R) : Vector R 1 :=
  let arr := match o with
    | some v => #[v]
    | none => #[0]
  Vector.mk arr (by
    cases o <;> rfl)

/-- Convert Vector to Option for threshold values --/
def vectorToOption (v : Vector R 1) : Option R :=
  some (v.get 0)

/-- Extract threshold value safely --/
def getThreshold (θ : Option R) : R :=
  match θ with
  | some v => v
  | none => 0

/--
The `localField` for neuron i in state s is the weighted sum of inputs from other neurons,
minus the threshold. This corresponds to ∑j Tij Vj - θi in the paper.
-/

def localField {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U]
  (wθ : Params (HopfieldNetwork R U)) (s : PhaseSpacePoint R U) (i : U) : R :=

  (∑ j ∈ Finset.univ, wθ.w i j * s.act j) - getThreshold (vectorToOption (wθ.θ i))
/--
The `updateRule` defines the neural state update according to the paper's Equation 1:
    Vi → 1 if ∑j Tij Vj > Ui
    Vi → 0 if ∑j Tij Vj < Ui

In our formalization, we use -1 instead of 0 for the "not firing" state.
-/
def updateRule [DecidableEq R] [DecidableEq U] (wθ : Params (HopfieldNetwork R U))
    (s : PhaseSpacePoint R U) (i : U) : R :=
  if localField wθ s i > 0 then 1 else -1

/--
A `PhaseSpaceFlow` describes how the system state evolves over time.
It maps each point in phase space to its successor state after updating one neuron.

From the paper (p.2554): "The equations of motion of the system describe a flow in state space."
-/
def PhaseSpaceFlow [DecidableEq R] [DecidableEq U]
    (wθ : Params (HopfieldNetwork R U)) (useq : ℕ → U) : PhaseSpacePoint R U → PhaseSpacePoint R U :=
  λ (s : PhaseSpacePoint R U) => s.Up wθ (useq 0)

/--
A `FixedPoint` of the phase space flow is a state that does not change under evolution.
In the paper, these correspond to the locally stable states of the network (p.2554):
"Various classes of flow patterns are possible, but the systems of use for memory
particularly include those that flow toward locally stable points..."
-/
def FixedPoint [DecidableEq R] [DecidableEq U] (wθ : Params (HopfieldNetwork R U))
    (s : PhaseSpacePoint R U) : Prop :=
  s.isStable wθ

/--
A `BasinOfAttraction` of a fixed point is the set of all states that converge to it.
In the paper (p.2554): "Then, if the system is started sufficiently near any Xa,
as at X = Xa + Δ, it will proceed in time until X ≈ Xa."
-/
def BasinOfAttraction [DecidableEq R] [DecidableEq U]
    (wθ : Params (HopfieldNetwork R U)) (p : PhaseSpacePoint R U)
    (useq : ℕ → U) (hf : fair useq) : Set (PhaseSpacePoint R U) :=
  {s | ∃ n : ℕ, seqStates wθ s useq n = p ∧ FixedPoint wθ p ∧ convergence_is_fair s useq hf}
  where
    convergence_is_fair (_ : PhaseSpacePoint R U) (useq : ℕ → U) (_ : fair useq) : Prop := fair useq

/--
The `EnergyLandscape` of a Hopfield network is the energy function defined over all possible states.
In the paper, this is the function E defined in Equation 7:
    E = -1/2 ∑∑ Tij Vi Vj
-/
def EnergyLandscape [DecidableEq R] [DecidableEq U] (wθ : Params (HopfieldNetwork R U)) :
  PhaseSpacePoint R U → R := λ (s : PhaseSpacePoint R U) => s.E wθ

@[simp]
lemma up_act_eq_iff_eq {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U]
  {wθ : Params (HopfieldNetwork R U)} {s : (HopfieldNetwork R U).State} {u : U} :
  (s.Up wθ u).act u = s.act u → s.Up wθ u = s := by
  intro h_act_eq
  -- Apply state extensionality
  apply NeuralNetwork.ext
  intro v
  -- Case split on whether v equals u
  by_cases h_v : v = u
  · -- Case v = u: use the hypothesis directly
    rw [h_v, h_act_eq]
  · -- Case v ≠ u: use act_of_non_up lemma
    rw [act_of_non_up wθ h_v]

/--
The `EnergyChange` when updating neuron i is always non-positive,
as proven in the paper with Equation 8.

This theorem formalizes a key result from the paper: the energy function
always decreases (or remains constant) under asynchronous updates.
-/
theorem energy_decrease [DecidableEq R] [DecidableEq U]
    (wθ : Params (HopfieldNetwork R U)) (s : PhaseSpacePoint R U) (i : U) :
  (s.Up wθ i).E wθ ≤ s.E wθ := by
  have h_stab_or_diff : (s.Up wθ i = s) ∨ (s.Up wθ i).act i ≠ s.act i := by
    let s' := s.Up wθ i
    by_cases h : s'.act i = s.act i
    case pos =>
      left
      exact up_act_eq_iff_eq h
    case neg =>
      right
      exact h
  cases h_stab_or_diff with
  | inl h_same =>
    rw [h_same]
  | inr h_diff =>
    exact energy_diff_leq_zero wθ h_diff

/--
This theorem captures the convergence result from the paper:
"Every initial state flows to a limit point (if synchrony is not assumed)."

The proof leverages the HopfieldNet_convergence_fair theorem from the existing codebase.
-/
theorem convergence_to_fixed_point [DecidableEq R] [DecidableEq U]
      (wθ : Params (HopfieldNetwork R U)) (s : PhaseSpacePoint R U)
    (useq : ℕ → U) (hf : fair useq) :
  ∃ (p : PhaseSpacePoint R U) (n : ℕ),
    seqStates wθ s useq n = p ∧ FixedPoint wθ p := by
  obtain ⟨N, hN⟩ := HopfieldNet_convergence_fair s useq hf
  use seqStates wθ s useq N, N
  constructor
  · rfl
  · exact hN
