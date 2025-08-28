/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import HopfieldNet.Papers.Hopfield82.ContentAddressableMemory
import HopfieldNet.Papers.Hopfield82.FaultTolerance
import HopfieldNet.Papers.Hopfield82.EnergyConvergence
import Mathlib.Data.Fintype.Basic

/-!
# Example Implementation of Hopfield's 1982 Model

This module provides concrete examples that demonstrate the key concepts from Hopfield's 1982 paper.
It implements a small Hopfield network and shows how it functions as a content-addressable memory.

## Main Examples

* `smallNetwork`: A 4-neuron Hopfield network storing 2 patterns
* `patternRetrieval`: Demonstration of retrieving patterns from partial information
* `patternCapacity`: Analysis of storage capacity in relation to network size
* `faultToleranceDemo`: Demonstration of robustness to component failures

## References

* Hopfield, J.J. (1982). Neural networks and physical systems with emergent collective
  computational abilities. Proceedings of the National Academy of Sciences, 79(8), 2554-2558.
-/

namespace HopfieldExample

open Hopfield82 NeuralNetwork State Matrix Finset

/-! ### Small Example Network -/

/--
`smallNetwork` creates a small Hopfield network with 4 neurons that stores 2 patterns.
The patterns are `[1, 1, -1, -1]` and `[-1, 1, -1, 1]`, which are orthogonal to each other.
-/
def smallNetwork : Params (HopfieldNetwork ℚ (Fin 4)) :=
  let patterns : Fin 2 → (HopfieldNetwork ℚ (Fin 4)).State :=
    ![{ act := ![1, 1, -1, -1], hp := by decide },
      { act := ![-1, 1, -1, 1], hp := by decide }];

  Hebbian patterns

/--
`hammingDistance` calculates the number of bits that differ between two states.
-/
def hammingDistance {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Nonempty U] [DecidableEq R] [DecidableEq U] [Fintype U]
    (s₁ s₂ : (HopfieldNetwork R U).State) : ℕ :=
  card {i | s₁.act i ≠ s₂.act i}

/--
`updateWithNoise` creates a corrupted version of a pattern by flipping a specified
number of bits randomly.

For simplicity in this example, we deterministically flip the first `numBits` bits.
-/
def updateWithNoise {R : Type} {n : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq (Fin n)] [Nonempty (Fin n)]
    (s : (HopfieldNetwork R (Fin n)).State) (numBits : ℕ) : (HopfieldNetwork R (Fin n)).State :=
  if numBits = 0 then s else
    { act := λ i => if i.val < numBits then -s.act i else s.act i,
      hp := by
        intro i
        by_cases h_cond : i.val < numBits
        · simp only [h_cond, if_true]
          rcases s.hp i with h_s_act_eq_1 | h_s_act_eq_neg_1
          · rw [h_s_act_eq_1]; simp
          · rw [h_s_act_eq_neg_1]; simp
        · simp only [h_cond, if_false]
          exact s.hp i
    }
/--
`pattern1` is the first pattern stored in the small network: `[1, 1, -1, -1]`.
-/
def pattern1 : (HopfieldNetwork ℚ (Fin 4)).State :=
  { act := ![1, 1, -1, -1], hp := by decide }

/--
`pattern2` is the second pattern stored in the small network: `[-1, 1, -1, 1]`.
-/
def pattern2 : (HopfieldNetwork ℚ (Fin 4)).State :=
  { act := ![-1, 1, -1, 1], hp := by decide }

/--
`useq_cyclic_example` is a cyclic update sequence for the 4-neuron network.
It cycles through neurons 0, 1, 2, 3 in order.
-/
def useq_cyclic_example : ℕ → Fin 4 :=
  λ i => ⟨i % 4, by apply Nat.mod_lt; exact Nat.zero_lt_succ 3⟩

/--
Proof that the update sequence is cyclic.
-/
lemma useq_cyclic_example_is_cyclic : cyclic useq_cyclic_example := by
  unfold cyclic
  constructor
  · intro u
    use u.val
    simp only [useq_cyclic_example]
    have h : u.val % 4 = u.val := by
      apply Nat.mod_eq_of_lt
      exact u.2
    simp [h]
  · intros i j h_mod
    simp only [Fintype.card_fin] at h_mod
    exact Fin.eq_of_val_eq h_mod

/--
`useq_cyclic_example_is_fair` proves that the cyclic update sequence is fair.
-/
lemma useq_cyclic_example_is_fair : fair useq_cyclic_example :=
  cycl_Fair useq_cyclic_example useq_cyclic_example_is_cyclic

/-! ### Pattern Retrieval Example -/

/--
`demonstrateRetrieval` shows how the Hopfield network retrieves a stored pattern
from a corrupted version with noise.

This example explicitly demonstrates the content-addressable memory property
described in the paper.
-/
def demonstrateRetrieval (pattern : (HopfieldNetwork ℚ (Fin 4)).State) (numBitsFlipped : ℕ) :
    (HopfieldNetwork ℚ (Fin 4)).State :=
  let corruptedPattern := updateWithNoise pattern numBitsFlipped;
  HopfieldNet_stabilize smallNetwork corruptedPattern useq_cyclic_example useq_cyclic_example_is_fair

/-! ### Pattern Orthogonality -/

/--
`patternsAreOrthogonal` proves that the two patterns stored in our small network
are orthogonal to each other (their dot product is zero), which is a key requirement
for reliable storage and retrieval in Hopfield networks, as discussed in the paper.
-/
theorem patternsAreOrthogonal : dotProduct pattern1.act pattern2.act = 0 := by
  unfold dotProduct pattern1 pattern2

  -- Expand the sum into individual terms
  have sum_expansion : ∑ i : Fin 4, pattern1.act i * pattern2.act i =
      pattern1.act 0 * pattern2.act 0 +
      pattern1.act 1 * pattern2.act 1 +
      pattern1.act 2 * pattern2.act 2 +
      pattern1.act 3 * pattern2.act 3 := by
    exact Fin.sum_univ_four fun i ↦ pattern1.act i * pattern2.act i
  rw [@Fin.sum_univ_four]

  -- Evaluate each term manually
  have p1_0 : pattern1.act 0 = 1 := rfl
  have p1_1 : pattern1.act 1 = 1 := rfl
  have p1_2 : pattern1.act 2 = -1 := rfl
  have p1_3 : pattern1.act 3 = -1 := rfl

  have p2_0 : pattern2.act 0 = -1 := rfl
  have p2_1 : pattern2.act 1 = 1 := rfl
  have p2_2 : pattern2.act 2 = -1 := rfl
  have p2_3 : pattern2.act 3 = 1 := rfl

  rw [Rat.add_assoc]

  -- Simplify the arithmetic
  norm_num

/-! ### Demonstration of Energy Function -/

/--
`energyDecreases` demonstrates that the energy of the Hopfield network decreases
(or remains the same) with each update, as proven in the paper.

This function returns a list of energy values as the network evolves from a
corrupted pattern to the stored pattern.
-/
def energyDecreases (pattern : (HopfieldNetwork ℚ (Fin 4)).State) (numBitsFlipped : ℕ) :
    List ℚ :=
  let corruptedPattern := updateWithNoise pattern numBitsFlipped;
  let maxSteps := 10;  -- Limit to avoid infinite loops

  let rec computeEnergySequence (s : (HopfieldNetwork ℚ (Fin 4)).State) (step : ℕ) : List ℚ :=
    if step = 0 then [s.E smallNetwork]
    else
      let nextS := s.Up smallNetwork (useq_cyclic_example step);
      s.E smallNetwork :: computeEnergySequence nextS (step - 1);

  computeEnergySequence corruptedPattern maxSteps

/-! ### Analysis of Pattern Capacity -/

/--
`theoreticalCapacity` calculates the theoretical maximum number of patterns
that can be stored in a Hopfield network with N neurons.

From the paper (p.2556): "About 0.15 N states can be simultaneously remembered
before error in recall is severe."
-/
noncomputable def theoreticalCapacity (N : ℕ) : ℕ :=
  Nat.floor (0.15 * (N : ℝ))

/-! ### Fault Tolerance Demonstration -/

/--
`demonstrateFaultTolerance` shows how the Hopfield network maintains functionality
even when some neurons are removed, as discussed in the paper.

This function simulates the removal of a specified number of neurons and tests
whether the network can still correctly retrieve the stored patterns.
-/
noncomputable def demonstrateFaultTolerance (numNeuronsRemoved : ℕ) (_ : numNeuronsRemoved ≤ 4) : Bool :=
  -- Use h to ensure we don't exceed the number of neurons in our network
  let neuronSet : Finset (Fin 4) := Finset.filter (fun i => i.val < min numNeuronsRemoved (by exact
    numNeuronsRemoved)) Finset.univ;

  -- Create a modified network with some neurons removed
  let modifiedNetwork := DeleteNeurons neuronSet.toList smallNetwork;

  -- Test if the patterns are still stable in the modified network
  let isPattern1Stable := isStable modifiedNetwork pattern1;
  let isPattern2Stable := isStable modifiedNetwork pattern2;

  isPattern1Stable && isPattern2Stable

/-! ### Demonstration of Content-Addressable Memory -/

/--
`contentAddressableMemoryDemo` creates a Hopfield network that functions as a
content-addressable memory, as described in the paper.

It shows that the network can retrieve complete patterns from partial information.
-/
def contentAddressableMemoryDemo : Bool :=
  -- Create two patterns with sufficient Hamming distance
  let p1 := pattern1;
  let p2 := pattern2;

  -- Create Hopfield network that stores these patterns
  let network := smallNetwork;

  -- Test retrieval with 1 bit flipped for each pattern
  let test1 := HopfieldNet_stabilize network (updateWithNoise p1 1) useq_cyclic_example useq_cyclic_example_is_fair;
  let test2 := HopfieldNet_stabilize network (updateWithNoise p2 1) useq_cyclic_example useq_cyclic_example_is_fair;

  -- Check if the network correctly retrieves the original patterns
  (hammingDistance test1 p1 = 0) && (hammingDistance test2 p2 = 0)

end HopfieldExample
