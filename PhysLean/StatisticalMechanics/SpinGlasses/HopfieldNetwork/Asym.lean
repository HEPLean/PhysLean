/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Core
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Asymmetric Hopfield Networks

This module provides an implementation of asymmetric Hopfield networks, which are neural networks
with potentially non-symmetric weight matrices. Unlike standard Hopfield networks that require
symmetric weights, asymmetric networks can converge under certain conditions.

## Main Components

* `AsymmetricHopfieldNetwork`: A neural network structure with asymmetric weights
* `updateStateAsym`: A function for updating states in the asymmetric case
* `localFieldAsym`: A function computing local fields in asymmetric networks
* `energyAsym`: A modified energy function for asymmetric networks

## Mathematical Details

The implementation is based on the decomposition of asymmetric weight matrices into:
* An antisymmetric component A (where A_{ij} = -A_{ji})
* A positive definite symmetric component S
* A non-negative diagonal constraint

This decomposition allows us to analyze the dynamics and convergence properties
of Hopfield networks with asymmetric weights.
-/


open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [StarRing R] [DecidableEq U] [Fintype U] [Nonempty U]

/-- A matrix `A : Matrix n n α` is "antisymmetric" if `Aᵀ = -A`. -/
def Matrix.IsAntisymm [Neg α] (A : Matrix n n α) : Prop := Aᵀ = -A

@[simp]
lemma Matrix.IsAntisymm.ext_iff [Neg α] {A : Matrix n n α} :
  A.IsAntisymm ↔ ∀ i j, A j i = -A i j := by
  simp [Matrix.IsAntisymm, Matrix.ext_iff]
  exact Eq.congr_right rfl

/--
`AsymmetricHopfieldNetwork` defines a Hopfield network with asymmetric weights.
Unlike standard Hopfield networks where weights must be symmetric,
this variant allows for asymmetric weights that can be decomposed into
an antisymmetric part and a positive definite symmetric part.

The network has:
- Fully connected neurons (each neuron is connected to all others)
- No self-connections (zero diagonal in weight matrix)
- Asymmetric weights (w_ij can differ from w_ji)
- Weights that can be decomposed into antisymmetric and positive definite components
-/
abbrev AsymmetricHopfieldNetwork (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
   [DecidableEq U] [Nonempty U] [Fintype U] [StarRing R] : NeuralNetwork R U where
  /- The adjacency relation between neurons `u` and `v`, defined as `u ≠ v`. -/
  Adj u v := u ≠ v
  /- The set of input neurons, defined as the universal set. -/
  Ui := Set.univ
  /- The set of output neurons, defined as the universal set. -/
  Uo := Set.univ
  /- A proof that the intersection of the input and output sets is empty. -/
  hhio := Set.empty_inter (Set.univ ∪ Set.univ)
  /- The set of hidden neurons, defined as the empty set. -/
  Uh := ∅
  /- A proof that all neurons are in the universal set. -/
  hU := by simp only [Set.mem_univ, Set.union_self, Set.union_empty]
  /- A proof that the input set is not equal to the empty set. -/
  hUi := Ne.symm Set.empty_ne_univ
  /- A proof that the output set is not equal to the empty set. -/
  hUo := Ne.symm Set.empty_ne_univ
  /- The weights can be decomposed into antisymmetric and positive definite parts -/
  pw := fun w =>
    ∃ (A S : Matrix U U R),
            A.IsAntisymm ∧                   -- A is antisymmetric
            Matrix.PosDef S ∧               -- S is positive definite
            w = A + S ∧                     -- Decomposition of the weight matrix
            (∀ i, w i i ≥ 0)                -- Non-negative diagonal
  /- κ₁ is 0 for every neuron. -/
  κ1 _ := 0
  /- κ₂ is 1 for every neuron. -/
  κ2 _ := 1
  /- The network function for neuron `u`, given weights `w` and predecessor states `pred`. -/
  fnet u w pred _ := HNfnet u w pred
  /- The activation function for neuron `u`, given input and threshold `θ`. -/
  fact u (_current_act_val : R) (net_input_val : R) (θ_vec : Vector R 1) := HNfact (θ_vec.get 0) net_input_val  /- The output function, given the activation state `act`. -/
  fout _ act := HNfout act
  /- A predicate that the activation state `act` is either 1 or -1. -/
  pact act := act = 1 ∨ act = -1
  /- A proof that the activation state of neuron `u`
    is determined by the threshold `θ` and the network function. -/
  hpact w _ _ _ θ act _ u :=
    ite_eq_or_eq ((θ u).get 0 ≤ HNfnet u (w u) fun v => HNfout (act v)) 1 (-1)

/--
Extracts the antisymmetric and symmetric components from parameters that
satisfy the asymmetric condition.

Parameters:
- wθ: The Hopfield network parameters
- hw': Proof that the parameters satisfy the asymmetric condition

Returns:
- A pair (A, S) where A is antisymmetric, S is positive definite, and w = A + S
-/
noncomputable def getAsymmetricDecomposition (wθ : Params (AsymmetricHopfieldNetwork R U))
    (_ : ∃ (A S : Matrix U U R), A.IsAntisymm ∧ Matrix.PosDef S ∧ wθ.w = A + S ∧ (∀ i, wθ.w i i ≥ 0)) :
    Matrix U U R × Matrix U U R :=
  let w := wθ.w
  let one_half : R := (1 : R) / (2 : R)
  let A_matrix := one_half • (w - wᵀ)
  let S_matrix := one_half • (w + wᵀ)
  (A_matrix, S_matrix)

/--
Computes the local field for a neuron in an asymmetric Hopfield network.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The current state of the network
- i: The index of the neuron

Returns:
- The local field (weighted sum of inputs minus threshold)
-/
def localFieldAsym [Nonempty U] (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i : U) : R :=
  (∑ j ∈ Finset.univ, wθ.w i j * s.act j) - (wθ.θ i).get 0

/--
Updates a neuron state according to asymmetric update rules.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The current state of the network
- i: The index of the neuron to update

Returns:
- A new state with the selected neuron updated
-/
def updateStateAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i : U) : State (AsymmetricHopfieldNetwork R U) :=
  { act := fun j => if j = i then
             let lf := localFieldAsym wθ s i
             if lf ≤ 0 then -1 else 1
           else s.act j,
    hp := fun j => by
      by_cases h : j = i
      · subst h
        by_cases h_lf : localFieldAsym wθ s j ≤ 0
        · simp [h_lf]
        · simp [h_lf]
      · simp [h]
        exact s.hp j
  }

/--
Returns the updated activation value of a neuron after applying the asymmetric update rule.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The current state of the network
- i: The index of the neuron

Returns:
- The activation value after update
-/
def updatedActValue (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i : U) : R :=
  (updateStateAsym wθ s i).act i

/--
Creates a sequence of state updates for an asymmetric Hopfield network.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The initial state
- useq: A sequence of neurons to update

Returns:
- A function mapping each time step to the corresponding state
-/
def seqStatesAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (useq : ℕ → U) : ℕ → State (AsymmetricHopfieldNetwork R U)
  | 0 => s
  | n+1 => updateStateAsym wθ (seqStatesAsym wθ s useq n) (useq n)

/--
Checks if a state is stable in an asymmetric Hopfield network.
A state is stable if no single-neuron update changes the state.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The state to check

Returns:
- True if the state is stable, false otherwise
-/
def isStableAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) : Prop :=
  ∀ i, updateStateAsym wθ s i = s

/--
Get the energy of an asymmetric Hopfield network for a specific state.
This is a modified energy function designed for asymmetric networks.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The current state of the network

Returns:
- The energy value of the network
-/
def energyAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) : R :=
  let w := wθ.w;
  let θ := fun i => (wθ.θ i).get 0;
  -- For asymmetric networks, we use a modified energy function
  -1/2 * ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, w i j * s.act i * s.act j -
  ∑ i ∈ Finset.univ, θ i * s.act i

/--
Potential function for asymmetric Hopfield networks at time step k.
This function is used to analyze the dynamics of the network during updates.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The current state of the network
- k: The current time step
- useq: A sequence of neurons to update

Returns:
- The potential value of the network
-/
def potentialFunction (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (k : ℕ) (useq : ℕ → U) : R :=
  ∑ i ∈ Finset.univ,
    ∑ j ∈ Finset.univ,
      wθ.w i j *
      (if i = useq (k % Fintype.card U) then
        (if localFieldAsym wθ s i > 0 then 1 else -1)
      else s.act i) *
      s.act j

-- Lemma: potentialFunction is bounded
@[simp]
lemma potential_function_bounded (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (k : ℕ) (useq : ℕ → U) :
  ∃ (lowerBound upperBound : R), lowerBound ≤ potentialFunction wθ s k useq ∧ potentialFunction wθ s k useq ≤ upperBound := by
  let maxSum : R := ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, |wθ.w i j|
  use -maxSum, maxSum
  constructor
  · -- Show that for each term, the product is at least -|weights_ij|
    unfold potentialFunction

    have hbound : ∀ (i j : U),
      wθ.w i j *
      (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) *
      s.act j ≥ -|wθ.w i j| := by
        intro i j
        have h1 : |(if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i)| = 1 := by
          split_ifs with h h_field
          · simp
          · simp
          · cases s.hp i with
            | inl h_one => simp [h_one]
            | inr h_neg_one => simp [h_neg_one]
        have h2 : |s.act j| = 1 := by
          cases s.hp j with
          | inl h_one => simp [h_one]
          | inr h_neg_one => simp [h_neg_one]

        calc
          wθ.w i j * (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) * s.act j
          ≥ -|wθ.w i j * (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) * s.act j| := neg_abs_le _
          _ = -|wθ.w i j * (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) * s.act j| := by
            simp only [gt_iff_lt, mul_ite, mul_one, mul_neg, ite_mul, neg_mul]
          _ = -|wθ.w i j| * |(if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i)| * |s.act j| := by
            rw [abs_mul, abs_mul]; simp_all only [gt_iff_lt, mul_one]
          _ = -|wθ.w i j| * 1 * 1 := by rw [h1, h2]
          _ = -|wθ.w i j| := by ring_nf

    -- Use the bound to establish the inequality with the sum
    calc
      potentialFunction wθ s k useq
      = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          wθ.w i j *
          (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) *
          s.act j := by rfl
      _ ≥ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, -|wθ.w i j| := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          exact hbound i j
      _ = -(∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, |wθ.w i j|) := by
          simp [Finset.sum_neg_distrib]
      _ = -maxSum := by rfl

  · apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h1 : |(if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i)| = 1 := by
        split_ifs with h h_field
        · exact abs_one
        · simp_all only [Finset.mem_univ, gt_iff_lt, not_lt, abs_neg, abs_one]
        cases s.hp i with
        | inl h_one => simp [h_one]
        | inr h_neg_one => simp [h_neg_one]
    have h2: |s.act j| = 1 := by
      cases s.hp j with
      | inl h_one => simp [h_one]
      | inr h_neg_one => simp [h_neg_one]
    calc
      wθ.w i j * (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) * s.act j
      ≤ |wθ.w i j * (if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i) * s.act j| := le_abs_self _
      _ = |wθ.w i j| * |(if i = useq (k % Fintype.card U) then (if localFieldAsym wθ s i > 0 then 1 else -1) else s.act i)| * |s.act j| := by
          rw [abs_mul, abs_mul]
      _ = |wθ.w i j| * 1 * 1 := by rw [h1, h2]
      _ = |wθ.w i j| := by ring

-- Lemma for updatedActValue in terms of localFieldAsym
@[simp]
lemma updatedActValue_eq (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i : U) :
  updatedActValue wθ s i = if localFieldAsym wθ s i > 0 then 1 else -1 := by
  unfold updatedActValue updateStateAsym
  simp only
  by_cases h : localFieldAsym wθ s i > 0
  · -- case: localFieldAsym wθ s i > 0
    simp [h]
  · -- case: localFieldAsym wθ s i ≤ 0
    simp [h]

-- Helper Lemma: localFieldAsym after an update
@[simp]
lemma localFieldAsym_update (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i : U) :
    localFieldAsym wθ (updateStateAsym wθ s i) i =
    (∑ j ∈ Finset.univ, wθ.w i j * (if j = i then (updatedActValue wθ s i) else s.act j)) - (wθ.θ i).get 0 := by
    unfold localFieldAsym
    -- The key is to understand how updateStateAsym affects the sum
    have h_update : ∀ j : U, (updateStateAsym wθ s i).act j =
      if j = i then updatedActValue wθ s i else s.act j := by
      intro j
      unfold updatedActValue updateStateAsym
      by_cases h_j_eq_i : j = i
      · subst h_j_eq_i
        simp
      · simp [h_j_eq_i]
    rw [Finset.sum_congr rfl]
    intro j _
    rw [h_update]

-- Helper Lemma: Expressing s'_j in terms of s_j and updatedActValue
@[simp]
lemma s'_eq_s_update (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (i j : U) :
  let s' := updateStateAsym wθ s i
  s'.act j = (if j = i then (updatedActValue wθ s i) else s.act j)
  := by
    by_cases h_j_eq_i : j = i
    · subst h_j_eq_i
      unfold updatedActValue updateStateAsym
      simp
    · unfold updateStateAsym
      simp [h_j_eq_i]

/--
Helper function to create parameters for an asymmetric Hopfield network.

Parameters:
- w: The weight matrix
- θ: The threshold function
- hw: A proof that weights respect the adjacency relation
- hasym: A proof that the weights can be decomposed appropriately

Returns:
- Parameters for an asymmetric Hopfield network
-/
def mkAsymmetricParams (w : Matrix U U R) (θ : U → Vector R 1) [Nonempty U]
    (hw : ∀ u v, ¬ (AsymmetricHopfieldNetwork R U).Adj u v → w u v = 0)
    (hasym : ∃ (A S : Matrix U U R),
      A.IsAntisymm ∧        -- A is antisymmetric
      (Matrix.PosDef S) ∧              -- S is positive definite
      w = A + S ∧                      -- Decomposition of the weight matrix
      (∀ i, w i i ≥ 0)) : Params (AsymmetricHopfieldNetwork R U) where
  w := w
  hw := hw
  hw' := hasym  -- The asymmetric decomposition property
  θ := θ
  σ := fun _ => Vector.emptyWithCapacity 0

/--
Attempts to find a stable state of an asymmetric Hopfield network by running a fixed number of updates.

Unlike symmetric Hopfield networks, asymmetric networks do NOT generally guarantee convergence to fixed points.
Convergence properties depend on the specific structure of the weight matrix decomposition:

1. When the symmetric positive definite component (S) dominates the antisymmetric component (A),
   the network is more likely to converge to fixed points
2. When the antisymmetric component dominates, the network may exhibit limit cycles or chaotic behavior
3. For balanced cases, behavior depends on initial conditions and update sequence

This function runs for N iterations and returns the resulting state, which may or may not be stable.

Parameters:
- wθ: The parameters for the asymmetric Hopfield network
- s: The initial state
- useq: A sequence of neurons to update
- hf: A proof that the update sequence is fair
- N: The maximum number of iterations (defaults to 10 times the network size -
  for different AHNs, different N values might be needed,)

Returns:
- The state after N iterations, with no guarantee of stability
-/
def iterateAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) [Nonempty U] (useq : ℕ → U) (_hf : fair useq)
    (N : ℕ := Fintype.card U * 10) : State (AsymmetricHopfieldNetwork R U) :=
  seqStatesAsym wθ s useq N

/--
Checks whether the network has stabilized after N iterations by comparing states
across multiple time points.
-/
def verifyStabilityAsym (wθ : Params (AsymmetricHopfieldNetwork R U))
    (s : State (AsymmetricHopfieldNetwork R U)) (useq : ℕ → U) (N : ℕ) : Bool :=
  -- Get the state after N iterations
  let stateN := seqStatesAsym wθ s useq N
  -- Get the state after N+1 iterations
  let stateN1 := seqStatesAsym wθ s useq (N+1)
  -- Check if all neurons have the same activation in both states
  decide (∀ i : U, stateN.act i = stateN1.act i)
