import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Stochastic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Analysis.BoundedVariation

open ProbabilityTheory.Kernel

namespace ProbabilityTheory.Kernel

/-- `Kernel.pow κ n` is the `n`-fold composition of the kernel `κ`, with `pow κ 0 = id`. -/
noncomputable def pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α) : ℕ → Kernel α α
| 0     => Kernel.id
| n + 1 => κ ∘ₖ (pow κ n)

end ProbabilityTheory.Kernel

/-!
# Markov Chain Framework

## Main definitions

* `stochasticHopfieldMarkovProcess`: A Markov process on Hopfield network states
* `gibbsTransitionKernel`: The transition kernel for Gibbs sampling
* `DetailedBalance`: The detailed balance condition for reversible Markov chains
* `mixingTime`: The time needed to approach the stationary distribution (TODO)

-/

open MeasureTheory ProbabilityTheory ENNReal Finset Function ProbabilityTheory.Kernel Set

namespace MarkovChain

-- Using the discrete sigma-algebra implicitly for the finite state space
instance (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :
  MeasurableSpace ((HopfieldNetwork R U).State) := ⊤

-- Prove all sets are measurable in the discrete sigma-algebra
lemma measurableSet_discrete {α : Type*} [MeasurableSpace α] (h : ‹_› = ⊤)
    (s : Set α) : MeasurableSet s := by
  rw [h]
  trivial

instance (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U] :
    DiscreteMeasurableSpace ((HopfieldNetwork R U).State) where
  forall_measurableSet := fun s => measurableSet_discrete rfl s

/-!
### Core Markov Chain Definitions
-/

/--
A `StationaryDistribution` for a transition kernel is a measure that remains
invariant under the action of the kernel.
-/
structure StationaryDistribution {α : Type*} [MeasurableSpace α] (K : Kernel α α) where
  /-- The probability measure that is stationary with respect to the kernel K. -/
  measure : Measure α
  /-- Proof that the measure is a probability measure (sums to 1). -/
  isProbability : IsProbabilityMeasure measure
  /-- Proof that the measure is invariant under the kernel K. -/
  isStationary : ∀ s, MeasurableSet s → (Measure.bind measure K) s = measure s

/--
The detailed balance condition for a Markov kernel with respect to a measure.
`μ(dx) K(x,dy) = μ(dy) K(y,dx)` for all measurable sets
-/
def DetailedBalance {α : Type*} [MeasurableSpace α] (μ : Measure α) (K : Kernel α α) : Prop :=
  ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, (K x B) ∂μ = ∫⁻ y in B, (K y A) ∂μ

/-- When detailed balance holds, the measure is stationary -/
def stationaryOfDetailedBalance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {K : Kernel α α} [IsMarkovKernel K]
    (h : DetailedBalance μ K) : StationaryDistribution K where
  measure := μ
  isProbability := inferInstance
  isStationary := by
    intro s hs
    have bind_def : (μ.bind K) s = ∫⁻ x, (K x s) ∂μ := by
      apply Measure.bind_apply hs (Kernel.aemeasurable K)
    have h_balance := h Set.univ s MeasurableSet.univ hs
    rw [bind_def]
    have h_univ : ∫⁻ x, K x s ∂μ = ∫⁻ x in Set.univ, K x s ∂μ := by
      simp only [Measure.restrict_univ]
    rw [h_univ, h_balance]
    have univ_one : ∀ y, K y Set.univ = 1 := by
      intro y
      exact measure_univ
    have h_one : ∫⁻ y in s, K y Set.univ ∂μ = ∫⁻ y in s, 1 ∂μ := by
      apply lintegral_congr_ae
      exact ae_of_all (μ.restrict s) univ_one
    rw [h_one, MeasureTheory.lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, one_mul]

/-!
### Markov Chain on Hopfield Networks
-/

section HopfieldMarkovChain

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
  [Fintype U] [Nonempty U] [Coe R ℝ]

instance : Nonempty ((HopfieldNetwork R U).State) := by
  let defaultState : (HopfieldNetwork R U).State := {
    act := fun _ => -1,
    hp := fun _ => Or.inr rfl
  }
  exact ⟨defaultState⟩

-- Fintype instance for the state space
noncomputable instance : Fintype ((HopfieldNetwork R U).State) := by
  let f : ((HopfieldNetwork R U).State) → (U → {r : R | r = 1 ∨ r = -1}) :=
    fun s u => ⟨s.act u, s.hp u⟩
  have h_inj : Function.Injective f := by
    intro s1 s2 h
    cases s1 with | mk act1 hp1 =>
    cases s2 with | mk act2 hp2 =>
    simp at *
    ext u
    have h_u := congr_fun h u
    simp [f] at h_u
    exact h_u
  have h_surj : Function.Surjective f := by
    intro g
    let act := fun u => (g u).val
    have hp : ∀ u, act u = 1 ∨ act u = -1 := fun u => (g u).property
    exists ⟨act, hp⟩
  exact _root_.instFintypeStateHopfieldNetwork

noncomputable def gibbsTransitionKernel (wθ : Params (HopfieldNetwork R U)) (T : ℝ) :
    Kernel ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) where
  toFun := fun state => (NN.State.gibbsSamplingStep wθ state T).toMeasure
  measurable' := Measurable.of_discrete

-- Mark the kernel as a Markov kernel (preserves probability)
instance gibbsIsMarkovKernel (wθ : Params (HopfieldNetwork R U)) (T : ℝ) :
    IsMarkovKernel (gibbsTransitionKernel wθ T) where
  isProbabilityMeasure := by
    intro s
    simp [gibbsTransitionKernel]
    exact PMF.toMeasure.isProbabilityMeasure (NN.State.gibbsSamplingStep wθ s T)

/--
The stochastic Hopfield Markov process, which models the evolution of Hopfield network states
over discrete time steps using Gibbs sampling at fixed temperature.
In this simplified model, the transition kernel is time-homogeneous (same for all steps).
-/
noncomputable def stochasticHopfieldMarkovProcess (wθ : Params (HopfieldNetwork R U)) (T : ℝ) :
    ℕ → Kernel ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) :=
  fun _ => gibbsTransitionKernel wθ T

/--
The n-step transition probability, which gives the probability of moving from
state x to state y in exactly n steps.
-/
noncomputable def nStepTransition (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (n : ℕ) :
    ((HopfieldNetwork R U).State) → ((HopfieldNetwork R U).State) → ENNReal :=
  fun x y => (Kernel.pow (gibbsTransitionKernel wθ T) n x) {y} -- Correct application of Kernel.pow

/--
The total variation distance between two probability measures on Hopfield network states.
Defined as supremum of |μ(A) - ν(A)| over all measurable sets A.
-/
noncomputable def totalVariation (μ ν : Measure ((HopfieldNetwork R U).State)) : ENNReal :=
  ⨆ (A : Set ((HopfieldNetwork R U).State)) (_ : MeasurableSet A),
    ENNReal.ofReal (abs ((μ A).toReal - (ν A).toReal))

/--
A state is aperiodic if there's a positive probability of returning to it in a single step.
-/
def IsAperiodic (wθ : Params (HopfieldNetwork R U)) (T : ℝ)
  (s : (HopfieldNetwork R U).State) : Prop := (gibbsTransitionKernel wθ T s) {s} > 0

/--
A Markov chain is irreducible if it's possible to get from any state to any other state
with positive probability in some finite number of steps.
-/
def IsIrreducible (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : Prop :=
  ∀ x y, ∃ n, (Kernel.pow (gibbsTransitionKernel wθ T) n x) {y} > 0 -- Use Kernel.pow correctly

/-- The unnormalized Boltzmann density function -/
noncomputable def boltzmannDensityFn (wθ : Params (HopfieldNetwork R U)) (T : ℝ)
    (s : (HopfieldNetwork R U).State) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(Coe.coe (NeuralNetwork.State.E wθ s) : ℝ) / T))

/-- The Boltzmann partition function (normalizing constant) -/
noncomputable def boltzmannPartitionFn (wθ : Params (HopfieldNetwork R U)) (T : ℝ) : ENNReal :=
  ∑ s ∈ Finset.univ, boltzmannDensityFn wθ T s

/-- Helper lemma: A finite sum of ENNReal values is positive if the set is
  nonempty and all terms are positive -/
lemma ENNReal.sum_pos {α : Type*} (s : Finset α) (f : α → ENNReal)
    (h_nonempty : s.Nonempty) (h_pos : ∀ i ∈ s, 0 < f i) : 0 < ∑ i ∈ s, f i := by
  rcases h_nonempty with ⟨i, hi⟩
  have h_pos_i : 0 < f i := h_pos i hi
  have h_le : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum (fun j _ => zero_le (f j)) hi
  exact lt_of_lt_of_le h_pos_i h_le

/-- The Boltzmann partition function is positive and finite -/
lemma boltzmannPartitionFn_pos_finite (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (_hT : T ≠ 0) :
  0 < boltzmannPartitionFn wθ T ∧ boltzmannPartitionFn wθ T < ⊤ := by
  simp only [boltzmannPartitionFn]
  have h_pos_term : ∀ s : (HopfieldNetwork R U).State, 0 < boltzmannDensityFn wθ T s := by
    intro s
    simp only [boltzmannDensityFn]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have h_finite_term : ∀ s : (HopfieldNetwork R U).State, boltzmannDensityFn wθ T s ≠ ⊤ := by
    intro s
    simp only [boltzmannDensityFn]
    exact ENNReal.ofReal_ne_top
  constructor
  · -- Proves positivity: sum of positive terms is positive
    apply ENNReal.sum_pos
    · exact Finset.univ_nonempty
    · intro s _hs_in_univ
      exact h_pos_term s
  · -- Proves finiteness: sum is finite if all terms are finite
    rw [sum_lt_top]
    intro s _hs_in_univ
    rw [lt_top_iff_ne_top]
    exact h_finite_term s
/--
The Boltzmann distribution over Hopfield network states at temperature T.
-/
noncomputable def boltzmannDistribution (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T ≠ 0) :
    Measure ((HopfieldNetwork R U).State) :=
  let densityFn := boltzmannDensityFn wθ T
  let partitionFn := boltzmannPartitionFn wθ T
  let _h_part_pos_finite := boltzmannPartitionFn_pos_finite wθ T hT
  let countMeasure : Measure ((HopfieldNetwork R U).State) := MeasureTheory.Measure.count
  if h_part : partitionFn = 0 ∨ partitionFn = ⊤ then
    0
  else
    let partitionFn_ne_zero : partitionFn ≠ 0 := by
      intro h_zero
      exact h_part (Or.inl h_zero)
    let partitionFn_ne_top : partitionFn ≠ ⊤ := by
      intro h_top
      exact h_part (Or.inr h_top)
    Measure.withDensity countMeasure (fun s => densityFn s / partitionFn)

-- Helper lemma to handle the 'if' in boltzmannDistribution definition
lemma boltzmannDistribution_def_of_pos_finite (wθ : Params (HopfieldNetwork R U))
    (T : ℝ) (hT : T ≠ 0) :
  boltzmannDistribution wθ T hT =
    let densityFn := boltzmannDensityFn wθ T
    let partitionFn := boltzmannPartitionFn wθ T
    let countMeasure : Measure ((HopfieldNetwork R U).State) := MeasureTheory.Measure.count
    Measure.withDensity countMeasure (fun s => densityFn s / partitionFn) := by
  let h_part := boltzmannPartitionFn_pos_finite wθ T hT
  simp [boltzmannDistribution, h_part.1.ne', h_part.2.ne]
  -- Use the fact that partitionFn is > 0 and < ⊤

/-- The Boltzmann distribution measure of the universe equals the integral of density/partition -/
lemma boltzmannDistribution_measure_univ (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T ≠ 0) :
  boltzmannDistribution wθ T hT Set.univ =
  ∫⁻ s in Set.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) ∂Measure.count := by
  rw [boltzmannDistribution_def_of_pos_finite wθ T hT]
  simp only [withDensity_apply _ MeasurableSet.univ]

/-- The integral over the universe equals the sum over all states -/
lemma boltzmannDistribution_integral_eq_sum (wθ : Params (HopfieldNetwork R U))
    (T : ℝ) (_hT : T ≠ 0) :
  ∫⁻ s in Set.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) ∂Measure.count =
  ∑ s ∈ Finset.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) := by
  rw [Measure.restrict_univ]
  trans ∑' (s : (HopfieldNetwork R U).State),
     (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T)
  · exact MeasureTheory.lintegral_count
      (fun s => (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T))
  · exact tsum_fintype fun b ↦ boltzmannDensityFn wθ T b / boltzmannPartitionFn wθ T

/-- Division can be distributed over the sum in the Boltzmann distribution -/
lemma boltzmannDistribution_div_sum (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T ≠ 0) :
  ∑ s ∈ Finset.univ, (boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) =
  (∑ s ∈ Finset.univ, boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) := by
  let Z := boltzmannPartitionFn wθ T
  let h_part := boltzmannPartitionFn_pos_finite wθ T hT
  have h_Z_pos : Z > 0 := h_part.1
  have h_Z_lt_top : Z < ⊤ := h_part.2
  have h_div_def : ∀ (a b : ENNReal), a / b = a * b⁻¹ := fun a b => by
    rw [ENNReal.div_eq_inv_mul]
    rw [mul_comm b⁻¹ a]
  simp only [h_div_def]
  rw [Finset.sum_mul]


/-- The sum of Boltzmann probabilities equals 1 -/
lemma boltzmannDistribution_sum_one  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T ≠ 0) :
  (∑ s ∈ Finset.univ, boltzmannDensityFn wθ T s) / (boltzmannPartitionFn wθ T) = 1 := by
  simp only [boltzmannPartitionFn]
  let h_part := boltzmannPartitionFn_pos_finite wθ T hT
  exact ENNReal.div_self h_part.1.ne' h_part.2.ne

/--
Proves that the Boltzmann distribution for a Hopfield network forms a valid probability measure.
-/
theorem boltzmannDistribution_isProbability {R U : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
    [Fintype U] [Nonempty U] [Coe R ℝ]
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (hT : T ≠ 0) :
  IsProbabilityMeasure (boltzmannDistribution wθ T hT) := by
  constructor
  rw [boltzmannDistribution_measure_univ wθ T hT]
  rw [boltzmannDistribution_integral_eq_sum wθ T hT]
  rw [boltzmannDistribution_div_sum wθ T hT]
  exact boltzmannDistribution_sum_one wθ T hT

end HopfieldMarkovChain

end MarkovChain
