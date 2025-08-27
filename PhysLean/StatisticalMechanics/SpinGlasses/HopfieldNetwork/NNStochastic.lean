import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.NeuralNetwork
import Mathlib.Probability.ProbabilityMassFunction.Constructions

universe uR uU uσ

open NeuralNetwork State

/-- Probability Mass Function over Neural Network States -/
def NeuralNetwork.StatePMF
  {R : Type uR} {U : Type uU} {σ : Type uσ} [Zero R]
  (NN : NeuralNetwork R U σ) : Type _ :=
  PMF NN.State

/-- Temperature-parameterized stochastic dynamics for neural networks -/
def NeuralNetwork.StochasticDynamics
  {R : Type uR} {U : Type uU} {σ : Type uσ} [Zero R]
  (NN : NeuralNetwork R U σ) :=
  ℝ → NN.State → NeuralNetwork.StatePMF NN

/-- Metropolis acceptance decision as a probability mass function over Boolean outcomes -/
def NeuralNetwork.State.metropolisDecision (p : ℝ) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal (min p 1)) (by
    have : min p 1 ≤ 1 := min_le_right _ _
    simp)
