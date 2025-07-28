import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.NeuralNetwork
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-- Probability Mass Function over Neural Network States -/
def NeuralNetwork.StatePMF {R U : Type} [Zero R]
  (NN : NeuralNetwork R U) := PMF (NN.State)

/-- Temperature-parameterized stochastic dynamics for neural networks -/
def NeuralNetwork.StochasticDynamics {R U : Type} [Zero R]
    (NN : NeuralNetwork R U) :=
  ∀ (_ : ℝ), NN.State → NeuralNetwork.StatePMF NN

/-- Metropolis acceptance decision as a probability mass function over Boolean outcomes -/
def NN.State.metropolisDecision (p : ℝ) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal (min p 1))
  (mod_cast min_le_right p 1)
