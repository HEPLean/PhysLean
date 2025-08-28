import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Hopfield82.PhaseSpaceFlow

namespace Hopfield82

open NeuralNetwork State Matrix Finset Real

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]

/-! ### Memory Storage Algorithm -/

/--
The `normalizedPattern` converts a neural state to a vector with -1/+1 values,
matching the (2Vᵢ - 1) term from equation 2 in Hopfield's paper.
-/
def normalizedPattern [DecidableEq R] [DecidableEq U] (s : (HopfieldNetwork R U).State) : U → R :=
  λ u => s.act u

/--
The `hebbian` function computes the weight matrix according to Equation 2 of Hopfield's paper:
    Tᵢⱼ = Σₛ (2Vᵢˢ - 1)(2Vⱼˢ - 1) with Tᵢᵢ = 0

Note that this is equivalent to the existing `Hebbian` definition in HopfieldNet.HN,
but we make the connection to the paper explicit here.
-/
def hebbian {m : ℕ} [DecidableEq R] [DecidableEq U]
  (ps : Fin m → (HopfieldNetwork R U).State) : Matrix U U R :=
  let normPatterns := λ s i => (ps s).act i;
  let T := ∑ s : Fin m, fun i j => normPatterns s i * normPatterns s j;
  λ i j => if i = j then 0 else T i j

/--
The `pseudoOrthogonality` property from Hopfield's paper (Equations 3-4) states:
For random patterns, the dot product between different patterns is approximately 0,
while the dot product of a pattern with itself is approximately N.
-/
def isPseudoOrthogonal {m : ℕ} [DecidableEq R] [DecidableEq U]
  (ps : Fin m → (HopfieldNetwork R U).State) : Prop :=
  ∀ i j : Fin m, i ≠ j → dotProduct (ps i).act (ps j).act = 0
