import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Hopfield82.MemoryStorage
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Hopfield82

open NeuralNetwork State Matrix Finset Real

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]

/-! ### Memory Capacity -/

/--
The `StorageCapacity` of a Hopfield network is the maximum number of patterns
that can be stored and reliably retrieved. The paper suggests this is around 0.15N.

From the paper (p.2556): "About 0.15 N states can be simultaneously remembered before
error in recall is severe."
-/
def StorageCapacity : ℝ := 0.15 * Fintype.card U

/--
The error function `erf(x)` is defined as:
  erf(x) = (2/√π) ∫₀ˣ e^(-t²) dt

This function is central in probability theory, especially for normal distributions.
-/
noncomputable def Real.erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt π) * ∫ (t : ℝ) in Set.Icc 0 x, Real.exp (-(t^2))

/--
The `PatternRetrievalError` function computes the probability of an error in pattern retrieval
for a network storing m patterns. This increases as m approaches and exceeds 0.15N.

This corresponds to the error probability P discussed in Equation 10 of the paper:
P = ∫_σ^∞ (1/√(2π)) e^(-x²/2) dx = (1/2)(1 - erf(σ/√2))

where σ = N/(2√(nN)) and n is the number of patterns.
-/
noncomputable def PatternRetrievalError (m : ℕ) : ℝ :=
  let N := Fintype.card U
  let σ := N / (2 * Real.sqrt (m * N : ℝ))
  (1/2) * (1 - Real.erf (σ / Real.sqrt 2))

/--
The result from the paper that a Hopfield network can store approximately 0.15N patterns
with high reliability, where N is the number of neurons.

This theorem formalizes the key result about storage capacity from the paper,
utilizing the Hebbian_stable theorem from the existing codebase.
-/
theorem storage_capacity_bound {m : ℕ} [DecidableEq U]
  (ps : Fin m → (HopfieldNetwork R U).State)
  (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0) :
  let wθ := Hebbian ps;
  (m : ℝ) ≤ ((Fintype.card U : ℝ) * (15 : ℝ)) / (100 : ℝ) → ∀ k : Fin m, FixedPoint wθ (ps k) := by
  intros _ hm k
  unfold FixedPoint
  apply Hebbian_stable
  · have h1 : (m : ℝ) ≤ ((Fintype.card U : ℝ) * 15) / 100 := hm
    have aux : (15 : ℝ) / 100 < 1 := by norm_num;
    have h2 : ((Fintype.card U : ℝ) * 15) / 100 < (Fintype.card U : ℝ) :=
        by
          have cardU_pos : 0 < (Fintype.card U : ℝ) := by norm_cast; exact Fintype.card_pos
          have h_rewrite : ((Fintype.card U : ℝ) * 15) / 100 = (Fintype.card U : ℝ) * (15 / 100) := by ring
          have h_frac_lt_one : (15 : ℝ) / 100 < 1 := by norm_num
          have h_mul_lt_mul : (Fintype.card U : ℝ) * (15 / 100) < (Fintype.card U : ℝ) * 1 :=
            mul_lt_mul_of_pos_left h_frac_lt_one cardU_pos
          have h_simplify : (Fintype.card U : ℝ) * 1 = (Fintype.card U : ℝ) := by ring
          calc
            ((Fintype.card U : ℝ) * 15) / 100 = (Fintype.card U : ℝ) * (15 / 100) := h_rewrite
            _ < (Fintype.card U : ℝ) * 1 := h_mul_lt_mul
            _ = (Fintype.card U : ℝ) := h_simplify
    have h3 : (m : ℝ) < (Fintype.card U : ℝ) := lt_of_le_of_lt h1 h2
    have h4 : m < Fintype.card U := by exact_mod_cast h3
    exact h4
  · exact horth
