/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Dimension.Free
import PhysLean.Meta.TODO.Basic
import PhysLean.QuantumMechanics.PlanckConstant
/-!

# Finite target quantum mechanics

The phrase 'finite target' is used to describe quantum mechanical systems where the
Hilbert space is finite.

Physical examples of such systems include:
- Spin systems.
- Tight binding chains.

-/
open Constants
namespace QuantumMechanics

/-- A `FiniteTarget` structure that is basis independent, i.e. use a linear map for
  the hamiltonian instead of a matrix."-/
structure FiniteTarget (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H] (n : ℕ) where
  /-- The Hamiltonian, written now as a vector space map on a finite dimensional Hilbert space. -/
  hdim: Module.finrank ℂ H = n
  Ham : H →L[ℂ] H -- continuous linear map. seems easier to work with and
                  -- standard than l[C] (lin map) as the →L[ℂ]s has a Star algebra structure.
  Ham_selfAdjoint: IsSelfAdjoint Ham

namespace FiniteTarget
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H] -- a Hilbert Space with finite dimension
variable {n : ℕ}(A : FiniteTarget H n)

/-- Given a finite target QM system `A`, the time evolution operator for a `t : ℝ`,
  `A.timeEvolution t` is defined as `exp(- I t /ℏ * A.Ham)`. Still a map.-/
noncomputable def timeEvolution (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ℂ (-(Complex.I * t / ℏ) • A.Ham)
  -- Note that the `H →L[ℂ] H`s make an algebra over 𝕂 := ℂ, so [Algebra 𝕂 𝔸] is satisfied.

/-- The matrix representation of the time evolution operator in a given basis. Given a
Planck constant `ℏ`, the matrix is a self-adjoint `n × n` matrix describing the timeEvolution. -/
noncomputable def timeEvolutionMatrix (t : ℝ) (b : Basis (Fin n) ℂ H) :
  Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix b b (A.timeEvolution t).toLinearMap
  -- For `LinearMap.toMatrix`, both `M₁`, `M₂` are H.

/- An instance of timeEvolutionmatrix over the standard basis.-/
noncomputable def timeEvolutionMatrixStandard (t : ℝ) :
  Matrix (Fin n) (Fin n) ℂ :=
  -- Use the fact that H ≃ ℂ^n to get a basis
    let b : Basis (Fin n) ℂ H := Module.finBasisOfFinrankEq ℂ H A.hdim
    (timeEvolutionMatrix A t b)

TODO "`6VZGG`" "Define a smooth structure on `FiniteTarget`."

end FiniteTarget

end QuantumMechanics
