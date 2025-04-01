/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import PhysLean.Meta.TODO.Basic
/-!

# Finite target quantum mechanics

The phrase 'finite target' is used to describe quantum mechanical systems where the
Hilbert space is finite.
-/

namespace QuantumMechanics

/-- A finite target quantum mechanical system with hilbert-space of dimension `n`
  and Plank constant `ℏ` is described by a self-adjoint `n × n` matrix. -/
structure FiniteTarget (n : ℕ) {ℏ : ℝ} (hℏ : 0 < ℏ) where
  /-- The Hamiltonian, written with respect to the standard basis on `Fin n → ℂ`. -/
  H : Matrix (Fin n) (Fin n) ℂ
  H_selfAdjoint : Matrix.IsHermitian H

namespace FiniteTarget

variable {n : ℕ} {ℏ : ℝ} {hℏ : 0 < ℏ} (A : FiniteTarget n hℏ)

/-- The Hilbert space associated with a finite target theory `A`. -/
@[nolint unusedArguments]
abbrev V (_ : FiniteTarget n hℏ) := Fin n → ℂ

/-- Given a finite target QM system `A`, the time evolution matrix for a `t : ℝ`,
  `A.timeEvolutionMatrix t` is defined as `e ^ (- I t /ℏ * A.H)`. -/
noncomputable def timeEvolutionMatrix (A : FiniteTarget n hℏ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ℂ (- (Complex.I * t / ℏ) • A.H)

/-- Given a finite target QM system `A`, `timeEvolution` is the linear map from
  `A.V` to `A.V` obtained by multiplication with `timeEvolutionMatrix`. -/
noncomputable def timeEvolution (A : FiniteTarget n hℏ) (t : ℝ) : A.V →ₗ[ℂ] A.V :=
  (LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))).symm
  (timeEvolutionMatrix A t)

TODO "6VZGG" "Define a smooth structure on `FiniteTarget`."

end FiniteTarget

end QuantumMechanics
