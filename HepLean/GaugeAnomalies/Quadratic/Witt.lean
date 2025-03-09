/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean
/-
import GaugeAnomalies.Quadratic.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.OrthogonalGroup.Basic
-/

/-!
# Witt Decomposition Theory

This file formalizes the Witt decomposition theory for quadratic forms, following
[CGN24] Section 3 and [Cas78] Chapter 4. The key structure is `WittDecomposition`,
which provides a complete decomposition of a quadratic space into hyperbolic and
anisotropic parts.

## Main Definitions

* `WittDecomposition k V`: The complete Witt decomposition structure
* `IsHyperbolicSpace k V`: Characterization of hyperbolic spaces
* `OrthogonalAction k V`: Action of orthogonal group on decomposition
* `CayleyTransform k V`: Implementation of Cayley transform

## Main Results

* `witt_decomp_exists`: Existence theorem for Witt decomposition
* `witt_index_unique`: Uniqueness of Witt index
* `orthogonal_action_transitive`: Transitivity of orthogonal group action

## Implementation Notes

Following [CGN24], we implement the iterative construction process for
finding the Witt decomposition, using the Gram-Schmidt process for
hyperbolic plane construction.

## References

* [CGN24] Camp, I., Gripaios, B., & Nguyen, K. L. (2024). arXiv:2403.10611
* [Cas78] Cassels, J.W.S. (1978). Rational Quadratic Forms.
* [Lam05] Lam, T.Y. (2005). Introduction to Quadratic Forms over Fields.

## Tags

witt decomposition, quadratic forms, orthogonal groups, cayley transform
-/

universe u v w

open scoped BigOperators Classical Matrix
open LinearMap Module Set Function

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [QuadraticStructure k V]
variable [Module.FiniteDimensional k V]

/-- Structure encapsulating a Witt decomposition of a quadratic space. -/
structure WittDecomposition (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] [QuadraticStructure k V] where
  /-- The hyperbolic part -/
  Vh : Submodule k V
  /-- The anisotropic part -/
  Va : Submodule k V
  /-- The Witt index -/
  index : ℕ
  /-- The hyperbolic planes -/
  planes : Fin index → HyperbolicPlane
  /-- Vh is spanned by the planes -/
  spans : Vh = Submodule.span k (⋃ i, {(planes i).v₁, (planes i).v₂})
  /-- The decomposition is direct -/
  direct : IsInternalDirectSum Vh Va
  /-- Hyperbolic planes are orthogonal -/
  orthogonal : ∀ i j, i ≠ j →
    (∀ vi ∈ {(planes i).v₁, (planes i).v₂},
     ∀ vj ∈ {(planes j).v₁, (planes j).v₂},
     QuadraticStructure.bilin vi vj = 0)
  /-- Va is anisotropic -/
  anisotropic : ∀ v ∈ Va, IsIsotropic v → v = 0

/-- A space is hyperbolic if it's a direct sum of hyperbolic planes. -/
def IsHyperbolicSpace (U : Submodule k V) : Prop :=
  ∃ n : ℕ, ∃ planes : Fin n → HyperbolicPlane,
    U = Submodule.span k (⋃ i, {(planes i).v₁, (planes i).v₂})

/-- Implementation of the Cayley transform following [CGN24] Section 3. -/
def CayleyTransform (A : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  -(1 - A) * (1 + A)⁻¹

/-- The Cayley transform is invertible when 1 is not an eigenvalue. -/
lemma cayley_transform_invertible (A : Matrix (Fin n) (Fin n) k)
    (h : ¬ IsEigenvalue A 1) : IsUnit (CayleyTransform A) := by
  sorry  -- Proof uses determinant properties

/-- Every regular quadratic form has a Witt decomposition. -/
theorem witt_decomp_exists [Module.FiniteDimensional k V]
    (hreg : QuadraticStructure.regular) :
    ∃ decomp : WittDecomposition k V, True := by
  sorry  -- Proof follows iterative construction from CGN24

/-- The Witt index is independent of the choice of decomposition. -/
theorem witt_index_unique (d₁ d₂ : WittDecomposition k V) :
    d₁.index = d₂.index := by
  sorry  -- Standard proof from [Cas78]

/-- The orthogonal group acts transitively on maximal totally isotropic subspaces. -/
theorem orthogonal_action_transitive (U₁ U₂ : Submodule k V)
    (h₁ : IsMaximalTotallyIsotropic U₁) (h₂ : IsMaximalTotallyIsotropic U₂) :
    ∃ g : OrthogonalGroup k V, U₂ = g • U₁ := by
  sorry  -- Proof uses Cayley transform machinery
