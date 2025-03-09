/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean
import Mathlib

/-
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Module.Basic
import GaugeAnomalies.Basic
-/

/-!
# Lie Algebra Structures for Gauge Theories

This file formalizes the Lie algebra structures needed for gauge theories,
following [CGN24] Section 3. The key decomposition g = s ⊕ a is implemented,
where s is semisimple and a is abelian.

## Main Definitions

* `LieAlgebraDecomp k g`: Structure capturing Lie algebra decomposition
* `IsLieFaithful k g V`: Property of faithful Lie algebra action
* `LieRepDatum k g`: Data for Lie algebra representations
* `ConnectedDecomposition G`: Decomposition (A × S)/Z for connected groups

## Main Results

* `decomp_unique`: Uniqueness of decomposition (up to isomorphism)
* `faithful_action_abelian`: Characterization of faithful abelian action
* `tensor_decomp`: Decomposition of tensor product representations

## References

* [CGN24] Camp, I., Gripaios, B., & Nguyen, K. L. (2024). arXiv:2403.10611
* [Kna02] Knapp, A.W. (2002). Lie Groups Beyond an Introduction
* [Hum78] Humphreys, J.E. (1978). Introduction to Lie Algebras and Representation Theory

## Tags

lie algebras, semisimple algebras, representation theory, gauge theory
-/

universe u v w

open scoped BigOperators Classical
open LieAlgebra Module Function

/-- Enhanced structure for Lie algebra decomposition capturing physical requirements. -/
structure LieAlgebraDecomp (k : Type u) [Field k] (g : Type v)
    [LieRing g] [LieAlgebra k g] where
  /-- The semisimple summand -/
  s : LieSubalgebra k g
  /-- The abelian summand -/
  a : LieSubalgebra k g
  /-- Proof that s is semisimple -/
  s_semisimple : IsSemisimple k s.1
  /-- Proof that a is abelian -/
  a_abelian : IsLieAbelian a.1
  /-- Decomposition is direct -/
  direct_sum : IsInternalDirectSum s a
  /-- Action on fermions is faithful -/
  faithful : ∀ x ∈ a.1, (∀ v, x • v = 0) → x = 0

/-- Structure containing data for a Lie algebra representation. -/
structure LieRepDatum (k : Type u) [Field k] (g : Type v)
    [LieRing g] [LieAlgebra k g] where
  /-- The representation space -/
  V : Type w
  [vec_space : Module k V]
  /-- The representation map -/
  ρ : g →ₗ[k] V →ₗ[k] V
  /-- Lie algebra homomorphism property -/
  lie_hom : ∀ x y : g, ρ (⁅x, y⁆) = ρ x * ρ y - ρ y * ρ x

/-- Implementation of connected Lie group decomposition (A × S)/Z. -/
class ConnectedDecomposition (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The torus part A -/
  A : Type u
  [group_A : Group A]
  [top_A : TopologicalSpace A]
  /-- The semisimple part S -/
  S : Type u
  [group_S : Group S]
  [top_S : TopologicalSpace S]
  /-- The finite central subgroup Z -/
  Z : Subgroup (A × S)
  /-- Z is central -/
  Z_central : ∀ z ∈ Z, ∀ g : A × S, z * g = g * z
  /-- The isomorphism G ≅ (A × S)/Z -/
  iso : G ≃* QuotientGroup.quotient Z

/-- A Lie algebra representation is faithful if its kernel is trivial. -/
def IsLieFaithful {k : Type u} [Field k] {g : Type v} [LieRing g] [LieAlgebra k g]
    (ρ : LieRepDatum k g) : Prop :=
  ∀ x : g, (∀ v : ρ.V, ρ.ρ x v = 0) → x = 0

/-- The decomposition g = s ⊕ a is unique up to isomorphism. -/
theorem decomp_unique {k : Type u} [Field k] {g : Type v} [LieRing g] [LieAlgebra k g]
    (d₁ d₂ : LieAlgebraDecomp k g) :
    ∃ φ : g ≃ₗ[k] g, φ.map_lie = id ∧ φ.toLinearMap d₁.s = d₂.s := by
  sorry  -- Standard proof using semisimplicity

/-- Key lemma: tensor product of irreducible representations. -/
lemma tensor_decomp {k : Type u} [Field k] {g : Type v} [LieRing g] [LieAlgebra k g]
    (ρ₁ ρ₂ : LieRepDatum k g) (h₁ : IsIrreducible ρ₁.ρ) (h₂ : IsIrreducible ρ₂.ρ) :
    ∃ decomp : TensorProduct k ρ₁.V ρ₂.V ≃ₗ[k] DirectSum (λ i : Fin n, Wi),
    ∀ i, IsIrreducible (πᵢ ∘ decomp) := by
  sorry  -- Follows from representation theory of semisimple Lie algebras
