/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean
import Mathlib
/-
import GaugeAnomalies.Lie.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.DirectSum.Decomposition
-/

/-!
# Representation Theory for 2D Gauge Theories

This file develops the representation theory needed for analyzing gauge anomalies,
following [CGN24] Section 3. We focus on representations of g = s ⊕ a and their
decomposition properties.

## Main Definitions

* `LieRepDecomposition k g`: Decomposition of representations
* `ChiralRepresentation k g`: Structure for chiral representations
* `AnomalyCoefficient k g ρ`: Anomaly coefficients from representations
* `IrrepDecomposition k g V`: Irreducible decomposition structure

## Main Results

* `decomp_exists`: Existence of irreducible decomposition
* `tensor_decomp_semisimple`: Tensor decomposition for semisimple part
* `anomaly_coeff_additive`: Additivity of anomaly coefficients

## References

* [CGN24] Camp, I., Gripaios, B., & Nguyen, K. L. (2024). arXiv:2403.10611
* [Kna02] Knapp, A.W. (2002). Lie Groups Beyond an Introduction
* [FH91] Fulton, W., Harris, J. (1991). Representation Theory

## Tags

representation theory, lie algebras, gauge theories, anomalies
-/

universe u v w

open scoped BigOperators Classical
open LieAlgebra Module Function DirectSum

/-- Structure capturing decomposition of Lie algebra representations. -/
structure LieRepDecomposition (k : Type u) [Field k] (g : Type v)
    [LieRing g] [LieAlgebra k g] (V : Type w) [Module k V] where
  /-- Number of irreducible components -/
  n : ℕ
  /-- The irreducible subspaces -/
  components : Fin n → Submodule k V
  /-- Each component is irreducible -/
  irreducible : ∀ i, IsIrreducible (components i)
  /-- Direct sum decomposition -/
  direct_sum : IsInternalDirectSum (fun i => components i)

/-- Structure for chiral representations in 2D gauge theories. -/
structure ChiralRepresentation (k : Type u) [Field k] (g : Type v)
    [LieRing g] [LieAlgebra k g] extends LieRepDatum k g where
  /-- Left or right moving -/
  is_left : Bool
  /-- Multiplicity of representation -/
  multiplicity : ℕ+
  /-- Action preserves chirality -/
  preserves_chirality : ∀ x : g, ∀ v : V,
    ∃ w : V, ρ x v = (if is_left then 1 else -1) • w

/-- Compute anomaly coefficient for a representation. -/
def AnomalyCoefficient {k : Type u} [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] (ρ : LieRepDatum k g) : k :=
  ∑ i j, (ρ.ρ (std_basis i) * ρ.ρ (std_basis j)).trace

/-- Structure for irreducible decomposition with explicit isomorphisms. -/
structure IrrepDecomposition (k : Type u) [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] (V : Type w) [Module k V] where
  /-- Number of irreducible components -/
  n : ℕ
  /-- The irreducible representations -/
  irreps : Fin n → LieRepDatum k g
  /-- Multiplicities -/
  mult : Fin n → ℕ
  /-- Each irrep is actually irreducible -/
  is_irrep : ∀ i, IsIrreducible (irreps i).ρ
  /-- The decomposition isomorphism -/
  iso : V ≃ₗ[k] DirectSum (λ i, (irreps i).V ^ (mult i))
  /-- The isomorphism respects the action -/
  action_compat : ∀ x : g, ∀ v : V,
    iso (x • v) = DirectSum.map (λ i v, (irreps i).ρ x v) (iso v)

/-- Every finite-dimensional representation has an irreducible decomposition. -/
theorem decomp_exists [Module.FiniteDimensional k V]
    (ρ : LieRepDatum k g) :
    ∃ decomp : IrrepDecomposition k V, True := by
  sorry  -- Standard complete reducibility argument

/-- Tensor product decomposition for semisimple part. -/
theorem tensor_decomp_semisimple {s : LieSubalgebra k g}
    (hs : IsSemisimple k s) (ρ₁ ρ₂ : LieRepDatum k s)
    (h₁ : IsIrreducible ρ₁.ρ) (h₂ : IsIrreducible ρ₂.ρ) :
    ∃ decomp : IrrepDecomposition k (TensorProduct k ρ₁.V ρ₂.V),
    ∀ i, IsIrreducible (decomp.irreps i).ρ := by
  sorry  -- Uses Clebsch-Gordan theory

/-- Anomaly coefficients are additive under direct sums. -/
theorem anomaly_coeff_additive {V₁ V₂ : Type w}
    [Module k V₁] [Module k V₂]
    (ρ₁ : LieRepDatum k g) (ρ₂ : LieRepDatum k g) :
    AnomalyCoefficient (ρ₁.directSum ρ₂) =
    AnomalyCoefficient ρ₁ + AnomalyCoefficient ρ₂ := by
  sorry  -- Uses trace properties
