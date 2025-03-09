/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean
import Mathlib
/-
import GaugeAnomalies.Lie.Basic
import GaugeAnomalies.Lie.Representation
import GaugeAnomalies.Quadratic.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Lie.Classical
-/

/-!
# Basic Anomaly Structure

This file formalizes the fundamental anomaly structures in 2D gauge theories,
following [CGN24] §3. The core structures capture both the local and global
aspects of gauge and gravitational anomalies.

## Main Definitions

* `AnomalyCoefficients k g`: Structure capturing anomaly coefficients
* `LocalAnomaly k g`: Local anomaly conditions for gauge theories
* `GlobalAnomaly k g`: Global anomaly structure (reserved for future use)
* `AnomalySystem k g`: Complete system of anomaly conditions

## Main Results

* `local_anomaly_semisimple`: Structure of semisimple part of local anomaly
* `trace_decomposition`: Decomposition of anomaly traces
* `consistent_iff_anomaly_free`: Consistency condition for anomaly cancellation

## References

* [CGN24] Camp, I., Gripaios, B., & Nguyen, K. L. (2024). "Two-dimensional gauge
  anomalies and p-adic numbers". arXiv:2403.10611
* [BIM19] Bilal, A., Iorio, A., & Metzger, M. (2019). "Two-dimensional gauge theories
  revisited: a geometric approach to anomalies". Int. J. Mod. Phys. A34.

## Notes

Notation follows [CGN24] §3. We use k for the base field (typically ℚ or ℝ).

## Tags

gauge anomalies, local anomalies, 2d quantum field theory, representation theory
-/

universe u v w

open scoped BigOperators Classical
open LieAlgebra Module Function

/-- Structure capturing anomaly coefficients in terms of representation traces. -/
structure AnomalyCoefficients (k : Type u) [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] where
  /-- Dimension of representation space -/
  n : ℕ
  /-- Coefficients from traces -/
  coeffs : Fin n → k
  /-- Sum-to-zero condition (gravitational anomaly) -/
  sum_zero : ∑ i, coeffs i = 0
  /-- Coefficients are nonzero (regularity) -/
  nonzero : ∀ i, coeffs i ≠ 0

/-- Local anomaly structure capturing both gauge and gravitational components. -/
structure LocalAnomaly (k : Type u) [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] where
  /-- Decomposition of Lie algebra -/
  decomp : LieAlgebraDecomp k g
  /-- Anomaly coefficients -/
  coeffs : AnomalyCoefficients k
  /-- The anomaly trace map -/
  trace : g → g →ₗ[k] k
  /-- Trace satisfies cyclic property -/
  trace_cyclic : ∀ x y z, trace x y = trace y z + trace z x
  /-- Relation to coefficients -/
  trace_decomp : ∀ x y, trace x y = ∑ i, coeffs.coeffs i * (std_basis i) x * (std_basis i) y

/-- Structure encapsulating global anomaly conditions. -/
class GlobalAnomaly (k : Type u) [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] where
  /-- Reserved for future formalization of global anomalies -/
  is_anomaly_free : Prop  -- Details to be specified in future work

/-- Complete system combining local and global anomaly conditions. -/
structure AnomalySystem (k : Type u) [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] where
  /-- The local anomaly structure -/
  local : LocalAnomaly k
  /-- Generators of gauge transformations -/
  gauge_generators : g →ₗ[k] g →ₗ[k] g
  /-- Anomaly cancellation condition -/
  anomaly_free : ∀ x y z, local.trace (gauge_generators x y) z = 0

/-- The trace decomposes according to semisimple and abelian parts. -/
theorem trace_decomposition {k : Type u} [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] (A : LocalAnomaly k) :
    ∀ x y, A.trace x y = A.trace (A.decomp.s.proj x) y + A.trace (A.decomp.a.proj x) y := by
  sorry  -- Proof uses direct_sum property and linearity

/-- The semisimple part of the local anomaly has special structure. -/
theorem local_anomaly_semisimple {k : Type u} [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] (A : LocalAnomaly k) :
    ∀ x y ∈ A.decomp.s, ∃ c : k, A.trace x y = c * KillingForm k g x y := by
  sorry  -- Uses semisimplicity and Killing form properties

/-- A theory is consistent if and only if it is anomaly-free. -/
theorem consistent_iff_anomaly_free {k : Type u} [Field k] {g : Type v}
    [LieRing g] [LieAlgebra k g] (A : AnomalySystem k) :
    (∀ x y z, A.local.trace (A.gauge_generators x y) z = 0) ↔
    A.local.coeffs.sum_zero ∧ ∀ x y ∈ A.local.decomp.s, A.local.trace x y = 0 := by
  sorry  -- Key theorem from [CGN24] §3
