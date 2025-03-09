/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean.GaugeAnomalies.Basic
import HepLean

/-!
# Quadratic Forms for Anomaly Analysis

This file develops the theory of quadratic forms needed for analyzing
gauge anomalies in 2D, following Camp et al. (2024).

## Main definitions

* `AnomalyQuadraticForm`: Structure for quadratic forms arising from anomalies
* `QuadraticStructure`: Enhanced structure with regularity conditions
* `IsIsotropic`: Properties of isotropic vectors and subspaces

## Tags

quadratic forms, gauge anomalies, isotropic subspaces
-/

/-- Core structure for quadratic spaces over arbitrary fields. -/
class QuadraticStructure (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] where
  bilin : BilinForm k V
  regular : BilinForm.Nondegenerate bilin
  [char_ne_two : CharP k 0]
  to_quadratic : V → k := fun v => bilin v v

/-- The quadratic form structure arising from anomaly analysis. -/
structure AnomalyQuadraticForm (n : ℕ) where
  coeffs : Fin n → ℤ
  nonzero : ∀ i, coeffs i ≠ 0
  traceZero : ∑ i, coeffs i = 0
