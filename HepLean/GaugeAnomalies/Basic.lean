
import HepLean
import Mathlib
/-!
# Basic Definitions for 2D Gauge Anomalies

This file contains the core definitions and structures needed for studying
gauge anomalies in two-dimensional quantum field theories, following
Camp et al. "Two-dimensional gauge anomalies and p-adic numbers" (2024).

## Main definitions

* `GaugeGroup`: Structure for gauge groups with smooth action
* `ChiralFermion`: Structure for chiral fermions
* `AnomalySystem`: Main structure combining gauge and fermionic data

## References

* [CGN24] Camp, Gripaios, Nguyen "Two-dimensional gauge anomalies and p-adic numbers"
  arXiv:2403.10611
* [Ser73] Serre "A Course in Arithmetic" Ch. IV
* [Cas78] Cassels "Rational Quadratic Forms" Ch. 4

## Tags

gauge theory, anomaly cancellation, quadratic forms, p-adic analysis
-/

open scoped BigOperators

/-- Core structure for gauge groups with smooth action. -/
structure GaugeGroup (G : Type*) [Group G] [TopologicalSpace G] where
  toGroup : Group G
  smooth : ∀ x : G, Continuous (fun y : G × G => x * y.1)

/-- Structure for a chiral fermion with representation data. -/
structure ChiralFermion (G : Type*) [Group G] where
  rep : Repr G      -- Representation of gauge group
  isLeft : Bool    -- Chirality (true = left-moving)

/-- Main structure combining gauge and fermionic data. -/
structure AnomalySystem where
  /-- The gauge group -/
  G : Type*
  [groupG : Group G]
  [topG : TopologicalSpace G]
  /-- Gauge group structure -/
  gaugeStr : GaugeGroup G
  /-- Number of fermions -/
  nFermions : ℕ
  /-- Fermion data -/
  fermions : Fin nFermions → ChiralFermion G
