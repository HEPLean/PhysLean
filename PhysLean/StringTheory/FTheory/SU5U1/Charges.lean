/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Insert
import PhysLean.Meta.TODO.Basic
/-!

# Allowed charges

For an SU(5) GUT model in F-theory with an additional U(1) symmetry,
this module gives the possible charges of the matter fields.

## References

Lawrie, Schafer-Nameki and Wong.
F-theory and All Things Rational: Surveying U(1) Symmetries with Rational Sections
<https://arxiv.org/pdf/1504.05593>. Page 6.

## TODO

The results in this file are currently stated, but not proved.

-/

TODO "AETF6" "The results in this file are currently stated, but not proved.
  They should should be proved following e.g. https://arxiv.org/pdf/1504.05593.
  This is a large project."

namespace FTheory

namespace SU5U1

/-- The distinct codimension one configurations of the
  zero-section (`σ₀`) relativity to the additional rational section (`σ₁`s). -/
inductive CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the same `ℙ¹` of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(01)}` -/
  | same : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0|1)}` -/
  | nearestNeighbor : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the next to nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0||1)}` -/
  | nextToNearestNeighbor : CodimensionOneConfig
deriving DecidableEq

namespace CodimensionOneConfig

/-- The allowed `U(1)`-charges of matter in the 5-bar representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedBarFiveCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-14, -9, -4, 1, 6, 11}
  | nextToNearestNeighbor => {-13, -8, -3, 2, 7, 12}

/-- The allowed `U(1)`-charges of matter in the 10d representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedTenCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-12, -7, -2, 3, 8, 13}
  | nextToNearestNeighbor => {-9, -4, 1, 6, 11}

end CodimensionOneConfig
end SU5U1

end FTheory
