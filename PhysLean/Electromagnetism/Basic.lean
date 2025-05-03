/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Electromagnetism

In this file we define the electric field, the magnetic field, and the field strength tensor.

-/

namespace Electromagnetism

/-- The electric field is a map from `d`+1 dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)

/-- The magnetic field is a map from `d+1` dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)

open IndexNotation
open realLorentzTensor

/-- The vector potential of an electromagnetic field-/
abbrev VectorPotential (d : ℕ := 3) := SpaceTime d → ℝT[d, .up]

/-- The electric permittivity and the magnetic permeability of free space. -/
structure EMSystem where
  /-- The permittivity of free space. -/
  ε₀ : ℝ
  /-- The permeability of free space. -/
  μ₀ : ℝ

TODO "6V2UZ" "Charge density and current density should be generalized to signed measures,
  in such a way
  that they are still easy to work with and can be integrated with with tensor notation.
  See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Maxwell's.20Equations"

/-- The charge density. -/
abbrev ChargeDensity := Time → Space → ℝ

/-- Current density. -/
abbrev CurrentDensity := Time → Space → EuclideanSpace ℝ (Fin 3)

namespace EMSystem
variable (𝓔 : EMSystem)
open SpaceTime

/-- The speed of light. -/
noncomputable def c : ℝ := 1/(√(𝓔.μ₀ * 𝓔.ε₀))

/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)

end EMSystem

end Electromagnetism
