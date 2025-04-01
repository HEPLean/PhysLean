/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
/-!

# Maxwell's equations

-/

namespace Electromagnetism

/-- An electromagnetic system consists of charge density, a current density,
  the speed ofl light and the electric permittivity. -/
structure EMSystem where
  /-- The speed of light. -/
  c : ℝ
  /-- The permittivity. -/
  ε₀ : ℝ

TODO "6V2UZ" "Charge density and current desnity should be generalized to signed measures,
  in such a way
  that they are still easy to work with and can be integrated with with tensor notation.
  See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Maxwell's.20Equations"

/-- The charge density. -/
abbrev ChargeDensity := SpaceTime → ℝ

/-- Current density. -/
abbrev CurrentDensity := SpaceTime → EuclideanSpace ℝ (Fin 3)

namespace EMSystem
variable (𝓔 : EMSystem)
open SpaceTime

/-- The permeability. -/
noncomputable def μ₀ : ℝ := 1/(𝓔.c^2 * 𝓔.ε₀)

/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)

end EMSystem

variable (𝓔 : EMSystem) (ρ : ChargeDensity) (J : CurrentDensity)
open SpaceTime

local notation "ε₀" => 𝓔.ε₀
local notation "μ₀" => 𝓔.μ₀

/-- Gauss's law for the Electric field. -/
def GaussLawElectric (E : ElectricField) : Prop :=
  ∀ x : SpaceTime, ε₀ * (∇⬝ E) x = ρ x

/-- Gauss's law for the Magnetic field. -/
def GaussLawMagnetic (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, (∇⬝ B) x = 0

/-- Ampère's law. -/
def AmpereLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, ∇× B x = μ₀ • (J x + ε₀ • ∂ₜ E x)

/-- Faraday's law. -/
def FaradayLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, ∇× E x = - ∂ₜ B x

/-- Maxwell's equations. -/
def MaxwellEquations (E : ElectricField) (B : MagneticField) : Prop :=
  GaussLawElectric 𝓔 ρ E ∧ GaussLawMagnetic B ∧
  FaradayLaw E B ∧ AmpereLaw 𝓔 J E B

TODO "6V2VD" "Show that if the charge density is spherically symmetric,
  then the electric field is also spherically symmetric."

end Electromagnetism
