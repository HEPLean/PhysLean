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
  the speed of light and the electric permittivity. -/
structure EMSystem where
  /-- The speed of light. -/
  c : ℝ
  /-- The permittivity. -/
  ε₀ : ℝ

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

/-- The permeability. -/
noncomputable def μ₀ : ℝ := 1/(𝓔.c^2 * 𝓔.ε₀)

/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)

end EMSystem

variable (𝓔 : EMSystem) (ρ : ChargeDensity) (J : CurrentDensity)
open SpaceTime

local notation "ε₀" => 𝓔.ε₀
local notation "μ₀" => 𝓔.μ₀
open Time

/-- Gauss's law for the Electric field. -/
def GaussLawElectric (E : ElectricField) : Prop :=
  ∀ t : Time, ∀ x : Space, ε₀ * (∇ ⬝ E t) x = ρ t x

/-- Gauss's law for the Magnetic field. -/
def GaussLawMagnetic (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ ⬝ B t) x = 0

/-- Ampère's law. -/
def AmpereLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × B t) x = μ₀ • (J t x + ε₀ • ∂ₜ (fun t => E t x) t)

/-- Faraday's law. -/
def FaradayLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × E t) x = - ∂ₜ (fun t => B t x) t

/-- Maxwell's equations. -/
def MaxwellEquations (E : ElectricField) (B : MagneticField) : Prop :=
  GaussLawElectric 𝓔 ρ E ∧ GaussLawMagnetic B ∧
  FaradayLaw E B ∧ AmpereLaw 𝓔 J E B

TODO "6V2VD" "Show that if the charge density is spherically symmetric,
  then the electric field is also spherically symmetric."

end Electromagnetism
