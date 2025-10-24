/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
/-!

# Maxwell's equations

Note that currently the equations are defined for isotropic and homogeneous domains.

-/

namespace Electromagnetism

/-- An optcial medium refers to an isotropic medium
  (which may or may not be free space)
  which consists of the electric permittivity
  and the magnetic permeability. -/
structure OpticalMedium where
  /-- The permittivity. -/
  ε : ℝ
  /-- The permeability. -/
  μ : ℝ
  eps_ge_zero : ε > 0
  mu_ge_zero : μ > 0

variable (𝓔 : OpticalMedium) (ρ : ChargeDensity) (J : CurrentDensity)
open SpaceTime

local notation "ε" => 𝓔.ε
local notation "μ" => 𝓔.μ
open Time

/-- Gauss's law for the Electric field. -/
def GaussLawElectric (E : ElectricField) : Prop :=
  ∀ t : Time, ∀ x : Space, ε * (∇ ⬝ E t) x = ρ t x

/-- Gauss's law for the Magnetic field. -/
def GaussLawMagnetic (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ ⬝ B t) x = 0

/-- Ampère's law. -/
def AmpereLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × B t) x = μ • (J t x + ε • ∂ₜ (fun t => E t x) t)

/-- Faraday's law. -/
def FaradayLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × E t) x = - ∂ₜ (fun t => B t x) t

/-- Maxwell's equations. -/
def MaxwellEquations (E : ElectricField) (B : MagneticField) : Prop :=
  GaussLawElectric 𝓔 ρ E ∧ GaussLawMagnetic B ∧
  AmpereLaw 𝓔 J E B ∧ FaradayLaw E B

TODO "6V2VD" "Show that if the charge density is spherically symmetric,
  then the electric field is also spherically symmetric."

end Electromagnetism
