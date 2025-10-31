/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Curl
/-!

# Electrostatics

Electrostatics corresponds to the study of electric fields and potentials in the absence of
time variation or magnetic fields.

The study of electrostatics usually necessitates the use of distributions, since point charges
are often used to model charged particles. The formal definition of such distributions
are often glossed over in physics. As a result some of the definitions or proofs
within PhysLean's electrostatics may seem over the top - but this is necessary for complete
mathematical correctness.

This script is old, and will soon be replaced.

-/

namespace Electromagnetism
open Distribution SchwartzMap

/-- The type of static electric fields (i.e. time-independent electric fields), defined
  as distributions from `Space d` to `EuclideanSpace ℝ (Fin d)`. -/
abbrev StaticElectricField (d : ℕ := 3) := (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)

/-- The type of charge distributions. Mathematically this is equivalent to the
  type of distributions from `Space d` to `ℝ`. -/
abbrev ChargeDistribution (d : ℕ := 3) := (Space d) →d[ℝ] ℝ

/-- The type of static electric potentials.
  Mathematically defined as distributions from `Space d` to `ℝ`. -/
abbrev StaticElectricPotential (d : ℕ := 3) :=
  (Space d) →d[ℝ] ℝ

namespace StaticElectricField

/-- The static electric field associated with a static electric potential. -/
noncomputable def ofPotential {d : ℕ} (φ : StaticElectricPotential d) : StaticElectricField d :=
  - Space.distGrad φ

/-- Gauss's law for static electric fields. -/
def GaussLaw {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    Prop := Space.distDiv E = (1 / ε) • ρ

lemma gaussLaw_iff {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    E.GaussLaw ε ρ ↔ Space.distDiv E = (1 / ε) • ρ := by
  rw [GaussLaw]

TODO "IBQW4" "Generalize Faraday's law to arbitrary space dimensions.
  This may involve generalizing the curl operator to arbitrary dimensions."

/-- Faraday's law in 3d for static electric fields. -/
def FaradaysLaw (E : StaticElectricField) : Prop :=
  Space.distCurl E = 0

/-- If the electric field is of the form `-∇φ` then Faraday's law holds. -/
lemma ofPotential_faradaysLaw (φ : StaticElectricPotential) :
    FaradaysLaw (ofPotential φ) := by
  simp [ofPotential, FaradaysLaw]

end StaticElectricField

end Electromagnetism
