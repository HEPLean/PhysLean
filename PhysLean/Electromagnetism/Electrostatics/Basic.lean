/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Distributions
/-!

# Electrostatics

In this file we define the static electric field as a distribution
on `Space d`.

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
  - Space.gradD φ

/-- Gauss's law for static electric fields. -/
def GaussLaw {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    Prop := Space.divD E = (1 / ε) • ρ

lemma gaussLaw_iff {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    E.GaussLaw ε ρ ↔ Space.divD E = (1 / ε) • ρ := by
  rw [GaussLaw]

TODO "IBQW4" "Generalize Faraday's law to arbitary space dimensions.
  This may involve generalizing the curl operator to arbitrary dimensions."

/-- Faraday's law in 3d for static electric fields. -/
def FaradaysLaw (E : StaticElectricField) : Prop :=
  Space.curlD E = 0

/-- If the electric field is of the form `-∇φ` then Faraday's law holds. -/
lemma ofPotential_faradaysLaw (φ : StaticElectricPotential) :
    FaradaysLaw (ofPotential φ) := by
  simp [ofPotential, FaradaysLaw]

end StaticElectricField

end Electromagnetism
