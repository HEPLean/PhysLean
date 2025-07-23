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

abbrev StaticElectricField (d : ℕ := 3) := (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)

abbrev ChargeDistribution (d : ℕ := 3) := (Space d) →d[ℝ] ℝ

abbrev StaticElectricPotential (d : ℕ := 3) :=
  (Space d) →d[ℝ] ℝ

namespace StaticElectricField

noncomputable def ofPotential {d : ℕ} (φ : StaticElectricPotential d) : StaticElectricField d :=
  - Space.gradD φ

def GaussLaw {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    Prop := Space.divD E = (1 / ε) • ρ

lemma gaussLaw_iff {d : ℕ} (E : StaticElectricField d) (ε : ℝ) (ρ : ChargeDistribution d) :
    E.GaussLaw ε ρ ↔ Space.divD E = (1 / ε) • ρ := by
  rw [GaussLaw]

def FaradaysLaw (E : StaticElectricField) : Prop :=
  Space.curlD E = 0

/-- If the electric field is of the form `-∇φ` then Faraday's law holds. -/
lemma ofPotential_faradaysLaw (φ : StaticElectricPotential) :
    FaradaysLaw (ofPotential φ) := by
  simp [ofPotential, FaradaysLaw]

end StaticElectricField


end Electromagnetism
