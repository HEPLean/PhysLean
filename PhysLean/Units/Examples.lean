/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.WithDim.Basic
/-!

# Examples of units in PhysLean

In this module we give some examples of how to use the units system in PhysLean.
This module should not be imported into any other module, and the results here
should not be used in the proofs of any other results other then those in this file.

-/

namespace UnitExamples
open Dimension CarriesDimension UnitChoices UnitDependent
/-!

## Defining a length dependent on units

-/

/-- The length corresponding to 400 meters. -/
noncomputable def meters400 : Dimensionful (WithDim L𝓭 ℝ) := toDimensionful SI ⟨400⟩

/-- Changing that length to miles. -/
example : meters400.1 {SI with length := LengthUnit.miles} = ⟨400/1609.344⟩ := by
  simp [meters400, toDimensionful_apply_apply, dimScale, LengthUnit.miles]
  ext
  simp
  trans 1609.344⁻¹ * 400
  · rfl
  norm_num

/-!

## Proving propositions are dimensionally correct

-/

/-- The speed of light as a dimensionful quantity. -/
noncomputable def speedOfLight : Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ) :=
  toDimensionful SI ⟨299792458⟩

/-- The equation `E = m c^2`, in this equation we `E` and `m` are implicitly in the
  units `u`, while the speed of light is explicitly written in those units. -/
def EnergyMass (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (u : UnitChoices) : Prop :=
    E.1 = m.1 * (speedOfLight.1 u).1 ^ 2

/-- The equation `E = m c^2`, in this version everything is written explicitly in
  terms of a choice of units. -/
def EnergyMass' (m : Dimensionful (WithDim M𝓭 ℝ))
    (E : Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ))
    (u : UnitChoices) : Prop :=
    (E.1 u).1 = (m.1 u).1 * (speedOfLight.1 u).1 ^ 2

/-- The lemma that the proposition `EnergyMass` is dimensionally correct-/
lemma energyMass_isDimensionallyInvariant :
    IsDimensionallyInvariant EnergyMass := by
  /- Scale such that the unit u1 is taken to u2. -/
  intro u1 u2
  /- Let `m` be the mass, `E` be the energy and `u` be the acutal units we start with. -/
  funext m E u
  calc _
    _ = ((scaleUnit u2 u1 E).1 =
        (scaleUnit u2 u1 m).1 * (speedOfLight.1 (scaleUnit u2 u1 u)).1 ^ 2) := by
      rfl
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        (u2.dimScale u1 M𝓭).1 * m.1 * ((u2.dimScale u1 (L𝓭 * T𝓭⁻¹)).1 *
          (speedOfLight.1 u).1) ^ 2) := by
      conv_lhs => rw [scaleUnit_apply, scaleUnit_apply, Dimensionful.of_scaleUnit]
      rfl
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 M𝓭 * u2.dimScale u1 (L𝓭 * T𝓭⁻¹) * u2.dimScale u1 (L𝓭 * T𝓭⁻¹)).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
        simp
        ring_nf
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * (L𝓭 * T𝓭⁻¹) * (L𝓭 * T𝓭⁻¹))).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
        simp
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1) *
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
      congr 4
      aesop
    _ = ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1 • E.1 =
        ((u2.dimScale u1 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)).1) •
          (m.1 * ((speedOfLight.1 u).1) ^ 2)) := by
      rfl
  simp
  rfl

/-! We now explore the consequences of `energyMass_isDimensionallyInvariant` and how
  we can use it. -/

lemma example1_energyMass : EnergyMass ⟨2⟩ ⟨2 * 299792458 ^ 2⟩ SI := by
  simp [EnergyMass]
  simp [speedOfLight, toDimensionful_apply_apply, dimScale, SI]

/- The lemma `energyMass_isDimensionallyInvariant` allows us to scale the units
  of `example1_energyMass`, that is - we proved it in one set of units, but we get the result
  in any set of units. -/
lemma example2_energyMass (u2 : UnitChoices) :
    EnergyMass (scaleUnit SI u2 ⟨2⟩)
      (scaleUnit SI u2 ⟨2 * 299792458 ^ 2⟩) u2 := by
  conv_rhs => rw [← UnitChoices.scaleUnit_apply_fst SI u2]
  have h1 := congrFun (congrFun (congrFun (energyMass_isDimensionallyInvariant SI u2)
    (scaleUnit SI u2 ⟨2⟩))
    (scaleUnit SI u2 ⟨2 * 299792458 ^ 2⟩)) (scaleUnit SI u2 SI)
  rw [← h1]
  simp [instUnitDependentTwoSided, instUnitDependentForall_1]
  exact example1_energyMass

TODO "LCR7N" "Add an example involving derivatives."

end UnitExamples
