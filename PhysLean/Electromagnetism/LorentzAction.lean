/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Electromagnetism.FieldStrength.Basic

/-!

# The Lorentz action on the electric and magnetic fields.

The Lorentz group acts on a pair of a electric and magnetic field.
The map `toElectricMagneticField` is equivariant, which turns a field strength into a pair of
electric and magnetic fieldd, is equivariant with respect to this action.

## TODO

This file currently only contains semiformal results, which
-/

namespace Electromagnetism

/-- The Lorentz action on the electric and magnetic fields. -/
semiformal_result "6WNUS" lorentzAction :
  MulAction (LorentzGroup 3) (ElectricField × MagneticField)

open FieldStrength

/-- The equivalence `toElectricMagneticField` is equivariant with respect to the
  group action.

  (In this semiformal result `lorentzActionTemp` should be replaced with `lorentzAction`.) -/
semiformal_result "6V2O4" toElectricMagneticField_equivariant (d : ℕ)
  (g : LorentzGroup 3) (E : ElectricField) (B : MagneticField)
  (lorentzActionTemp : (LorentzGroup 3) → (ElectricField  × MagneticField)
    → (ElectricField  × MagneticField)) (x : SpaceTime) :
  (toElectricMagneticField.symm (lorentzActionTemp g  (E, B))).1  x=
  (realLorentzTensor.F.obj _).ρ g ((toElectricMagneticField.symm (E, B)).1 x)


end Electromagnetism
