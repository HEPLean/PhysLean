/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.Group.Orthochronous
import PhysLean.Meta.Informal.Basic
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/
TODO "6VZNK" "Add definition of the restricted Lorentz group."
TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
  combiniation of a boost and a rotation."
TODO "6VZNU" "Prove restricted Lorentz group equivalent to connected component of identity
  of the Lorentz group."

namespace LorentzGroup

/-- The subgroup of the Lorentz group consisting of elements which are proper and orthochronous. -/
informal_definition Restricted where
  deps := [``LorentzGroup, ``IsProper, ``IsOrthochronous]
  tag := "6VZN7"

end LorentzGroup
