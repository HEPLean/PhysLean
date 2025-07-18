/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Instances.Real
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.SpaceTime.Basic
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

-/
TODO "6V2FP" "Redefine the gauge group as a quotient of SU(3) x SU(2) x U(1) by a subgroup of ℤ₆."

namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The global gauge group of the Standard Model with no discrete quotients.
  The `I` in the Name is an indication of the statement that this has no discrete quotients. -/
abbrev GaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

/-- The subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₆-subgroup of `GaugeGroupI` with elements `(α^2 * I₃, α^(-3) * I₂, α)`,
where `α` is a sixth complex root of unity.

See https://math.ucr.edu/home/baez/guts.pdf
-/
@[sorryful]
def gaugeGroupℤ₆SubGroup [inst : Group GaugeGroupI] : Subgroup GaugeGroupI := sorry

/-- The smallest possible gauge group of the Standard Model, i.e., the quotient of `GaugeGroupI` by
the ℤ₆-subgroup `gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
@[sorryful]
def GaugeGroupℤ₆ : Type := sorry

/-- The ℤ₂subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₂-subgroup of `GaugeGroupI` derived from the ℤ₂ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition gaugeGroupℤ₂SubGroup where
  deps := [``GaugeGroupI]
  tag := "6V2GH"

/-- The gauge group of the Standard Model with a ℤ₂ quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroupℤ₂ where
  deps := [``GaugeGroupI, ``StandardModel.gaugeGroupℤ₂SubGroup]
  tag := "6V2GO"

/-- The ℤ₃-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₃-subgroup of `GaugeGroupI` derived from the ℤ₃ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition gaugeGroupℤ₃SubGroup where
  deps := [``GaugeGroupI]
  tag := "6V2GV"

/-- The gauge group of the Standard Model with a ℤ₃-quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₃-subgroup `gaugeGroupℤ₃SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroupℤ₃ where
  deps := [``GaugeGroupI, ``StandardModel.gaugeGroupℤ₃SubGroup]
  tag := "6V2G3"

/-- Specifies the allowed quotients of `SU(3) x SU(2) x U(1)` which give a valid
  gauge group of the Standard Model. -/
inductive GaugeGroupQuot : Type
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₆`. -/
  | ℤ₆ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₂`. -/
  | ℤ₂ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₃`. -/
  | ℤ₃ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the full SM gauge group. -/
  | I : GaugeGroupQuot

/-- The (global) gauge group of the Standard Model given a choice of quotient, i.e., the map from
`GaugeGroupQuot` to `Type` which gives the gauge group of the Standard Model for a given choice of
quotient.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroup where
  deps := [``GaugeGroupI, ``gaugeGroupℤ₂SubGroup, ``gaugeGroupℤ₃SubGroup,
    ``GaugeGroupQuot]
  tag := "6V2HF"

/-!

## Smoothness structure on the gauge group.

-/

/-- The gauge group `GaugeGroupI` is a Lie group. -/
informal_lemma gaugeGroupI_lie where
  deps := [``GaugeGroupI]
  tag := "6V2HL"

/-- For every `q` in `GaugeGroupQuot` the group `GaugeGroup q` is a Lie group. -/
informal_lemma gaugeGroup_lie where
  deps := [``GaugeGroup]
  tag := "6V2HR"

/-- The trivial principal bundle over SpaceTime with structure group `GaugeGroupI`. -/
informal_definition gaugeBundleI where
  deps := [``GaugeGroupI, ``SpaceTime]
  tag := "6V2HX"

/-- A global section of `gaugeBundleI`. -/
informal_definition gaugeTransformI where
  deps := [``gaugeBundleI]
  tag := "6V2H5"

end StandardModel
