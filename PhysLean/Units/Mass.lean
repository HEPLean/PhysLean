/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
import PhysLean.Units.Basic
/-!
# Mass

In this module we define the type `Mass`, which represents the mass of a particle,
in an arbitrary (but given) set of units.

-/
open Dimension
open NNReal

/-- Mass in a given but arbitary set of units. -/
abbrev Mass : Type := Measured M𝓭 ℝ≥0
