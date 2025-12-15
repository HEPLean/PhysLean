/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

-/

open StandardModel

/-!

## A. The configuration space

-/

/-- The configuration space of the two Higgs doublet model. -/
structure TwoHiggsDoublet where
  /-- The first Higgs doublet. -/
  Φ1 : HiggsVec
  /-- The second Higgs doublet. -/
  Φ2 : HiggsVec
