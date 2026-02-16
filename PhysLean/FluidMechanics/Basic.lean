/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
/-!
This module introduces the idea of an ideal fluid and the mass flux density. The rest of the early workings is to be seen in ./IdealFluid/
-/
open scoped InnerProductSpace

structure IdealFluid where
  density: Time → Space → ℝ
  velocity: Time → Space→ Space
  pressure: Time → Space → ℝ

namespace IdealFluid

def massFluxDensity (F: IdealFluid) (t : Time) (pos : Space ) :
    Space := (IdealFluid.density F t pos) • (IdealFluid.velocity F t pos)

end IdealFluid
