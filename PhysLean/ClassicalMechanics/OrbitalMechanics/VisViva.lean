/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe
-/

import Mathlib.Data.Real.Basic


/-!
# Circular Orbit Vis Viva
Defines the orbital speed for a circular orbit (v^2 = G M / r).
-/

namespace ClassicalMechanics

/-- Orbital speed for a circular orbit. -/
def vis_viva_circular (G M r : ℝ) : ℝ :=
  Real.sqrt (G * M / r)

/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma vis_viva_circular_sq (G M r : ℝ) (hr : r > 0) :
    (vis_viva_circular G M r)^2 = G * M / r := by
  simp [vis_viva_circular, Real.sqrt_sq hr.le]

end ClassicalMechanics
