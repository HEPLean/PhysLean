/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.NNReal.Defs
/-!

## Boltzmann constant

In this file we define the Boltzmann constant `kB` as a non-negative real number.
This is introduced as an axiom.

-/
open NNReal

namespace Constants

/-- The Boltzmann constant. -/
axiom kB : ℝ≥0

/-- The Boltzmann constant is non-negative. -/
lemma kB_nonneg : 0 ≤ kB := by
  apply NNReal.coe_nonneg

end Constants
