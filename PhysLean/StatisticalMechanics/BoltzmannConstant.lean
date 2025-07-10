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

/-- The Boltzmann constant axiom. -/
axiom kBAx : {p : ℝ | 0 < p}

/-- The Boltzmann constant. -/
noncomputable def kB : ℝ := kBAx.1

/-- The Boltzmann constant is positive. -/
lemma kB_pos : 0 < kB := kBAx.2

/-- The Boltzmann constant is non-negative. -/
lemma kB_nonneg : 0 ≤ kB := le_of_lt kBAx.2

/-- The Boltzmann constant is not equal to zero. -/
lemma kB_neq_zero : kB ≠ 0 := by
  linarith [kB_pos]

end Constants
