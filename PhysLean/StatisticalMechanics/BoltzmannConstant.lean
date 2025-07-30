/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.NNReal.Defs
/-!

# Boltzmann constant

The Boltzmann constant is a constant `kB` of dimension `m² kg s⁻² K⁻¹`, that is
`Energy/Temperature`. It is named after Ludwig Boltzmann.

In this module we axiomise the existence of the Boltzmann constant in a given (but arbitrary)
set of units.

-/
open NNReal

namespace Constants

/-- The axiom introducing the Boltzmann constant in a given but arbitrary set of units. -/
axiom kBAx : {p : ℝ | 0 < p}

/-- The Boltzmann constant in a given but arbitary set of units.
  Boltzman's constant has dimension equivalent to `Energy/Temperature`. -/
noncomputable def kB : ℝ := kBAx.1

/-- The Boltzmann constant is positive. -/
lemma kB_pos : 0 < kB := kBAx.2

/-- The Boltzmann constant is non-negative. -/
lemma kB_nonneg : 0 ≤ kB := le_of_lt kBAx.2

/-- The Boltzmann constant is not equal to zero. -/
lemma kB_neq_zero : kB ≠ 0 := by
  linarith [kB_pos]

end Constants
