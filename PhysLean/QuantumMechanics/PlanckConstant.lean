/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.NNReal.Defs
/-!

# Planck's constant

In this module we define the Planck's constant `ℏ` as a positive real number.
This is introduced as an axiom.

-/
open NNReal

namespace Constants

/-- Planck's constant. -/
axiom ℏ : Subtype fun x : ℝ => 0 < x

/-- Planck's constant is positive. -/
lemma ℏ_pos : 0 < (ℏ : ℝ) := ℏ.2

/-- Planck's constant is non-negative. -/
lemma ℏ_nonneg : 0 ≤ (ℏ : ℝ) := le_of_lt ℏ.2

/-- Planck's constant is not equal to zero. -/
lemma ℏ_ne_zero : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ.2

end Constants
