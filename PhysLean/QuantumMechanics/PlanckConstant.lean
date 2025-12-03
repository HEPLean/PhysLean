/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.NNReal.Defs
import PhysLean.Meta.TODO.Basic
/-!

# Planck's constant

In this module we define the Planck's constant `ℏ` as a positive real number.
This is introduced as an axiom.

-/

TODO "DOC13" "Add documentation explaining the physical significance of Planck's constant
  and its role in quantum mechanics, including references to the uncertainty principle."

TODO "DOC14" "Document the choice of using an axiom for ℏ and discuss how this relates
  to the unit system choices in PhysLean."

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
