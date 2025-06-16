/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.DeriveFintype
/-!

# The field labels

The field labels of the `SU(5)` SUSY GUT is an inductive type that labels
the allowed representations present in the theory.

-/

namespace SuperSymmetry
namespace SU5

/-- The types of field present in an SU(5) GUT. -/
inductive FieldLabel
  | fiveBarHu
  | fiveHu
  | fiveBarHd
  | fiveHd
  | fiveBarMatter
  | fiveMatter
  | tenMatter
deriving DecidableEq, Fintype

/-- The R-Parity of a field, landding on `1` if it is in the non-trivial representation
  and `0` otherwise. -/
def FieldLabel.RParity : FieldLabel → Fin 2
  | fiveBarHu => 0
  | fiveHu => 0
  | fiveBarHd => 0
  | fiveHd => 0
  | fiveBarMatter => 1
  | fiveMatter => 1
  | tenMatter => 1

end SU5
end SuperSymmetry
