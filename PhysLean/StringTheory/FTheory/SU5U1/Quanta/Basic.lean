/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.FiveQuanta
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.TenQuanta
/-!

# Quanta of representations

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

-/
namespace FTheory

namespace SU5U1
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta associated with the representations in a `SU(5) x U(1)` F-theory.
  This contains the value of the charges and the flux intergers `(M, N)` for the
  5-bar matter content and the 10d matter content, and the charges of the `Hd` and
  `Hu` particles (there values of `(M,N)` are not included as they are
  forced to be `(0, 1)` and `(0, -1)` respectively. -/
abbrev Quanta : Type := Option ℤ × Option ℤ × FiveQuanta × TenQuanta

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm Charges

instance : DecidableEq Quanta := instDecidableEqProd

/-- The underlying `Charges` of a `Quanta`. -/
def toCharges (x : Quanta) : Charges :=
  (x.1, x.2.1, x.2.2.1.toCharges.toFinset, x.2.2.2.toCharges.toFinset)

end Quanta

end SU5U1

end FTheory
