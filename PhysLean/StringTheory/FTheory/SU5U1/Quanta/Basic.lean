/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Fluxes.NoExotics.ToList
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Lemmas
/-!

# Quanta of representations

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- The quanta of 5-bar representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev FiveQuanta : Type := Multiset (ℤ × ℤ × ℤ)

namespace FiveQuanta

/-- The underlying `FluxesFive` from a `FiveQuanta`. -/
def toFluxesFive (x : FiveQuanta) : FluxesFive := x.map Prod.snd

/-- The underlying Multiset charges from a `FiveQuanta`. -/
def toCharges (x : FiveQuanta) : Multiset ℤ := x.map Prod.fst

end FiveQuanta

/-- The quanta of w0d representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev TenQuanta : Type := Multiset (ℤ × ℤ × ℤ)

namespace TenQuanta

/-- The underlying `FluxesTen` from a `TenQuanta`. -/
def toFluxesTen (x : TenQuanta) : FluxesTen := x.map Prod.snd

/-- The underlying Multiset charges from a `TenQuanta`. -/
def toCharges (x : TenQuanta) : Multiset ℤ := x.map Prod.fst

end TenQuanta

end SU5U1

end FTheory
