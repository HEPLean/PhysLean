/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Insert
import PhysLean.StringTheory.FTheory.SU5U1.Charges
/-!

# Matter

This module contains the data of the matter content of the SU(5) GUT model in F-theory
with an additional U(1) symmetry.

## References

Krippendorf, Schafer-Nameki and Wong.
Froggatt-Nielson meets Mordell-Weil: A Phenomenological Survey of Global F-theory GUTs with U(1)s
<https://arxiv.org/pdf/1507.05961>.

-/
namespace FTheory

namespace SU5U1

/-- A type for the `U(1)`-charges of matter.
  This is often denoted `q`. -/
abbrev Charge : Type := ℤ

/-- A type for the chirality of matter. This is induced by G₄-flux.
  This is often denoted `M`. -/
abbrev Chirality : Type := ℕ

/-- A type for the hypercharge flux associated with matter curves.
  This is often denote `N`. -/
abbrev HyperChargeFlux : Type := ℤ

/-- The matter content, assumed to sit in the 5-bar or 10d representation of
  `SU(5)`. -/
structure MatterContent (I : CodimensionOneConfig) where
  /-- The number of matter fields in the 5-bar representation of `SU(5)`. -/
  numberBarFive : ℕ
  /-- The number of matter fields in the 10d representation of `SU(5)`. -/
  numberTen : ℕ
  /-- The chirality, charge and hyperChargeFlux associated with the 5-bar representations. -/
  quantaBarFive : Multiset (Chirality × HyperChargeFlux × Charge)
  /-- The chirality, charge and hyperChargeFlux associated with the 10d representations. -/
  quantaTen : Multiset (Chirality × HyperChargeFlux × Charge)
  /-- The cardinality of `quantaBarFive` should equal `numberBarFive`. -/
  quantaBarFive_card : quantaBarFive.card = numberBarFive
  /-- The cardinality of `quantaTen` should equal `numberTen`. -/
  quantaTen_card : quantaTen.card = numberTen
  /-- There is no matter in the 5-bar representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_bar_five : ∀ q ∈ quantaBarFive, (q.1 = 0 → q.2.1 ≠ 0)
  /-- There is no matter in the 10d representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_ten : ∀ q ∈ quantaTen, (q.1 = 0 → q.2.1 ≠ 0)

end SU5U1

end FTheory
