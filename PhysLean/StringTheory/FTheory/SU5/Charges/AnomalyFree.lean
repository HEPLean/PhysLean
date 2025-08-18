/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Quanta.Basic
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Map
/-!

# Anomaly cancellation

In this module we define the proposition `IsAnomalyFree` on charges, which states
that the charges can be extended to quanta which are anomaly free.

We give the viable charges which are anomaly free for each of the three codimension one
configurations. This is in the lemma `viable_anomalyFree`.

-/
namespace FTheory

namespace SU5

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig
open Tree
open PhysLean

/-!

## Anomaly coefficents of charges

-/

variable {𝓩 : Type}
/-- The condition on a collection of charges `c` that it extends to an anomaly free `Quanta`.
  That anomaly free `Quanta` is not tracked by this proposition. -/
def IsAnomalyFree [DecidableEq 𝓩] [CommRing 𝓩] (c : Charges 𝓩) : Prop :=
  ∃ x ∈ Quanta.ofChargesExpand c, Quanta.AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2

instance [DecidableEq 𝓩] [CommRing 𝓩] {c : Charges 𝓩} : Decidable (IsAnomalyFree c) :=
  Multiset.decidableExistsMultiset

set_option maxRecDepth 2000 in
/-- The viable charges which are anomaly free. -/
lemma viable_anomalyFree (I : CodimensionOneConfig) :
    (viableCharges I).filter IsAnomalyFree =
    (match I with
    | .same => {(some 2, some (-2), {-1, 1}, {-1}), (some (-2), some 2, {-1, 1}, {1})}
    | .nearestNeighbor => {(some 6, some (-14), {-9, 1}, {-7})}
    | .nextToNearestNeighbor => ∅) := by
  revert I
  decide

end Charges

end SU5

end FTheory
