/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.IsViable.Elems
/-!

# Generation of Yukawa couplings

In this file we consider the singlets needed to regenerate the Yukawa couplings.

We ask whether these singlets regenerate a dangerous coupling in the super potential
at one or two insertions of the Yukawa singlets.

We find that there are no viable `Quanta` which do not
regenerate a dangerous coupling with at most two insertions of the Yukawa singlets.

We do not consider the Kahler potential in this file.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm Charges CodimensionOneConfig

/-!

## One insertion

The viable `Quanta` which do not regenerate a dangerous coupling at one
insertion of the Yukawa singlets.

-/

set_option maxRecDepth 2000 in
lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_one_eq_of_same :
    (viableElems same).toMultiset.filter (fun x =>
      ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 1)
    = {(some 2, some (-2), {(-1, 1, 2), (1, 2, -2)}, {(-1, 3, 0)}),
    (some 2, some (-2), {(-1, 0, 2), (1, 3, -2)}, {(-1, 3, 0)}),
    (some (-2), some 2, {(-1, 2, -2), (1, 1, 2)}, {(1, 3, 0)}),
    (some (-2), some 2, {(-1, 3, -2), (1, 0, 2)}, {(1, 3, 0)})} := by
  decide

set_option maxRecDepth 2000 in
lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_one_eq_of_NN :
    (viableElems nearestNeighbor).toMultiset.filter
      (fun x => ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 1)
    = {(some 6, some (-14), {(-9, 1, 2), (1, 2, -2)}, {(-7, 3, 0)}),
    (some 6, some (-14), {(-9, 0, 2), (1, 3, -2)}, {(-7, 3, 0)})}:= by
  decide

lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_one_eq_of_NtoNN :
    (viableElems nextToNearestNeighbor).toMultiset.filter
    (fun x => ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 1) = ∅ := by
  decide

/-!

## One or two insertions

The viable `Quanta` which do not regenerate a dangerous coupling with one or two
insertions of the Yukawa singlets.

-/

set_option maxRecDepth 2000 in
lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_two_eq_of_same :
    (viableElems same).toMultiset.filter (fun x =>
    ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 2) = ∅ := by
  decide

set_option maxRecDepth 2000 in
lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_two_eq_of_NN :
    (viableElems nearestNeighbor).toMultiset.filter (fun x =>
    ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 2) = ∅ := by
  decide

set_option maxRecDepth 2000 in
lemma viableElems_filter_yukawaSingletsRegenerateDangerousInsertion_two_eq_of_NtoNN :
    (viableElems nextToNearestNeighbor).toMultiset.filter (fun x =>
    ¬ (toCharges x).YukawaGeneratesDangerousAtLevel 2) = ∅ := by
  decide

end Quanta
end SU5U1

end FTheory
