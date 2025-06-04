/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
/-!

# Cardinality of nonPhenoConstrainedCharges

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

lemma nonPhenoConstrainedCharges_same_card : (nonPhenoConstrainedCharges same).card = 1148 := by
  rfl

lemma nonPhenoConstrainedCharges_nearestNeighbor_card :
    (nonPhenoConstrainedCharges nearestNeighbor).card = 407 := by
  rfl

lemma nonPhenoConstrainedCharges_nextToNearestNeighbor_card :
    (nonPhenoConstrainedCharges nextToNearestNeighbor).card = 234 := by
  rfl

end Charges

end SU5U1

end FTheory
