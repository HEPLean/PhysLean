/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Basic
/-!

# Elements of the non pheno-constrained charges for `nearestNeighbor`

For the `CodimensionOneConfig`, `nearestNeighbor`, we give trees of charges which
are not pheno-constrained, and prove properties about them.

These trees are complete in the sense that they contain all the non pheno-constrained, complete,
charges which are in
`ofFinset nearestNeighbor.allowedBarFiveCharges nearestNeighbor.allowedTenCharges`.
We use the `FourTree` type here for efficiency.

We break the properties of these trees into smaller modules, to aid in
speed of building.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open CodimensionOneConfig
open PhysLean Tree

/-- For `I = nearestNeighbor` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling.

  These trees can be found with e.g.
  `#eval nonPhenoConstrainedChargesExt nextToNearestNeighbor`. -/
def nonPhenoConstrainedChargesNearestNeighbor :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  root {trunk (some (-14)) {branch (some 1) {twig {-14} {leaf {-2, 3}},
    twig {11} {leaf {-2, 3}, leaf {-7, 8}}},
    branch (some 11) {twig {-14} {leaf {-2, 13}}},
    branch (some (-9)) {twig {-14} {leaf {-12, 3}}, twig {1} {leaf {-12, 3}},
      twig {11} {leaf {-12, 3}}, twig {-14, 1} {leaf {-12, 3}}},
    branch (some (-4)) {twig {1} {leaf {-12, 8}},
    twig {-14} {leaf {-2}, leaf {-12, 8}, leaf {3, -2}, leaf {13, -2}},
    twig {-9} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}},
    twig {11} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {3, -2}},
    twig {-14, -9} {leaf {-2}, leaf {-12, 8}},
    twig {-14, 1} {leaf {-12, 8}},
    twig {-14, 11} {leaf {-2}, leaf {-12, 8}},
    twig {-9, 11} {leaf {-12, 8}},
    twig {-14, -9, 11} {leaf {-12, 8}}},
    branch (some 6) {twig {-9} {leaf {-7, 13}},
    twig {-14} {leaf {3}, leaf {-12, 3}, leaf {-2, 3}, leaf {13, 3}},
    twig {-4} {leaf {3}, leaf {-7, 13}, leaf {-12, 3}, leaf {13, 3}},
    twig {1} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {11} {leaf {3}, leaf {-7, 13}, leaf {-12, 3}, leaf {-2, 3}, leaf {13, 3}},
    twig {-9, 11} {leaf {-7, 13}},
    twig {-14, -4} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-14, 1} {leaf {3}, leaf {-12, 3}},
    twig {-4, 11} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {1, 11} {leaf {3}, leaf {13, 3}}}},
  trunk (some (-9)) {branch (some 1) {twig {-9} {leaf {-12, 13}, leaf {-7, -12, 13}},
    twig {-4} {leaf {-12, 13}, leaf {-7, -12, 13}}},
    branch (some 6) {twig {11} {leaf {-2, 8}, leaf {-7, 13}, leaf {-12, -2, 8}},
    twig {-9} {leaf {-2, 8}, leaf {-7, 13}, leaf {-12, -2, 8}, leaf {-12, -7, 13}},
    twig {-4} {leaf {-7, 13}, leaf {-12, -7, 13}},
    twig {-9, 11} {leaf {-7, 13}}},
    branch (some (-4)) {twig {-14} {leaf {-2}, leaf {-12, 8}},
    twig {-14, -9} {leaf {-2}, leaf {-12, 8}},
    twig {-14, 11} {leaf {-2}, leaf {-12, 8}},
    twig {-9, 11} {leaf {-12, 8}},
    twig {-9} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {8, -2}, leaf {-12, 8, -2}},
    twig {11} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {8, -2}, leaf {-12, 8, -2}},
    twig {-14, -9, 11} {leaf {-12, 8}}},
    branch (some (-14)) {twig {6} {leaf {-7}},
    twig {1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 6} {leaf {-7}},
    twig {-4, 6} {leaf {-7}},
    twig {1, 11} {leaf {-7}},
    twig {6, 11} {leaf {-7}},
    twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}, leaf {8, -12, -2}},
    twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7},
      leaf {8, -12, -2}, leaf {-12, 13, -7}},
    twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
    twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}, leaf {-12, 13, -7}},
    twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 6} {leaf {-7}},
    twig {-9, 1, 11} {leaf {-7}},
    twig {-9, 6, 11} {leaf {-7}},
    twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}},
  trunk (some (-4)) {branch (some (-9)) {twig {-4} {leaf {-12, 3}}, twig {1} {leaf {-12, 3}},
    twig {11} {leaf {-12, 3}}, twig {-4, 11} {leaf {-12, 3}}},
    branch (some 1) {twig {11} {leaf {-7, 8}, leaf {13, -7, 8}},
    twig {-9} {leaf {-12, 13}, leaf {-7, -12, 13}},
    twig {-4} {leaf {-12, 13}, leaf {-7, -12, 13}}},
    branch (some 11) {twig {-14} {leaf {-2, 13}}, twig {1} {leaf {3, 8}, leaf {13, 3, 8}}},
    branch (some 6) {twig {-14} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-9} {leaf {-7, 13}, leaf {-12, -7, 13}},
    twig {-4} {leaf {3}, leaf {-7, 13}, leaf {-12, 3}, leaf {13, 3}, leaf {-12, -7, 13}},
    twig {-9, 11} {leaf {-7, 13}},
    twig {11} {leaf {3}, leaf {-7, 13}, leaf {-12, 3}, leaf {13, 3}, leaf {8, -7, 13}},
    twig {-14, -4} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-14, 1} {leaf {3}, leaf {-12, 3}},
    twig {1} {leaf {3}, leaf {-12, 3}, leaf {8, 3}, leaf {13, 3}, leaf {8, 13, 3}},
    twig {-4, 11} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {1, 11} {leaf {3}, leaf {13, 3}}},
    branch (some (-14)) {twig {6} {leaf {-7}},
    twig {1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 6} {leaf {-7}},
    twig {-4, 6} {leaf {-7}},
    twig {1, 11} {leaf {-7}},
    twig {6, 11} {leaf {-7}},
    twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}, leaf {-12, 13, -7}},
    twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
    twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}, leaf {-12, 13, -7}},
    twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 6} {leaf {-7}},
    twig {-9, 1, 11} {leaf {-7}},
    twig {-9, 6, 11} {leaf {-7}},
    twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}, leaf {13, -7},
      leaf {8, 13, -7}},
    twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}},
  trunk (some 1) {branch (some (-9)) {twig {-14} {leaf {-12, 3}},
    twig {-4} {leaf {-12, 3}},
    twig {1} {leaf {-12, 3}},
    twig {11} {leaf {-12, 3}},
    twig {-14, -4} {leaf {-12, 3}},
    twig {-14, 1} {leaf {-12, 3}},
    twig {-4, 11} {leaf {-12, 3}}},
    branch (some 11) {twig {-14} {leaf {-2, 13}}, twig {1} {leaf {3, 8}, leaf {13, 3, 8}}},
    branch (some (-4)) {twig {1} {leaf {-12, 8}},
    twig {-14} {leaf {-2}, leaf {-12, 8}, leaf {13, -2}},
    twig {-14, 1} {leaf {-12, 8}},
    twig {-14, 11} {leaf {-2}, leaf {-12, 8}},
    twig {11} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {8, -2}, leaf {-12, 8, -2}}},
    branch (some 6) {twig {-14} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-4} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-9} {leaf {-2, 8}, leaf {-12, -2, 8}},
    twig {-14, -4} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-14, 1} {leaf {3}, leaf {-12, 3}},
    twig {1} {leaf {3}, leaf {-12, 3}, leaf {8, 3}, leaf {13, 3}, leaf {8, 13, 3}}},
    branch (some (-14)) {twig {6} {leaf {-7}},
    twig {-4} {leaf {-7}, leaf {-12, -7}},
    twig {1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 6} {leaf {-7}},
    twig {-4, 6} {leaf {-7}},
    twig {1, 11} {leaf {-7}},
    twig {6, 11} {leaf {-7}},
    twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -12, -2}},
    twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}, leaf {8, -12, -2}},
    twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 6} {leaf {-7}},
    twig {-9, 1, 11} {leaf {-7}},
    twig {-9, 6, 11} {leaf {-7}},
    twig {-9, 11} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}},
  trunk (some 6) {branch (some 1) {twig {-9} {leaf {-12, 13}}},
    branch (some (-4)) {twig {-9} {leaf {-12, 8}}, twig {1} {leaf {-12, 8}}, twig {11}
      {leaf {-12, 8}}, twig {-9, 11} {leaf {-12, 8}}},
    branch (some 11) {twig {1} {leaf {3, 8}, leaf {13, 3, 8}}},
    branch (some (-14)) {twig {6} {leaf {-7}},
    twig {-9} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 6} {leaf {-7}},
    twig {-4, 6} {leaf {-7}},
    twig {1, 11} {leaf {-7}},
    twig {6, 11} {leaf {-7}},
    twig {11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 6} {leaf {-7}},
    twig {-9, 1, 11} {leaf {-7}},
    twig {-9, 6, 11} {leaf {-7}},
    twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}},
  trunk (some 11) {branch (some (-9)) {twig {-14} {leaf {-12, 3}},
    twig {-4} {leaf {-12, 3}},
    twig {1} {leaf {-12, 3}},
    twig {11} {leaf {-12, 3}},
    twig {-14, -4} {leaf {-12, 3}},
    twig {-14, 1} {leaf {-12, 3}},
    twig {-4, 11} {leaf {-12, 3}}},
    branch (some 1) {twig {-14} {leaf {-2, 3}}, twig {11} {leaf {-2, 3}, leaf {-7, 8},
      leaf {13, -7, 8}}},
    branch (some (-4)) {twig {1} {leaf {-12, 8}},
    twig {-14} {leaf {-2}, leaf {-12, 8}, leaf {3, -2}, leaf {13, -2}},
    twig {-14, -9} {leaf {-2}, leaf {-12, 8}},
    twig {-14, 1} {leaf {-12, 8}},
    twig {-14, 11} {leaf {-2}, leaf {-12, 8}},
    twig {-9, 11} {leaf {-12, 8}},
    twig {-9} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {8, -2}, leaf {-12, 8, -2}},
    twig {11} {leaf {-2}, leaf {-12, 8}, leaf {-12, -2}, leaf {3, -2}, leaf {8, -2},
      leaf {-12, 8, -2}},
    twig {-14, -9, 11} {leaf {-12, 8}}},
    branch (some 6) {twig {-14} {leaf {3}, leaf {-12, 3}, leaf {-2, 3}, leaf {13, 3}},
    twig {-4} {leaf {3}, leaf {-7, 13}, leaf {-12, 3}, leaf {13, 3}},
    twig {-9} {leaf {-2, 8}, leaf {-7, 13}, leaf {-12, -2, 8}},
    twig {-9, 11} {leaf {-7, 13}},
    twig {11} {leaf {3}, leaf {-2, 8}, leaf {-7, 13}, leaf {-12, 3}, leaf {-2, 3},
      leaf {13, 3}, leaf {-12, -2, 8}, leaf {8, -7, 13}},
    twig {-14, -4} {leaf {3}, leaf {-12, 3}, leaf {13, 3}},
    twig {-4, 11} {leaf {3}, leaf {-12, 3}, leaf {13, 3}}},
    branch (some (-14)) {twig {6} {leaf {-7}},
    twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 6} {leaf {-7}},
    twig {-4, 6} {leaf {-7}},
    twig {1, 11} {leaf {-7}},
    twig {6, 11} {leaf {-7}},
    twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}, leaf {8, -12, -2}},
    twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
    twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
    twig {-9, -4, 6} {leaf {-7}},
    twig {-9, 1, 11} {leaf {-7}},
    twig {-9, 6, 11} {leaf {-7}},
    twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
    twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}, leaf {13, -7},
      leaf {8, -12, -2}, leaf {8, 13, -7}},
    twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}}}

end Charges

end SU5U1

end FTheory
