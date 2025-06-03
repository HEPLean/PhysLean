/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Basic
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Elems
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Basic
/-!

# Elements of the non pheno-constrained charges

For each `CodimensionOneConfig`, `I`, we give trees of charges which are not pheno-constrained,
and prove properties about them.

These trees are complete in the sense that they contain all the non pheno-constrained, complete,
charges which are in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`.
We use the `Tree` type defined in `FTheory.SU5U1.Charges.Tree.Basic` here for efficiency.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile
open CodimensionOneConfig
open Tree Leaf Twig Branch Trunk

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling. Unlike `nonPhenoConstrainedCharges`, these trees are calculated
  and therefore not good when using `decide` etc.
-/
def nonPhenoConstrainedChargesExt (I : CodimensionOneConfig) : Tree :=
  let completionTopYukawa :=  ((((irreducibleElems I topYukawa).map
    (fromChargeProfile topYukawa)).bind
    (completions I.allowedBarFiveCharges I.allowedTenCharges)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addOneTopYukawa := (((completionTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addTwoTopYukawa :=  (((addOneTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addThreeTopYukawa :=  (((addTwoTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  Tree.fromMultiset (completionTopYukawa + addOneTopYukawa + addTwoTopYukawa + addThreeTopYukawa)

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling.

  These trees can be found with e.g.
  `#eval nonPhenoConstrainedChargesExt nextToNearestNeighbor`. -/
def nonPhenoConstrainedCharges : (I : CodimensionOneConfig) → Tree
  | same => root {trunk (some (-1)) {branch (some 0) {twig {-3} {leaf {-1, 0}}},
      branch (some 3) {twig {-3} {leaf {-1, 0}}},
      branch (some (-3)) {twig {-2} {leaf {-2, 1}}},
      branch (some 1) {twig {-2} {leaf {-2, 1}}},
      branch (some 2) {twig {-2} {leaf {-2, 1}}}},
    trunk (some 1) {branch (some (-3)) {twig {3} {leaf {0, 1}}},
      branch (some 0) {twig {3} {leaf {0, 1}}},
      branch (some (-2)) {twig {2} {leaf {-1, 2}}},
      branch (some (-1)) {twig {2} {leaf {-1, 2}}},
      branch (some 3) {twig {2} {leaf {-1, 2}}}},
    trunk (some 0) {branch (some (-3)) {twig {3} {leaf {-2, 2}}},
      branch (some 3) {twig {-3} {leaf {-2, 2}}},
      branch (some (-2)) {twig {1} {leaf {-3, 3}},
      twig {2} {leaf {-3, 3}},
      twig {-1} {leaf {-3, 3}, leaf {-2, -3, 3}},
      twig {-1, 1} {leaf {-3, 3}},
      twig {-1, 2} {leaf {-3, 3}}},
      branch (some (-1)) {twig {-3} {leaf {-2, 2}, leaf {-3, -2, 2}},
      twig {-3, 3} {leaf {-2, 2}},
      twig {3} {leaf {-2, 2}, leaf {3, -2, 2}},
      twig {1} {leaf {-3, 3}, leaf {2, -3, 3}},
      twig {2} {leaf {-3, 3}, leaf {2, -3, 3}}},
      branch (some 1) {twig {-3} {leaf {-2, 2}, leaf {-3, -2, 2}},
      twig {-3, 3} {leaf {-2, 2}},
      twig {3} {leaf {-2, 2}, leaf {3, -2, 2}},
      twig {-2} {leaf {-3, 3}, leaf {-2, -3, 3}},
      twig {-1} {leaf {-3, 3}, leaf {-2, -3, 3}}},
      branch (some 2) {twig {-2} {leaf {-3, 3}},
      twig {-1} {leaf {-3, 3}},
      twig {-2, 1} {leaf {-3, 3}},
      twig {-1, 1} {leaf {-3, 3}},
      twig {1} {leaf {-3, 3}, leaf {2, -3, 3}}}},
    trunk (some (-3)) {branch (some (-2)) {twig {1} {leaf {-3, 0}},
      twig {0} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}}},
      branch (some (-1)) {twig {-2} {leaf {-3, 0}},
      twig {0} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}}},
      branch (some 0) {twig {-2} {leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {-2, -1} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}, leaf {-2, -3, 0}},
      twig {-2, 1} {leaf {-3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}},
      twig {-1, 2} {leaf {-3, 0}}},
      branch (some 3) {twig {-1} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {0} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {2} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {-1, 0} {leaf {-2, -1}, leaf {-3, -2, -1}}},
      branch (some 1) {twig {-2} {leaf {-3, 0}},
      twig {0} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {-2, -1} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}, leaf {-2, -3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}},
      twig {-1, 2} {leaf {-3, 0}},
      twig {0, -1} {leaf {-2, -1}, leaf {-3, -2, -1}}},
      branch (some 2) {twig {-2} {leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {0} {leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {-2, -1} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}, leaf {-3, -2, -1}, leaf {-2, -3, 0}},
      twig {-2, 1} {leaf {-3, 0}},
      twig {0, -1} {leaf {-2, -1}, leaf {-3, -2, -1}}}},
    trunk (some 3) {branch (some 0) {twig {-1} {leaf {0, 3}},
      twig {2} {leaf {0, 3}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}},
      twig {-2, 1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}, leaf {2, 0, 3}},
      twig {-1, 2} {leaf {0, 3}},
      twig {1, 2} {leaf {0, 3}}},
      branch (some 1) {twig {2} {leaf {0, 3}}, twig {0} {leaf {1, 2}, leaf {3, 1, 2}},
        twig {-2} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}}},
      branch (some 2) {twig {-1} {leaf {0, 3}}, twig {0} {leaf {1, 2}, leaf {3, 1, 2}},
        twig {-2} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}}},
      branch (some (-3)) {twig {-2} {leaf {1, 2}, leaf {3, 1, 2}},
      twig {0} {leaf {1, 2}, leaf {3, 1, 2}},
      twig {1} {leaf {1, 2}, leaf {3, 1, 2}},
      twig {0, 1} {leaf {1, 2}, leaf {3, 1, 2}}},
      branch (some (-2)) {twig {-1} {leaf {0, 3}},
      twig {2} {leaf {0, 3}},
      twig {0} {leaf {1, 2}, leaf {3, 1, 2}},
      twig {1} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}, leaf {2, 0, 3}},
      twig {-1, 2} {leaf {0, 3}},
      twig {1, 2} {leaf {0, 3}},
      twig {0, 1} {leaf {1, 2}, leaf {3, 1, 2}}},
      branch (some (-1)) {twig {2} {leaf {0, 3}},
      twig {0} {leaf {1, 2}, leaf {3, 1, 2}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}},
      twig {-2, 1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}, leaf {3, 1, 2}, leaf {2, 0, 3}},
      twig {1, 2} {leaf {0, 3}},
      twig {0, 1} {leaf {1, 2}, leaf {3, 1, 2}}}},
    trunk (some (-2)) {branch (some 3) {twig {-3} {leaf {-2, 0}},
      twig {0} {leaf {-3, 1}},
      twig {-3, -1} {leaf {-2, 0}},
      twig {-1} {leaf {-2, 0}, leaf {-3, 1}, leaf {-3, -2, 0}}},
      branch (some (-1)) {twig {3} {leaf {-2, 0}, leaf {-3, 1}},
      twig {1} {leaf {-1}, leaf {-3, -1}},
      twig {1, 2} {leaf {-1}},
      twig {-3} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}, leaf {0, -1}},
      twig {2} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}, leaf {-3, -2, -1}},
      twig {1, 2, -3} {leaf {-1}},
      twig {1, -3} {leaf {-1}, leaf {-3, -1}},
      twig {2, -3} {leaf {-1}, leaf {-3, -1}}},
      branch (some 1) {twig {3} {leaf {-2, 0}},
      twig {-3} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}, leaf {0, -1}, leaf {3, -1}},
      twig {0} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1}, leaf {-3, -2, -1}},
      twig {0, 2} {leaf {-1}, leaf {-3, -1}},
      twig {2} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}, leaf {-3, -2, -1}},
      twig {0, -3} {leaf {-1}, leaf {-3, -1}},
      twig {2, -3} {leaf {-1}, leaf {-3, -1}},
      twig {-3, -1} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}},
      twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, 0},
        leaf {-3, -2, -1}},
      twig {0, 2, -3} {leaf {-1}, leaf {-3, -1}},
      twig {-3, 0, -1} {leaf {-1}, leaf {-3, -1}},
      twig {0, -1} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, -1}}},
      branch (some (-3)) {twig {3} {leaf {-2, 0}, leaf {-3, 1}},
      twig {1} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {1, 2} {leaf {-1}},
      twig {-1, 3} {leaf {-3, 1}},
      twig {2} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {2, -1}, leaf {-3, -2, -1}},
      twig {1, -1} {leaf {-1}, leaf {-3, -1}},
      twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}, leaf {-3, -1}, leaf {-2, -1},
        leaf {-3, -2, 0}, leaf {-3, -2, -1}},
      twig {2, 0} {leaf {-1}, leaf {-3, -1}},
      twig {0} {leaf {-1}, leaf {-3, 1}, leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1},
        leaf {-3, -2, -1}},
      twig {-1, 0} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, -1}}},
      branch (some 0) {twig {3} {leaf {-2, 0}, leaf {-3, 1}},
      twig {1} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {-3} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}, leaf {0, -1}, leaf {3, -1}},
      twig {-1, 3} {leaf {-3, 1}},
      twig {1, -3} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {-3, -1} {leaf {-1}, leaf {-2, 0}, leaf {-3, -1}},
      twig {1, -1} {leaf {-1}, leaf {-3, -1}},
      twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}, leaf {-3, -1}, leaf {-2, -1},
        leaf {-3, -2, 0}, leaf {-3, -2, -1}},
      twig {-3, 1, -1} {leaf {-1}, leaf {-3, -1}}},
      branch (some 2) {twig {3} {leaf {-3, 1}},
      twig {-3} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {1} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {-1, 3} {leaf {-3, 1}},
      twig {-3, 1} {leaf {-1}, leaf {-3, -1}, leaf {3, -1}},
      twig {-3, -1} {leaf {-1}, leaf {-3, -1}},
      twig {1, -1} {leaf {-1}, leaf {-3, -1}},
      twig {-1} {leaf {-1}, leaf {-3, 1}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, -1}},
      twig {-3, 0} {leaf {-1}, leaf {-3, -1}},
      twig {0} {leaf {-1}, leaf {-3, 1}, leaf {-3, -1}, leaf {-2, -1}, leaf {3, -1},
        leaf {-3, -2, -1}},
      twig {-3, 1, -1} {leaf {-1}, leaf {-3, -1}},
      twig {-3, -1, 0} {leaf {-1}, leaf {-3, -1}},
      twig {-1, 0} {leaf {-1}, leaf {-3, -1}, leaf {-2, -1}, leaf {-3, -2, -1}}}},
    trunk (some 2) {branch (some (-3)) {twig {3} {leaf {0, 2}},
      twig {0} {leaf {-1, 3}},
      twig {3, 1} {leaf {0, 2}},
      twig {1} {leaf {0, 2}, leaf {-1, 3}, leaf {3, 0, 2}}},
      branch (some 1) {twig {-3} {leaf {0, 2}, leaf {-1, 3}},
      twig {-2, -1} {leaf {1}},
      twig {-1} {leaf {1}, leaf {3, 1}},
      twig {3} {leaf {1}, leaf {0, 2}, leaf {0, 1}, leaf {3, 1}},
      twig {-2} {leaf {1}, leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-2, -1, 3} {leaf {1}},
      twig {-2, 3} {leaf {1}, leaf {3, 1}},
      twig {-1, 3} {leaf {1}, leaf {3, 1}}},
      branch (some (-1)) {twig {-3} {leaf {0, 2}},
      twig {3} {leaf {1}, leaf {0, 2}, leaf {-3, 1}, leaf {0, 1}, leaf {3, 1}},
      twig {-2} {leaf {1}, leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-2, 0} {leaf {1}, leaf {3, 1}},
      twig {0} {leaf {1}, leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {1} {leaf {1}, leaf {0, 2}, leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2}, leaf {2, 3, 1}},
      twig {-2, 3} {leaf {1}, leaf {3, 1}},
      twig {0, 3} {leaf {1}, leaf {3, 1}},
      twig {1, 3} {leaf {1}, leaf {0, 2}, leaf {3, 1}},
      twig {0, 1} {leaf {1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-2, 0, 3} {leaf {1}, leaf {3, 1}},
      twig {0, 1, 3} {leaf {1}, leaf {3, 1}}},
      branch (some (-2)) {twig {-3} {leaf {-1, 3}},
      twig {-1} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {3} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {-3, 1} {leaf {-1, 3}},
      twig {-1, 3} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {3, 0} {leaf {1}, leaf {3, 1}},
      twig {0} {leaf {1}, leaf {-1, 3}, leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-1, 1} {leaf {1}, leaf {3, 1}},
      twig {3, 1} {leaf {1}, leaf {3, 1}},
      twig {1} {leaf {1}, leaf {-1, 3}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-1, 3, 1} {leaf {1}, leaf {3, 1}},
      twig {0, 3, 1} {leaf {1}, leaf {3, 1}},
      twig {0, 1} {leaf {1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}}},
      branch (some 0) {twig {-3} {leaf {0, 2}, leaf {-1, 3}},
      twig {-1} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {3} {leaf {1}, leaf {0, 2}, leaf {-3, 1}, leaf {0, 1}, leaf {3, 1}},
      twig {-3, 1} {leaf {-1, 3}},
      twig {-1, 3} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {-1, 1} {leaf {1}, leaf {3, 1}},
      twig {3, 1} {leaf {1}, leaf {0, 2}, leaf {3, 1}},
      twig {1} {leaf {1}, leaf {0, 2}, leaf {-1, 3}, leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2},
        leaf {2, 3, 1}},
      twig {-1, 3, 1} {leaf {1}, leaf {3, 1}}},
      branch (some 3) {twig {-3} {leaf {0, 2}, leaf {-1, 3}},
      twig {-2, -1} {leaf {1}},
      twig {-1} {leaf {1}, leaf {-3, 1}, leaf {3, 1}},
      twig {-3, 1} {leaf {-1, 3}},
      twig {-2} {leaf {1}, leaf {-2, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-2, 0} {leaf {1}, leaf {3, 1}},
      twig {0} {leaf {1}, leaf {-1, 3}, leaf {-3, 1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}},
      twig {-1, 1} {leaf {1}, leaf {3, 1}},
      twig {1} {leaf {1}, leaf {0, 2}, leaf {-1, 3}, leaf {2, 1}, leaf {3, 1}, leaf {3, 0, 2},
        leaf {2, 3, 1}},
      twig {0, 1} {leaf {1}, leaf {2, 1}, leaf {3, 1}, leaf {2, 3, 1}}}}}
  | nearestNeighbor => root {trunk (some 1) {branch (some (-14)) {twig {11} {leaf {-7, 8}}},
      branch (some (-4)) {twig {11} {leaf {-7, 8}}},
      branch (some (-9)) {twig {-4} {leaf {-12, 13}}},
      branch (some 6) {twig {-9} {leaf {-12, 13}}, twig {-4} {leaf {-12, 13}}}},
    trunk (some (-4)) {branch (some (-14)) {twig {-9} {leaf {-2}, leaf {-12, -2}},
        twig {11} {leaf {-2}, leaf {-12, -2}}},
      branch (some (-9)) {twig {11} {leaf {-2}, leaf {-12, -2}}},
      branch (some 1) {twig {-14} {leaf {-2}, leaf {13, -2}},
      twig {-14, -9} {leaf {-2}},
      twig {-9} {leaf {-2}, leaf {-12, -2}},
      twig {-14, 11} {leaf {-2}},
      twig {11} {leaf {-2}, leaf {-12, -2}}},
      branch (some 11) {twig {-14} {leaf {-2}, leaf {13, -2}}, twig {-14, -9} {leaf {-2}},
        twig {-9} {leaf {-2}, leaf {-12, -2}}}},
    trunk (some 11) {branch (some 1) {twig {-14} {leaf {-2, 13}}},
      branch (some 6) {twig {-14} {leaf {-2, 13}}},
      branch (some (-9)) {twig {1} {leaf {3, 8}, leaf {13, 3, 8}}},
      branch (some (-4)) {twig {-14} {leaf {-2, 13}}, twig {1} {leaf {3, 8}, leaf {13, 3, 8}}}},
    trunk (some 6) {branch (some (-9)) {twig {-4} {leaf {-7, 13}}, twig {11} {leaf {-7, 13}}},
      branch (some 1) {twig {-14} {leaf {3}, leaf {13, 3}}, twig {11} {leaf {3}, leaf {13, 3}}},
      branch (some (-14)) {twig {-9} {leaf {-7, 13}},
      twig {-4} {leaf {3}, leaf {-7, 13}, leaf {13, 3}},
      twig {1} {leaf {3}, leaf {13, 3}},
      twig {11} {leaf {3}, leaf {-7, 13}, leaf {13, 3}},
      twig {-9, 11} {leaf {-7, 13}},
      twig {-4, 11} {leaf {3}, leaf {13, 3}},
      twig {1, 11} {leaf {3}, leaf {13, 3}}},
      branch (some (-4)) {twig {-9} {leaf {-7, 13}},
      twig {11} {leaf {3}, leaf {-7, 13}, leaf {13, 3}},
      twig {-9, 11} {leaf {-7, 13}},
      twig {1} {leaf {3}, leaf {8, 3}, leaf {13, 3}, leaf {8, 13, 3}},
      twig {1, 11} {leaf {3}, leaf {13, 3}}},
      branch (some 11) {twig {-9} {leaf {-7, 13}},
      twig {-14} {leaf {3}, leaf {13, 3}},
      twig {-4} {leaf {3}, leaf {-7, 13}, leaf {13, 3}},
      twig {-14, 1} {leaf {3}},
      twig {-14, -4} {leaf {3}, leaf {13, 3}},
      twig {1} {leaf {3}, leaf {8, 3}, leaf {13, 3}, leaf {8, 13, 3}}}},
    trunk (some (-14)) {branch (some (-9)) {twig {6} {leaf {-7}},
      twig {1} {leaf {-7}, leaf {-12, -7}},
      twig {1, 11} {leaf {-7}},
      twig {6, 11} {leaf {-7}},
      twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}, leaf {13, -7}}},
      branch (some (-4)) {twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}},
      twig {1} {leaf {-7}, leaf {-12, -7}},
      twig {1, 11} {leaf {-7}},
      twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}, leaf {13, -7}},
      twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 1, 11} {leaf {-7}},
      twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}}},
      branch (some 1) {twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}},
      twig {-4} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 6} {leaf {-7}},
      twig {-4, 6} {leaf {-7}},
      twig {6, 11} {leaf {-7}},
      twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {8, -7}},
      twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
      twig {-9, -4, 6} {leaf {-7}},
      twig {-9, 6, 11} {leaf {-7}},
      twig {-9, 11} {leaf {-7}, leaf {-12, -7}}},
      branch (some 6) {twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}},
      twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
      twig {1} {leaf {-7}, leaf {-12, -7}},
      twig {1, 11} {leaf {-7}},
      twig {11} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}},
      twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
      twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 1, 11} {leaf {-7}},
      twig {-9, 11} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
      twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}},
      branch (some 11) {twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}, leaf {-12, -7}, leaf {13, -7}},
      twig {-4} {leaf {-7}, leaf {-12, -7}, leaf {13, -7}},
      twig {1} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 6} {leaf {-7}},
      twig {-4, 6} {leaf {-7}},
      twig {-9, -4} {leaf {-7}, leaf {-12, -7}},
      twig {-9, 1} {leaf {-7}, leaf {-12, -7}},
      twig {-4, 1} {leaf {-7}, leaf {-12, -7}},
      twig {-9, -4, 6} {leaf {-7}},
      twig {-9, -4, 1} {leaf {-7}, leaf {-12, -7}}}}}
  | nextToNearestNeighbor => root {trunk (some (-13)) {branch (some (-8))
        {twig {7} {leaf {-9, -4}}},
      branch (some 2) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
      branch (some 7) {twig {-3} {leaf {-9, -4}}},
      branch (some 12) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}}},
    trunk (some 7) {branch (some (-8)) {twig {-13} {leaf {-4, 11}}},
      branch (some 2) {twig {-13} {leaf {-4, 11}}},
      branch (some 12) {twig {-13} {leaf {-4, 11}}}},
    trunk (some (-8)) {branch (some 12) {twig {-13} {leaf {-9, 1}}},
      branch (some (-13)) {twig {12} {leaf {-9, 1}}, twig {-3} {leaf {-4}, leaf {-9, -4}},
        twig {7} {leaf {-4}, leaf {-9, -4}}},
      branch (some (-3)) {twig {12} {leaf {-9, 1}},
      twig {-13} {leaf {-4}, leaf {-9, 1}, leaf {1, -4}},
      twig {-13, 7} {leaf {-4}},
      twig {7} {leaf {-4}, leaf {-9, -4}}},
      branch (some 2) {twig {-13} {leaf {-4}, leaf {-9, 1}, leaf {1, -4}, leaf {11, -4}},
      twig {-13, -3} {leaf {-4}},
      twig {-3} {leaf {-4}, leaf {-9, -4}},
      twig {-13, 7} {leaf {-4}},
      twig {7} {leaf {-4}, leaf {-9, -4}}},
      branch (some 7) {twig {-13} {leaf {-4}, leaf {11, -4}}, twig {-13, -3} {leaf {-4}},
        twig {-3} {leaf {-4}, leaf {-9, -4}}}},
    trunk (some 2) {branch (some (-3)) {twig {12} {leaf {-9, 11}}},
      branch (some (-13)) {twig {-8} {leaf {1}},
      twig {7} {leaf {1}},
      twig {-8, 12} {leaf {1}},
      twig {7, 12} {leaf {1}},
      twig {12} {leaf {1}, leaf {-9, 1}}},
      branch (some (-8)) {twig {-3} {leaf {-9, 11}},
      twig {-13} {leaf {1}, leaf {-9, 1}},
      twig {-13, 7} {leaf {1}},
      twig {7} {leaf {1}, leaf {11, 1}},
      twig {7, 12} {leaf {1}},
      twig {12} {leaf {1}, leaf {-9, 11}, leaf {-9, 1}}},
      branch (some 7) {twig {-13} {leaf {1}}, twig {-13, -8} {leaf {1}},
        twig {-8} {leaf {1}, leaf {11, 1}}},
      branch (some 12) {twig {-3} {leaf {-9, 11}},
      twig {-13} {leaf {1}, leaf {-9, 1}},
      twig {-13, -8} {leaf {1}},
      twig {-8} {leaf {1}, leaf {-9, 11}, leaf {11, 1}},
      twig {-13, 7} {leaf {1}},
      twig {7} {leaf {1}, leaf {11, 1}}}},
    trunk (some 12) {branch (some 2) {twig {-13} {leaf {6}, leaf {11, 6}},
        twig {7} {leaf {6}, leaf {1, 11}, leaf {11, 6}}},
      branch (some (-13)) {twig {-8} {leaf {6}, leaf {11, 6}},
      twig {2} {leaf {6}, leaf {11, 6}},
      twig {7} {leaf {6}, leaf {11, 6}},
      twig {-8, 7} {leaf {6}, leaf {11, 6}},
      twig {2, 7} {leaf {6}, leaf {11, 6}}},
      branch (some (-8)) {twig {-13} {leaf {6}, leaf {11, 6}},
      twig {-13, 2} {leaf {6}},
      twig {2} {leaf {6}, leaf {11, 6}},
      twig {7} {leaf {6}, leaf {1, 11}, leaf {11, 6}},
      twig {2, 7} {leaf {6}, leaf {11, 6}}},
      branch (some (-3)) {twig {-13} {leaf {6}, leaf {11, 6}},
      twig {-8} {leaf {6}, leaf {1, 11}, leaf {11, 6}},
      twig {-13, 2} {leaf {6}},
      twig {2} {leaf {6}, leaf {11, 6}},
      twig {7} {leaf {6}, leaf {1, 11}, leaf {11, 6}},
      twig {-13, -8} {leaf {6}, leaf {11, 6}},
      twig {-8, 7} {leaf {6}, leaf {11, 6}},
      twig {2, 7} {leaf {6}, leaf {11, 6}}},
      branch (some 7) {twig {-13} {leaf {6}, leaf {11, 6}},
      twig {-8} {leaf {6}, leaf {1, 11}, leaf {11, 6}},
      twig {-13, -8} {leaf {6}, leaf {11, 6}}}}}

/-!

## Properties of the charges in nonPhenoConstrainedCharges

-/

/-!

### Cardinalities

-/

lemma nonPhenoConstrainedCharges_same_card : (nonPhenoConstrainedCharges same).card = 480 := by
  rfl

lemma nonPhenoConstrainedCharges_nearestNeighbor_card :
    (nonPhenoConstrainedCharges nearestNeighbor).card = 169 := by
  rfl

lemma nonPhenoConstrainedCharges_nextToNearestNeighbor_card :
    (nonPhenoConstrainedCharges nextToNearestNeighbor).card = 117 := by
  rfl

/-!

### Each charge is complete

-/

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, x.IsComplete := by
  decide

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, x.IsComplete := by
  decide

set_option maxRecDepth 2000 in
lemma isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, x.IsComplete := by
  decide

lemma isComplete_of_mem_nonPhenoConstrainedCharge (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, x.IsComplete :=
  match I with
  | same =>  isComplete_of_mem_nonPhenoConstrainedCharge_same
  | nearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nearestNeighbor
  | nextToNearestNeighbor => isComplete_of_mem_nonPhenoConstrainedCharge_nextToNearestNeighbor

/-!

### Each change is not pheno-constrained

-/

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset, ¬ x.IsPhenoConstrained := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset, ¬ x.IsPhenoConstrained := by
  decide

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset, ¬ x.IsPhenoConstrained := by
  decide

lemma not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset, ¬ x.IsPhenoConstrained :=
  match I with
  | same => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor => not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

/-!

### Each change has a top Yukawa coupling

-/

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_same :
    ∀ x ∈ (nonPhenoConstrainedCharges same).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nearestNeighbor).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

set_option maxRecDepth 2000 in
lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor :
    ∀ x ∈ (nonPhenoConstrainedCharges nextToNearestNeighbor).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) := by
  decide

lemma isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (nonPhenoConstrainedCharges I).toMultiset,
      IsPresent topYukawa (toChargeProfile topYukawa x) :=
  match I with
  | same => isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_same
  | nearestNeighbor => isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nearestNeighbor
  | nextToNearestNeighbor => isPresent_topYukawa_of_mem_nonPhenoConstrainedCharges_nextToNearestNeighbor

/-!

### phenoInsertQ10 on nonPhenoConstrainedCharges is empty

This result is used to help show completeness.

-/

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_same : ∀ q10 ∈ same.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges same) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nearestNeighbor : ∀ q10 ∈ nearestNeighbor.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges nearestNeighbor) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nextToNearestNeighbor :
    ∀ q10 ∈ nextToNearestNeighbor.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges nextToNearestNeighbor) q10).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ10_card_zero (I : CodimensionOneConfig) :
    ∀ q10 ∈ I.allowedTenCharges,
    (phenoInsertQ10 (nonPhenoConstrainedCharges I) q10).card = 0 :=
  match I with
  | same => nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_same
  | nearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nearestNeighbor
  | nextToNearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ10_card_zero_nextToNearestNeighbor

/-!

### phenoInsertQ5 on nonPhenoConstrainedCharges is empty

This result is used to help show completeness.

-/

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same : ∀ q5 ∈ same.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges same) (q5)).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nearestNeighbor :
    ∀ q5 ∈ nearestNeighbor.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges nearestNeighbor) (q5)).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nextToNearestNeighbor :
    ∀ q5 ∈ nextToNearestNeighbor.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges nextToNearestNeighbor) (q5)).card = 0 := by
  decide

lemma nonPhenoConstrainedCharges_phenoInsertQ5_card_zero (I : CodimensionOneConfig) :
    ∀ q5 ∈ I.allowedBarFiveCharges,
    (phenoInsertQ5 (nonPhenoConstrainedCharges I) (q5)).card = 0 :=
  match I with
  | same => nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_same
  | nearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nearestNeighbor
  | nextToNearestNeighbor => nonPhenoConstrainedCharges_phenoInsertQ5_card_zero_nextToNearestNeighbor

end Charges

end SU5U1

end FTheory
