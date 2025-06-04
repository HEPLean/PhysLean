/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Basic
/-!

# Elements of the non pheno-constrained charges

For each `CodimensionOneConfig`, `I`, we give trees of charges which are not pheno-constrained,
and prove properties about them.

These trees are complete in the sense that they contain all the non pheno-constrained, complete,
charges which are in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`.
We use the `Tree` type defined in `FTheory.SU5U1.Charges.Tree.Basic` here for efficiency.

We break the properties of these trees into smaller modules, to aid in
speed of building.

## Comment on proofs

Note a lot of proofs related to `nonPhenoConstrainedCharges` depend on `decide`.
These proofs like all proofs are still constrained by `maxHeartBeats`, which prevents
them from being too time consuming. See e.g.
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.E2.9C.94.20count_heartbeat.20and.20decide/near/521743784

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
  Yukawa coupling.

  These trees can be found with e.g.
  `#eval nonPhenoConstrainedChargesExt nextToNearestNeighbor`. -/
def nonPhenoConstrainedChargesNextToNearestNeighbor : Tree :=
 root {trunk (some 12) {branch (some (-8)) {twig {-13} {leaf {-9, 1}},
    twig {12} {leaf {-9, 1}}},
  branch (some 2) {twig {-3} {leaf {-9, 11}},
   twig {-13} {leaf {1}, leaf {-9, 1}},
   twig {-13, 7} {leaf {1}},
   twig {7} {leaf {1}, leaf {11, 1}},
   twig {7, 12} {leaf {1}},
   twig {12} {leaf {1}, leaf {-9, 11}, leaf {-9, 1}}}},
 trunk (some (-13)) {branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some (-8)) {twig {12} {leaf {-9, 1}},
   twig {-13} {leaf {-4}, leaf {-9, 1}, leaf {1, -4}, leaf {6, -4}, leaf {11, -4}},
   twig {-13, 7} {leaf {-4}},
   twig {7} {leaf {-4}, leaf {-9, -4}, leaf {6, -4}}},
  branch (some (-3)) {twig {-13} {leaf {-4, 1}, leaf {-9, 6}},
   twig {-8} {leaf {-9, 6}},
   twig {2} {leaf {-9, 6}},
   twig {-13, -8} {leaf {-9, 6}},
   twig {-13, 2} {leaf {-9, 6}}},
  branch (some 2) {twig {-8} {leaf {1}},
   twig {7} {leaf {1}, leaf {-4, 6}},
   twig {-13} {leaf {1}, leaf {-4, 6}, leaf {-9, 1}, leaf {-4, 1}},
   twig {-13, -8} {leaf {1}},
   twig {-13, 7} {leaf {1}},
   twig {-8, 12} {leaf {1}},
   twig {7, 12} {leaf {1}},
   twig {12} {leaf {1}, leaf {-9, 1}}},
  branch (some 12) {twig {-13} {leaf {6}, leaf {-9, 6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-8} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {2} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {7} {leaf {6}, leaf {-9, 6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-13, -8} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, 2} {leaf {6}, leaf {-9, 6}},
   twig {-8, 7} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {2, 7} {leaf {6}, leaf {11, 6}}}},
 trunk (some (-8)) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some (-3)) {twig {-13} {leaf {-4, 1}, leaf {-9, 6}},
   twig {-8} {leaf {-9, 6}},
   twig {7} {leaf {-9, 6}},
   twig {-13, -8} {leaf {-9, 6}},
   twig {-8, 7} {leaf {-9, 6}}},
  branch (some 2) {twig {-3} {leaf {-9, 11}},
   twig {-13} {leaf {1}, leaf {-9, 1}, leaf {-4, 1}},
   twig {-13, -8} {leaf {1}},
   twig {-8} {leaf {1}, leaf {-9, 11}, leaf {11, 1}},
   twig {-13, 7} {leaf {1}},
   twig {7} {leaf {1}, leaf {11, 1}}},
  branch (some 12) {twig {-13} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-8} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {11, 6}},
   twig {2} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {7} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, -8} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, 2} {leaf {6}, leaf {-9, 6}},
   twig {-8, 7} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {2, 7} {leaf {6}, leaf {11, 6}}}},
 trunk (some (-3)) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-8)) {twig {-3} {leaf {-4}, leaf {-9, -4}}, twig {7} {leaf {-4}, leaf {-9, -4},
    leaf {6, -4}}},
  branch (some 2) {twig {-13} {leaf {-4, 6}},
   twig {-8} {leaf {-9, 11}},
   twig {-3} {leaf {-9, 11}},
   twig {12} {leaf {-9, 11}},
   twig {-8, 12} {leaf {-9, 11}}},
  branch (some 12) {twig {-13} {leaf {6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-8} {leaf {6}, leaf {11, 6}},
   twig {-13, 2} {leaf {6}},
   twig {2} {leaf {6}, leaf {11, 6}},
   twig {7} {leaf {6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-13, -8} {leaf {6}, leaf {11, 6}},
   twig {-8, 7} {leaf {6}, leaf {11, 6}},
   twig {2, 7} {leaf {6}, leaf {11, 6}}}},
 trunk (some 2) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some (-8)) {twig {12} {leaf {-9, 1}},
   twig {-13} {leaf {-4}, leaf {-9, 1}, leaf {11, -4}},
   twig {-13, -3} {leaf {-4}},
   twig {-3} {leaf {-4}, leaf {-9, -4}},
   twig {-13, 7} {leaf {-4}},
   twig {7} {leaf {-4}, leaf {-9, -4}}},
  branch (some (-3)) {twig {-13} {leaf {-9, 6}}, twig {2} {leaf {-9, 6}}, twig {7} {leaf {-9, 6}},
    twig {-13, 2} {leaf {-9, 6}}},
  branch (some 12) {twig {-13} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-8} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {11, 6}},
   twig {2} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {7} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, -8} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, 2} {leaf {6}, leaf {-9, 6}},
   twig {-8, 7} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {2, 7} {leaf {6}, leaf {11, 6}}}},
 trunk (some 7) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-8)) {twig {-13} {leaf {-4}, leaf {6, -4}, leaf {11, -4}},
   twig {-13, -3} {leaf {-4}},
   twig {-3} {leaf {-4}, leaf {-9, -4}},
   twig {-13, 7} {leaf {-4}},
   twig {7} {leaf {-4}, leaf {-9, -4}, leaf {6, -4}}},
  branch (some (-3)) {twig {-8} {leaf {-9, 6}}, twig {2} {leaf {-9, 6}}, twig {7} {leaf {-9, 6}},
     twig {-8, 7} {leaf {-9, 6}}},
  branch (some 2) {twig {12} {leaf {1}},
   twig {-13} {leaf {1}, leaf {-4, 6}},
   twig {-13, -8} {leaf {1}},
   twig {-8} {leaf {1}, leaf {11, 1}},
   twig {-13, 7} {leaf {1}},
   twig {7} {leaf {1}, leaf {-4, 6}, leaf {11, 1}},
   twig {-8, 12} {leaf {1}},
   twig {7, 12} {leaf {1}}},
  branch (some 12) {twig {-13} {leaf {6}, leaf {-9, 6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-8} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {11, 6}},
   twig {2} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {7} {leaf {6}, leaf {1, 11}, leaf {-9, 6}, leaf {-4, 6}, leaf {11, 6}},
   twig {-13, -8} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {-13, 2} {leaf {6}, leaf {-9, 6}},
   twig {-8, 7} {leaf {6}, leaf {-9, 6}, leaf {11, 6}},
   twig {2, 7} {leaf {6}, leaf {11, 6}}}}}

end Charges

end SU5U1

end FTheory
