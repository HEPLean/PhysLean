/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Same
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.NearestNeighbor
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.NextToNearestNeighbor
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimallyAllowsTerm.OfFinset
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfRationalSection
/-!

# Elements of the non pheno-constrained charges

For each `CodimensionOneConfig`, `I`, we give trees of charges which are not pheno-constrained,
by combining the trees of `nonPhenoConstrainedChargesSame`,
`nonPhenoConstrainedChargesNearestNeighbor`, and `nonPhenoConstrainedChargesNextToNearestNeighbor`.

These trees are complete in the sense that they contain all the non pheno-constrained, complete,
charges which are in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`.
We use the `FourTree` type here for efficiency.

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

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig
open Tree
open PhysLean

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling. Unlike `nonPhenoConstrainedCharges`, these trees are calculated
  and therefore not good when using `decide` etc.
-/
def nonPhenoConstrainedChargesExt (I : CodimensionOneConfig) :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  let completionTopYukawa := (((minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
      I.allowedTenCharges topYukawa).bind
    (completions I.allowedBarFiveCharges I.allowedTenCharges)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addOneTopYukawa := (((completionTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addTwoTopYukawa := (((addOneTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  let addThreeTopYukawa := (((addTwoTopYukawa).bind (fun x =>
    (minimalSuperSet I.allowedBarFiveCharges I.allowedTenCharges x).val)).dedup.filter
    (fun x => ¬ IsPhenoConstrained x))
  FourTree.fromMultiset (completionTopYukawa + addOneTopYukawa +
    addTwoTopYukawa + addThreeTopYukawa)

/-- For a given `I : CodimensionOneConfig` the tree of charges containing all
  charges which are not phenomenlogically constrained, and which permit a top
  Yukawa coupling.

  These trees can be found with e.g.
  `#eval nonPhenoConstrainedChargesExt nextToNearestNeighbor`. -/
def nonPhenoConstrainedCharges : (I : CodimensionOneConfig) →
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)
  | same => nonPhenoConstrainedChargesSame
  | nearestNeighbor => nonPhenoConstrainedChargesNearestNeighbor
  | nextToNearestNeighbor => nonPhenoConstrainedChargesNextToNearestNeighbor

end Charges

end SU5U1

end FTheory
