/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.IsViable.Basic
/-!

# Quanta elements which are viable

For the `CodimensionOneConfig`, `I`, we give `FourTree`s corresponding to `Quanta`
which are viable. This is done in `viableElems`.

These trees are complete in the sense that they contain all the viable `Quanta`, which we prove.

That is to say, there is only finite number of viable quantum numbers one can associate to
representations in a `SU(5) × U(1)` F-theory, and these trees contain all of them.

This is one of the results of, arXiv:1507.05961, except there the result is a
calculation, whilst here it is a formal proof.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Quanta
open SuperSymmetry.SU5
open PhysLean FourTree Leaf Twig Branch Trunk

/-- The `FourTree` of elements of `Quanta` for which the `IsViable` condition holds for a given
  `I : CodimensionOneConfig`. This is an excutable version used to generate `viableElems`,
  but not useful in proofs.
-/
def viableElemsExe (I : CodimensionOneConfig) :
    FourTree (Option ℤ) (Option ℤ) FiveQuanta TenQuanta :=
  let C : Multiset Charges := (Charges.nonPhenoConstrainedChargesExt I).toMultiset
  let F : Multiset (Option ℤ × Option ℤ × FiveQuanta × TenQuanta) :=
    C.bind fun c =>
      let X1 := (FiveQuanta.ofCharges I c.2.2.1.val).product (TenQuanta.ofCharges I c.2.2.2.val)
      X1.map fun x => (c.1, c.2.1, x.1, x.2)
  FourTree.fromMultiset (F.filter fun x => AnomalyCancellation x.1 x.2.1 x.2.2.1 x.2.2.2)


/-- The `FourTree` of elements of `Quanta` for which the `IsViable` condition holds for a given
  `I : CodimensionOneConfig`.

  Note, these results where calculated using e.g.
  `set_option pp.deepTerms true`
  `#eval (viableElemsExe .nextToNearestNeighbor)`
-/
def viableElems : (I : CodimensionOneConfig) →
    FourTree (Option ℤ) (Option ℤ) FiveQuanta TenQuanta
  | .same => root {trunk (some (-3)) {branch (some 0) {twig {(-2, 3, -3), (-1, 0, 3)}
      {leaf {(0, 3, 0)}, leaf {(-3, 1, 0), (0, 2, 0)}, leaf {(-3, 2, 0), (0, 1, 0)}}},
    branch (some 1) {twig {(-2, 2, -2), (0, 1, 2)}
      {leaf {(-2, 1, 0), (3, 2, 0)}, leaf {(-2, 2, 0), (3, 1, 0)}},
    twig {(-2, 3, -2), (0, 0, 2)} {leaf {(-2, 1, 0), (3, 2, 0)}, leaf {(-2, 2, 0), (3, 1, 0)}},
    twig {(-2, 2, -2), (0, 0, 2), (3, 1, 0)} {leaf {(-2, 1, 0), (3, 2, 0)},
      leaf {(-2, 2, 0), (3, 1, 0)}}}},
  trunk (some 2) {branch (some (-2)) {twig {(-3, 0, 3), (-1, 3, -3)}
      {leaf {(-3, 1, -1), (-1, 2, 1)}, leaf {(-3, 2, -1), (-1, 1, 1)}},
    twig {(-1, 1, 2), (1, 2, -2)} {leaf {(-1, 3, 0)}, leaf {(-3, 1, 0), (-1, 2, 0)},
      leaf {(-3, 2, 0), (-1, 1, 0)}},
    twig {(-1, 0, 2), (1, 3, -2)} {leaf {(-1, 3, 0)}, leaf {(-3, 1, 0), (-1, 2, 0)},
      leaf {(-3, 2, 0), (-1, 1, 0)}},
    twig {(-3, 1, 0), (-1, 0, 2), (1, 2, -2)} {leaf {(-1, 3, 0)}, leaf {(-3, 1, 0), (-1, 2, 0)},
      leaf {(-3, 2, 0), (-1, 1, 0)}}},
    branch (some (-1)) {twig {(0, 0, 3), (1, 3, -3)} {leaf {(-3, 1, 0), (2, 2, 0)},
      leaf {(-3, 2, 0), (2, 1, 0)}}},
    branch (some 0) {twig {(1, 1, 2), (3, 2, -2)} {leaf {(0, 1, -1), (2, 2, 1)},
      leaf {(0, 2, -1), (2, 1, 1)}},
    twig {(1, 0, 2), (3, 3, -2)} {leaf {(0, 1, -1), (2, 2, 1)}, leaf {(0, 2, -1), (2, 1, 1)}}},
    branch (some 1) {twig {(3, 3, 0)} {leaf {(0, 2, 1), (1, 1, -1)},
      leaf {(0, 1, 1), (1, 2, -1)}}}},
  trunk (some (-2)) {branch (some (-1)) {twig {(-3, 3, 0)} {leaf {(-1, 1, -1), (0, 2, 1)},
      leaf {(-1, 2, -1), (0, 1, 1)}}},
    branch (some 0) {twig {(-3, 2, -2), (-1, 1, 2)} {leaf {(-2, 2, 1), (0, 1, -1)},
      leaf {(-2, 1, 1), (0, 2, -1)}},
    twig {(-3, 3, -2), (-1, 0, 2)} {leaf {(-2, 2, 1), (0, 1, -1)}, leaf {(-2, 1, 1), (0, 2, -1)}}},
    branch (some 1) {twig {(-1, 3, -3), (0, 0, 3)} {leaf {(-2, 1, 0), (3, 2, 0)},
      leaf {(-2, 2, 0), (3, 1, 0)}}},
    branch (some 2) {twig {(-1, 2, -2), (1, 1, 2)} {leaf {(1, 3, 0)}, leaf {(1, 1, 0), (3, 2, 0)},
      leaf {(1, 2, 0), (3, 1, 0)}},
    twig {(-1, 3, -2), (1, 0, 2)} {leaf {(1, 3, 0)}, leaf {(1, 1, 0), (3, 2, 0)},
      leaf {(1, 2, 0), (3, 1, 0)}},
    twig {(1, 3, -3), (3, 0, 3)} {leaf {(1, 2, 1), (3, 1, -1)}, leaf {(1, 1, 1), (3, 2, -1)}},
    twig {(-1, 2, -2), (1, 0, 2), (3, 1, 0)} {leaf {(1, 3, 0)}, leaf {(1, 1, 0), (3, 2, 0)},
      leaf {(1, 2, 0), (3, 1, 0)}}}},
  trunk (some (-1)) {branch (some 0)
    {twig {(-3, 0, 1), (-2, 3, -3), (-1, 0, 2)} {leaf {(0, 3, 0)}}},
    branch (some 2) {twig {(0, 3, -3), (1, 0, 3)} {leaf {(1, 3, 0)}, leaf {(1, 1, 0), (2, 2, 0)},
      leaf {(1, 2, 0), (2, 1, 0)}, leaf {(1, 1, 0), (3, 2, 0)}, leaf {(1, 2, 0), (3, 1, 0)},
      leaf {(1, 1, 0), (2, 1, 0), (3, 1, 0)}}}},
  trunk (some 1) {branch (some (-2)) {twig {(-1, 0, 3), (0, 3, -3)} {leaf {(-1, 3, 0)},
      leaf {(-3, 1, 0), (-1, 2, 0)}, leaf {(-3, 2, 0), (-1, 1, 0)}, leaf {(-2, 1, 0), (-1, 2, 0)},
      leaf {(-2, 2, 0), (-1, 1, 0)}, leaf {(-3, 1, 0), (-2, 1, 0), (-1, 1, 0)}}},
    branch (some 0) {twig {(1, 0, 2), (2, 3, -3), (3, 0, 1)} {leaf {(0, 3, 0)}}}},
  trunk (some 3) {branch (some 0) {twig {(1, 0, 3), (2, 3, -3)} {leaf {(0, 3, 0)},
      leaf {(0, 1, 0), (3, 2, 0)}, leaf {(0, 2, 0), (3, 1, 0)}}},
    branch (some (-1)) {twig {(0, 1, 2), (2, 2, -2)} {leaf {(-3, 1, 0), (2, 2, 0)},
      leaf {(-3, 2, 0), (2, 1, 0)}},
    twig {(0, 0, 2), (2, 3, -2)} {leaf {(-3, 1, 0), (2, 2, 0)}, leaf {(-3, 2, 0), (2, 1, 0)}},
    twig {(-3, 1, 0), (0, 0, 2), (2, 2, -2)} {leaf {(-3, 1, 0), (2, 2, 0)},
      leaf {(-3, 2, 0), (2, 1, 0)}}}}}
  | .nearestNeighbor => root {trunk (some (-9)) {branch (some (-14))
    {twig {(-9, 0, 2), (-4, 3, -3), (1, 0, 1)} {leaf {(-7, 3, 0)},
      leaf {(-12, 1, 0), (-7, 2, 0)}, leaf {(-12, 2, 0), (-7, 1, 0)}}}},
  trunk (some 1) {branch (some (-14)) {twig {(-9, 0, 3), (-4, 3, -3)} {leaf {(-7, 3, 0)},
    leaf {(-12, 1, 0), (-7, 2, 0)}, leaf {(-12, 2, 0), (-7, 1, 0)}}}},
  trunk (some 6) {branch (some (-14)) {twig {(-9, 1, 2), (1, 2, -2)} {leaf {(-7, 3, 0)},
    leaf {(-12, 1, 0), (-7, 2, 0)}, leaf {(-12, 2, 0), (-7, 1, 0)}},
    twig {(-9, 0, 2), (1, 3, -2)} {leaf {(-7, 3, 0)}, leaf {(-12, 1, 0), (-7, 2, 0)},
    leaf {(-12, 2, 0), (-7, 1, 0)}},
    twig {(-9, 0, 2), (1, 2, -2), (11, 1, 0)} {leaf {(-7, 3, 0)}},
    twig {(-9, 0, 2), (-4, 1, 0), (1, 2, -2)} {leaf {(-7, 3, 0)},
    leaf {(-12, 1, 0), (-7, 2, 0)}, leaf {(-12, 2, 0), (-7, 1, 0)}}}}}
  | .nextToNearestNeighbor =>root {trunk (some (-3)) {branch (some 12) {
      twig {(2, 3, -3), (7, 0, 3)} {leaf {(6, 3, 0)}, leaf {(6, 1, 0), (11, 2, 0)},
      leaf {(6, 2, 0), (11, 1, 0)}}}}}

/-- Every element in `viableElems` `IsViable`. -/
lemma isViable_of_mem_viableElems (I : CodimensionOneConfig) (x : Quanta)
    (hx : x ∈ viableElems I) : IsViable I x := by
  rw [mem_iff_mem_toMultiset] at hx
  revert x I
  decide

lemma viableElems_nodups (I : CodimensionOneConfig) : (viableElems I).toMultiset.Nodup := by
  revert I
  decide

lemma viableElems_same_card : (viableElems .same).card = 70 := by
  rfl

lemma viableElems_nearestNeighbor_card : (viableElems .nearestNeighbor).card = 16 := by
  rfl

lemma viableElems_nextToNearestNeighbor_card : (viableElems .nextToNearestNeighbor).card = 3 := by
  rfl

end Quanta
end SU5U1

end FTheory
