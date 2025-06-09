/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.IsViable.Elems
/-!

# Cases of `Quanta` in `viableElems`

In `arXiv:1507.05961`, there are a number of specific cases of `Quanta` which are
viable given. These are named based on convention, we give some of those cases in this
paper and prove that they are in `viableElems` for the appropriate `I : CodimensionOneConfig`.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Quanta
open PotentialTerm Charges

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.a in table 1 of arXiv:1507.05961. -/
def caseI14a : Quanta := (some 2, some (-2), {(-1, 1, 2), (1, 2, -2)}, {(-1, 3, 0)})

lemma caseI14a_mem_viableElems : caseI14a ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.b in table 1 of arXiv:1507.05961. -/
def caseI14b : Quanta := (some 1, some (-2), {(0, 3, -3), (-1, 0, 3)}, {(-1, 3, 0)})

lemma caseI14b_mem_viableElems : caseI14b ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def caseI14c : Quanta := (some 6, some (-14), {(1, 2, -2), (-9, 1, 2)}, {(-7, 3, 0)})

lemma caseI14c_mem_viableElems : caseI14c ∈ viableElems .nearestNeighbor := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def caseI14c' : Quanta := (some 6, some (-14), {(1, 3, -2), (-9, 0, 2)}, {(-7, 3, 0)})

lemma caseI14c'_mem_viableElems : caseI14c' ∈ viableElems .nearestNeighbor := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.d in table 1 of arXiv:1507.05961. -/
def caseI14d : Quanta := (some (-3), some 0, {(-2, 3, -3), (-1, 0, 3)}, {(0, 3, 0)})

lemma caseI14d_mem_viableElems : caseI14d ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.e in table 1 of arXiv:1507.05961. -/
def caseI14e : Quanta := (some 1, some (-14), {(-9, 0, 3), (-4, 3, -3)}, {(-7, 3, 0)})

lemma caseI14e_mem_viableElems : caseI14e ∈ viableElems .nearestNeighbor := by
  decide

/-- A case of `Quanta` with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.f in table 1 of arXiv:1507.05961. -/
def caseI14f : Quanta := (some (-3), some 12, {(2, 3, -3), (7, 0, 3)}, {(6, 3, 0)})

lemma caseI14f_mem_viableElems : caseI14f ∈ viableElems .nextToNearestNeighbor := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the two versions of I.2.4.a in table 8 of arXiv:1507.05961. -/
def caseI24a : Quanta := (some 2, some (-2), {(-3, 0, 3), (-1, 3, -3)}, {(-3, 1, -1), (-1, 2, 1)})

lemma caseI24a_mem_viableElems : caseI24a ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the two versions of the I.2.4.a in table 8 of arXiv:1507.05961. -/
def caseI24a' : Quanta := (some 2, some (-2), {(-3, 0, 3), (-1, 3, -3)}, {(-3, 2, -1), (-1, 1, 1)})

lemma caseI24a'_mem_viableElems : caseI24a' ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b : Quanta := (some 2, some (-2), {(-1, 0, 2), (1, 3, -2)}, {(-3, 1, 0), (-1, 2, 0)})

lemma caseI24b_mem_viableElems : caseI24b ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b' : Quanta := (some 2, some (-2), {(-1, 1, 2), (1, 2, -2)}, {(-3, 1, 0), (-1, 2, 0)})

lemma caseI24b'_mem_viableElems : caseI24b' ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b'' : Quanta := (some 2, some (-2), {(-1, 0, 2), (1, 3, -2)}, {(-3, 2, 0), (-1, 1, 0)})

lemma caseI24b''_mem_viableElems : caseI24b'' ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b''' : Quanta := (some 2, some (-2), {(-1, 1, 2), (1, 2, -2)}, {(-3, 2, 0), (-1, 1, 0)})

lemma caseI24b'''_mem_viableElems : caseI24b''' ∈ viableElems .same := by
  decide

/-- A case of `Quanta` with three 10d representations and 4 5-bar representations.
  This corresponds to example I.3.4.a of arXiv:1507.05961 (Eq. A12). -/
def caseI34a : Quanta := (some 1, some (-2), {(-1, 0, 3), (0, 3, -3)},
  {(-3, 1, 0), (-2, 1, 0), (-1, 1, 0)})

lemma caseI34a_mem_viableElems : caseI34a ∈ viableElems .same := by
  decide

end Quanta
end SU5U1

end FTheory
