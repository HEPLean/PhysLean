/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ReducedCharges
/-!

# The irreducible subsets of charges for a present term

For a given `CodimensionOneConfig`, `I`, and a `PotentialTerm`, `T`,
we define the finite set of `T.ChargeType` such that a
`T.reducedChargesIsPresent I` is present if it contains a subset in this list.

We define this finite set of irreducible subsets of charges both in an
simple form ` irreducibleSet' I T` which has the disavantage of being
slow to use `decide` with, and an explicit form `irreducibleSet' I T`
which is faster to use `decide` with.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace PotentialTerm

open CodimensionOneConfig

/-!

## Is irreducible

-/

/-- For a potential term `T`, an `x : T.ChargeType` is said to be irreducible if
  it allows the term `T`, and no other member of it's powerset allows `T`. -/
def IsIrreducible {T : PotentialTerm} (x : T.ChargeType) : Prop :=
  ∀ y ∈ powerset x, y = x ↔ IsPresent T y

instance {T : PotentialTerm} (x : T.ChargeType) : Decidable (T.IsIrreducible x) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ IsPresent T y))

lemma isPresent_of_isIrreducible {T : PotentialTerm} {x : T.ChargeType} (h : IsIrreducible x) :
    IsPresent T x := by
  simp [IsIrreducible] at h
  simpa using h x (self_mem_powerset x)

lemma isPresent_of_has_isIrreducible_subset {T : PotentialTerm} {x : T.ChargeType}
    (hx : ∃ y ∈ powerset x, IsIrreducible y) : IsPresent T x := by
  obtain ⟨y, hy⟩ := hx
  rw [← subset_of_iff_mem_powerset] at hy
  apply isPresent_of_subset T hy.1
  exact isPresent_of_isIrreducible hy.2

lemma isPresent_iff_has_isIrreducible_subset {T : PotentialTerm} {x : T.ChargeType} :
    IsPresent T x ↔ ∃ y ∈ powerset x, IsIrreducible y  := by
  by_cases hx : IsIrreducible x
  · simp [isPresent_of_isIrreducible hx]
    use x
    simp [hx]

  ·
    rw [IsIrreducible] at hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    by_cases hyx : y = x
    · subst hyx
      simp_all



/-!

## Cardinalities of the irreducible set

-/

def irreducibleSetCard (I : CodimensionOneConfig) (T : PotentialTerm) : ℕ :=
  match I, T with
  | same, μ => 7
  | same, K2 => 37
  | same, K1 => 20
  | same, W4 => 25
  | same, W3 => 16
  | same, W2 => 45
  | same, W1 => 45
  | same, Λ => 20
  | same, β => 7
  | same, topYukawa => 20
  | same, bottomYukawa => 37
  | nearestNeighbor, μ => 6
  | nearestNeighbor, K2 => 27
  | nearestNeighbor, K1 => 15
  | nearestNeighbor, W4 => 18
  | nearestNeighbor, W3 => 12
  | nearestNeighbor, W2 => 30
  | nearestNeighbor, W1 => 30
  | nearestNeighbor, Λ => 15
  | nearestNeighbor, β => 6
  | nearestNeighbor, topYukawa => 15
  | nearestNeighbor, bottomYukawa => 27
  | nextToNearestNeighbor, μ =>  6
  | nextToNearestNeighbor, K2 => 24
  | nextToNearestNeighbor, K1 => 12
  | nextToNearestNeighbor, W4 => 18
  | nextToNearestNeighbor, W3 => 12
  | nextToNearestNeighbor, W2 => 21
  | nextToNearestNeighbor, W1 => 21
  | nextToNearestNeighbor, Λ => 13
  | nextToNearestNeighbor, β => 6
  | nextToNearestNeighbor, topYukawa => 12
  | nextToNearestNeighbor, bottomYukawa => 24

/-!

## Explicit set of irreducible charges

-/

/-- OfNat instance on `Option ℤ`. -/
local instance (n : ℕ) : OfNat (Option ℤ) n where
  ofNat := some n

/-- Negation on `Option ℤ`. -/
local instance : Neg (Option ℤ) where
  neg x := match x with
    | none => none
    | some n => some (-n)

/-- For a `I = same` and a `T : PotentialTerm`, the irreducible
  elements in `T.ChargeType` which if one occurs as a subset of
  `x : T.ChargeType` then `x` permits the term `T`.
  They are irreducible in the sense that they can't be broken down into smaller subsets which
  are also lead to the term. -/
def irreducibleSetSame : (T : PotentialTerm) → Multiset T.ChargeType
  | μ => {(-3, -3), (-2, -2), (-1, -1), (0, 0), (1, 1), (2, 2), (3, 3)}
  | K2 => {(-3, 0, {3}), (-3, 1, {2}), (-3, 2, {1}), (-3, 3, {0}), (-2, -1, {3}),
    (-2, 0, {2}), (-2, 1, {1}), (-2, 2, {0}), (-2, 3, {-1}), (-1, -2, {3}), (-1, -1, {2}),
    (-1, 0, {1}), (-1, 1, {0}), (-1, 2, {-1}), (-1, 3, {-2}), (0, -3, {3}), (0, -2, {2}),
    (0, -1, {1}), (0, 0, {0}), (0, 1, {-1}), (0, 2, {-2}), (0, 3, {-3}), (1, -3, {2}),
    (1, -2, {1}), (1, -1, {0}), (1, 0, {-1}), (1, 1, {-2}), (1, 2, {-3}), (2, -3, {1}),
    (2, -2, {0}), (2, -1, {-1}), (2, 0, {-2}), (2, 1, {-3}), (3, -3, {0}), (3, -2, {-1}),
    (3, -1, {-2}), (3, 0, {-3})}
  | K1 => {({-3}, {-2, -1}), ({-3}, {-3, 0}), ({-2}, {-1}), ({-2}, {-2, 0}), ({-2}, {-3, 1}),
    ({-1}, {-1, 0}), ({-1}, {-2, 1}), ({-1}, {-3, 2}), ({0}, {0}), ({0}, {-1, 1}), ({0}, {-2, 2}),
    ({0}, {-3, 3}), ({1}, {0, 1}), ({1}, {-1, 2}), ({1}, {-2, 3}), ({2}, {1}), ({2}, {0, 2}),
    ({2}, {-1, 3}), ({3}, {1, 2}), ({3}, {0, 3})}
  | W4 => {(-3, -3, {-3}), (-3, -2, {-1}), (-3, -1, {1}), (-3, 0, {3}), (-2, -2, {-2}),
    (-2, -1, {0}), (-2, 0, {2}), (-1, -2, {-3}), (-1, -1, {-1}), (-1, 0, {1}), (-1, 1, {3}),
    (0, -1, {-2}), (0, 0, {0}), (0, 1, {2}), (1, -1, {-3}), (1, 0, {-1}), (1, 1, {1}), (1, 2, {3}),
    (2, 0, {-2}), (2, 1, {0}), (2, 2, {2}), (3, 0, {-3}), (3, 1, {-1}), (3, 2, {1}), (3, 3, {3})}
  | W3 => {(-3, {-3}), (-2, {-2}), (-2, {-3, -1}), (-1, {-1}), (-1, {-2, 0}), (-1, {-3, 1}),
    (0, {0}), (0, {-1, 1}), (0, {-2, 2}), (0, {-3, 3}), (1, {1}), (1, {0, 2}), (1, {-1, 3}),
    (2, {2}), (2, {1, 3}), (3, {3})}
  | W2 => {(-3, {1}), (-3, {-1, 2}), (-3, {-3, 3}), (-3, {0, 3}), (-3, {-2, 2, 3}),
    (-2, {0, 1}), (-2, {-2, 2}), (-2, {0, 2}), (-2, {-1, 1, 2}), (-2, {-1, 0, 3}),
    (-2, {-2, 1, 3}), (-2, {-3, 2, 3}), (-1, {-1, 1}), (-1, {0, 1}), (-1, {-3, 2}),
    (-1, {-1, 0, 2}), (-1, {-2, 1, 2}), (-1, {-1, 3}), (-1, {-2, 0, 3}), (-1, {-3, 1, 3}),
    (0, {0}), (0, {-2, 1}), (0, {-1, 2}), (0, {-3, 1, 2}), (0, {-2, -1, 3}), (1, {-1, 0}),
    (1, {-3, 1}), (1, {-1, 1}), (1, {-2, 0, 1}), (1, {-2, -1, 2}), (1, {-3, 0, 2}), (1, {-2, 3}),
    (1, {-3, -1, 3}), (2, {-2, 0}), (2, {-1, 0}), (2, {-2, -1, 1}), (2, {-3, 0, 1}), (2, {-2, 2}),
    (2, {-3, -1, 2}), (2, {-3, -2, 3}), (3, {-1}), (3, {-3, 0}), (3, {-2, 1}), (3, {-3, -2, 2}),
    (3, {-3, 3})}
  | W1 => {({-3}, {1}), ({-3}, {-1, 2}), ({-3}, {-3, 3}), ({-3}, {0, 3}), ({-3}, {-2, 2, 3}),
    ({-2}, {0, 1}), ({-2}, {-2, 2}), ({-2}, {0, 2}), ({-2}, {-1, 1, 2}), ({-2}, {-1, 0, 3}),
    ({-2}, {-2, 1, 3}), ({-2}, {-3, 2, 3}), ({-1}, {-1, 1}), ({-1}, {0, 1}), ({-1}, {-3, 2}),
    ({-1}, {-1, 0, 2}), ({-1}, {-2, 1, 2}), ({-1}, {-1, 3}), ({-1}, {-2, 0, 3}), ({-1}, {-3, 1, 3}),
    ({0}, {0}), ({0}, {-2, 1}), ({0}, {-1, 2}), ({0}, {-3, 1, 2}), ({0}, {-2, -1, 3}),
    ({1}, {-1, 0}), ({1}, {-3, 1}), ({1}, {-1, 1}), ({1}, {-2, 0, 1}), ({1}, {-2, -1, 2}),
    ({1}, {-3, 0, 2}), ({1}, {-2, 3}), ({1}, {-3, -1, 3}), ({2}, {-2, 0}), ({2}, {-1, 0}),
    ({2}, {-2, -1, 1}), ({2}, {-3, 0, 1}), ({2}, {-2, 2}), ({2}, {-3, -1, 2}), ({2}, {-3, -2, 3}),
    ({3}, {-1}), ({3}, {-3, 0}), ({3}, {-2, 1}), ({3}, {-3, -2, 2}), ({3}, {-3, 3})}
  | Λ => {({-1}, {2}), ({-2, -1}, {3}), ({0}, {0}), ({-3, 0}, {3}), ({-2, 0}, {2}),
    ({-1, 0}, {1}), ({1}, {-2}), ({-3, 1}, {2}), ({-2, 1}, {1}), ({-1, 1}, {0}), ({0, 1}, {-1}),
    ({-3, 2}, {1}), ({-2, 2}, {0}), ({-1, 2}, {-1}), ({0, 2}, {-2}), ({1, 2}, {-3}), ({-3, 3}, {0}),
    ({-2, 3}, {-1}), ({-1, 3}, {-2}), ({0, 3}, {-3})}
  | β => {(-3, {-3}), (-2, {-2}), (-1, {-1}), (0, {0}), (1, {1}), (2, {2}), (3, {3})}
  | topYukawa => {(-3, {-2, -1}), (-3, {-3, 0}), (-2, {-1}), (-2, {-2, 0}), (-2, {-3, 1}),
    (-1, {-1, 0}), (-1, {-2, 1}), (-1, {-3, 2}), (0, {0}), (0, {-1, 1}), (0, {-2, 2}), (0, {-3, 3}),
    (1, {0, 1}), (1, {-1, 2}), (1, {-2, 3}), (2, {1}), (2, {0, 2}), (2, {-1, 3}), (3, {1, 2}),
    (3, {0, 3})}
  | bottomYukawa => {(-3, {0}, {3}), (-3, {1}, {2}), (-3, {2}, {1}), (-3, {3}, {0}),
    (-2, {-1}, {3}), (-2, {0}, {2}), (-2, {1}, {1}), (-2, {2}, {0}), (-2, {3}, {-1}),
    (-1, {-2}, {3}), (-1, {-1}, {2}), (-1, {0}, {1}), (-1, {1}, {0}), (-1, {2}, {-1}),
    (-1, {3}, {-2}), (0, {-3}, {3}), (0, {-2}, {2}), (0, {-1}, {1}), (0, {0}, {0}), (0, {1}, {-1}),
    (0, {2}, {-2}), (0, {3}, {-3}), (1, {-3}, {2}), (1, {-2}, {1}), (1, {-1}, {0}), (1, {0}, {-1}),
    (1, {1}, {-2}), (1, {2}, {-3}), (2, {-3}, {1}), (2, {-2}, {0}), (2, {-1}, {-1}), (2, {0}, {-2}),
    (2, {1}, {-3}), (3, {-3}, {0}), (3, {-2}, {-1}), (3, {-1}, {-2}), (3, {0}, {-3})}

-- #eval (presentSubsetExe .nextToNearestNeighbor bottomYukawa)
/-- For a `I = nearestNeighbor` and a `T : PotentialTerm`, the irreducible
  elements in `T.ChargeType` which if one occurs as a subset of
  `x : T.ChargeType` then `x` permits the term `T`.
  They are irreducible in the sense that they can't be broken down into smaller subsets which
  are also lead to the term `T`. -/
def irreducibleSetNN : (T : PotentialTerm) → Multiset T.ChargeType
  | μ => {(-14, -14), (-9, -9), (-4, -4), (1, 1), (6, 6), (11, 11)}
  | K2 => {(-14, 1, {13}), (-14, 6, {8}), (-14, 11, {3}), (-9, -4, {13}),
    (-9, 1, {8}), (-9, 6, {3}), (-9, 11, {-2}), (-4, -9, {13}), (-4, -4, {8}), (-4, 1, {3}),
    (-4, 6, {-2}), (-4, 11, {-7}), (1, -14, {13}), (1, -9, {8}), (1, -4, {3}), (1, 1, {-2}),
    (1, 6, {-7}), (1, 11, {-12}), (6, -14, {8}), (6, -9, {3}), (6, -4, {-2}), (6, 1, {-7}),
    (6, 6, {-12}), (11, -14, {3}), (11, -9, {-2}), (11, -4, {-7}), (11, 1, {-12})}
  | K1 => {({-14}, {-7}), ({-14}, {-12, -2}), ({-9}, {-7, -2}), ({-9}, {-12, 3}),
    ({-4}, {-2}), ({-4}, {-7, 3}), ({-4}, {-12, 8}), ({1}, {-2, 3}), ({1}, {-7, 8}),
    ({1}, {-12, 13}), ({6}, {3}), ({6}, {-2, 8}), ({6}, {-7, 13}), ({11}, {3, 8}),
    ({11}, {-2, 13})}
  | W4 => {(-14, -14, {-14}), (-14, -9, {-4}), (-14, -4, {6}), (-9, -9, {-9}),
    (-9, -4, {1}), (-9, 1, {11}), (-4, -9, {-14}), (-4, -4, {-4}), (-4, 1, {6}), (1, -4, {-9}),
    (1, 1, {1}), (1, 6, {11}), (6, -4, {-14}), (6, 1, {-4}), (6, 6, {6}), (11, 1, {-9}),
    (11, 6, {1}), (11, 11, {11})}
  | W3 => {(-14, {-14}), (-9, {-9}), (-9, {-14, -4}), (-4, {-4}), (-4, {-9, 1}),
    (-4, {-14, 6}), (1, {1}), (1, {-4, 6}), (1, {-9, 11}), (6, {6}), (6, {1, 11}), (11, {11})}
  | W2 => {(-14, {-2, 8}), (-14, {3, 8}), (-14, {-12, 13}), (-14, {-2, 3, 13}),
    (-14, {-7, 8, 13}), (-9, {3}), (-9, {-7, 8}), (-9, {-2, 13}), (-9, {-12, 8, 13}), (-4, {-2, 3}),
    (-4, {-12, 8}), (-4, {-2, 8}), (-4, {-7, 3, 8}), (-4, {-7, -2, 13}), (-4, {-12, 3, 13}),
    (1, {-7, 3}), (1, {-2, 3}), (1, {-7, -2, 8}), (1, {-12, 3, 8}), (1, {-7, 13}),
    (1, {-12, -2, 13}), (6, {-2}), (6, {-12, 3}), (6, {-7, 8}), (6, {-12, -7, 13}), (11, {-7, -2}),
    (11, {-7, 3}), (11, {-12, -2, 3}), (11, {-12, -7, 8}), (11, {-12, 13})}
  | W1 => {({-14}, {-2, 8}), ({-14}, {3, 8}), ({-14}, {-12, 13}),
    ({-14}, {-2, 3, 13}), ({-14}, {-7, 8, 13}), ({-9}, {3}), ({-9}, {-7, 8}), ({-9}, {-2, 13}),
    ({-9}, {-12, 8, 13}), ({-4}, {-2, 3}), ({-4}, {-12, 8}), ({-4}, {-2, 8}), ({-4}, {-7, 3, 8}),
    ({-4}, {-7, -2, 13}), ({-4}, {-12, 3, 13}), ({1}, {-7, 3}), ({1}, {-2, 3}), ({1}, {-7, -2, 8}),
    ({1}, {-12, 3, 8}), ({1}, {-7, 13}), ({1}, {-12, -2, 13}), ({6}, {-2}), ({6}, {-12, 3}),
    ({6}, {-7, 8}), ({6}, {-12, -7, 13}), ({11}, {-7, -2}), ({11}, {-7, 3}), ({11}, {-12, -2, 3}),
    ({11}, {-12, -7, 8}), ({11}, {-12, 13})}
  | Λ => {({-4}, {8}), ({-9, -4}, {13}), ({1}, {-2}), ({-14, 1}, {13}),
    ({-9, 1}, {8}), ({-4, 1}, {3}), ({6}, {-12}), ({-14, 6}, {8}), ({-9, 6}, {3}), ({-4, 6}, {-2}),
    ({1, 6}, {-7}), ({-14, 11}, {3}), ({-9, 11}, {-2}), ({-4, 11}, {-7}), ({1, 11}, {-12})}
  | β => {(-14, {-14}), (-9, {-9}), (-4, {-4}), (1, {1}), (6, {6}), (11, {11})}
  | topYukawa => {(-14, {-7}), (-14, {-12, -2}), (-9, {-7, -2}), (-9, {-12, 3}),
    (-4, {-2}), (-4, {-7, 3}), (-4, {-12, 8}), (1, {-2, 3}), (1, {-7, 8}), (1, {-12, 13}), (6, {3}),
    (6, {-2, 8}), (6, {-7, 13}), (11, {3, 8}), (11, {-2, 13})}
  | bottomYukawa => {(-14, {1}, {13}), (-14, {6}, {8}), (-14, {11}, {3}),
    (-9, {-4}, {13}), (-9, {1}, {8}), (-9, {6}, {3}), (-9, {11}, {-2}), (-4, {-9}, {13}),
    (-4, {-4}, {8}), (-4, {1}, {3}), (-4, {6}, {-2}), (-4, {11}, {-7}), (1, {-14}, {13}),
    (1, {-9}, {8}), (1, {-4}, {3}), (1, {1}, {-2}), (1, {6}, {-7}), (1, {11}, {-12}),
    (6, {-14}, {8}), (6, {-9}, {3}), (6, {-4}, {-2}), (6, {1}, {-7}), (6, {6}, {-12}),
    (11, {-14}, {3}), (11, {-9}, {-2}), (11, {-4}, {-7}), (11, {1}, {-12})}

/-- For a `I = nextToNearestNeighbor` and a `T : PotentialTerm`, the irreducible
  elements in `T.ChargeType` which if one occurs as a subset of
  `x : T.ChargeType` then `x` permits the term `T`.
  They are irreducible in the sense that they can't be broken down into smaller subsets which
  are also lead to the term `T`. -/
def irreducibleSetNToNN : (T : PotentialTerm) → Multiset T.ChargeType
  | μ => {(-13, -13), (-8, -8), (-3, -3), (2, 2), (7, 7), (12, 12)}
  | K2 => {(-13, 2, {11}), (-13, 7, {6}), (-13, 12, {1}), (-8, -3, {11}),
    (-8, 2, {6}), (-8, 7, {1}), (-8, 12, {-4}), (-3, -8, {11}), (-3, -3, {6}), (-3, 2, {1}),
    (-3, 7, {-4}), (-3, 12, {-9}), (2, -13, {11}), (2, -8, {6}), (2, -3, {1}), (2, 2, {-4}),
    (2, 7, {-9}), (7, -13, {6}), (7, -8, {1}), (7, -3, {-4}), (7, 2, {-9}), (12, -13, {1}),
    (12, -8, {-4}), (12, -3, {-9})}
  | K1 => {({-13}, {-9, -4}), ({-8}, {-4}), ({-8}, {-9, 1}),
    ({-3}, {-4, 1}), ({-3}, {-9, 6}), ({2}, {1}), ({2}, {-4, 6}), ({2}, {-9, 11}), ({7}, {1, 6}),
    ({7}, {-4, 11}), ({12}, {6}), ({12}, {1, 11})}
  | W4 => {(-13, -13, {-13}), (-13, -8, {-3}), (-13, -3, {7}),
    (-8, -8, {-8}), (-8, -3, {2}), (-8, 2, {12}), (-3, -8, {-13}), (-3, -3, {-3}), (-3, 2, {7}),
    (2, -3, {-8}), (2, 2, {2}), (2, 7, {12}), (7, -3, {-13}), (7, 2, {-3}), (7, 7, {7}),
    (12, 2, {-8}), (12, 7, {2}), (12, 12, {12})}
  | W3 => {(-13, {-13}), (-8, {-8}), (-8, {-13, -3}), (-3, {-3}),
    (-3, {-8, 2}), (-3, {-13, 7}), (2, {2}), (2, {-3, 7}), (2, {-8, 12}), (7, {7}),
    (7, {2, 12}), (12, {12})}
  | W2 => {(-13, {1, 6}), (-13, {-9, 11}), (-13, {1, 11}),
    (-13, {-4, 6, 11}), (-8, {-4, 6}), (-8, {1, 6}), (-8, {-4, 1, 11}), (-8, {-9, 6, 11}),
    (-3, {1}), (-3, {-9, 6}), (-3, {-4, 11}), (2, {-4, 1}), (2, {-4, 6}), (2, {-9, 1, 6}),
    (2, {-9, -4, 11}), (7, {-9, 1}), (7, {-4, 1}), (7, {-9, -4, 6}), (7, {-9, 11}), (12, {-4}),
    (12, {-9, 6})}
  | W1 => {({-13}, {1, 6}), ({-13}, {-9, 11}), ({-13}, {1, 11}),
    ({-13}, {-4, 6, 11}), ({-8}, {-4, 6}), ({-8}, {1, 6}), ({-8}, {-4, 1, 11}), ({-8}, {-9, 6, 11}),
    ({-3}, {1}), ({-3}, {-9, 6}), ({-3}, {-4, 11}), ({2}, {-4, 1}), ({2}, {-4, 6}),
    ({2}, {-9, 1, 6}), ({2}, {-9, -4, 11}), ({7}, {-9, 1}), ({7}, {-4, 1}), ({7}, {-9, -4, 6}),
    ({7}, {-9, 11}), ({12}, {-4}), ({12}, {-9, 6})}
  | Λ => {({-3}, {6}), ({-8, -3}, {11}), ({2}, {-4}), ({-13, 2}, {11}),
    ({-8, 2}, {6}), ({-3, 2}, {1}), ({-13, 7}, {6}), ({-8, 7}, {1}), ({-3, 7}, {-4}),
    ({2, 7}, {-9}), ({-13, 12}, {1}), ({-8, 12}, {-4}), ({-3, 12}, {-9})}
  | β => {(-13, {-13}), (-8, {-8}), (-3, {-3}), (2, {2}), (7, {7}),
    (12, {12})}
  | topYukawa => {(-13, {-9, -4}), (-8, {-4}), (-8, {-9, 1}), (-3, {-4, 1}),
    (-3, {-9, 6}), (2, {1}), (2, {-4, 6}), (2, {-9, 11}), (7, {1, 6}), (7, {-4, 11}), (12, {6}),
    (12, {1, 11})}
  | bottomYukawa => {(-13, {2}, {11}), (-13, {7}, {6}), (-13, {12}, {1}),
    (-8, {-3}, {11}), (-8, {2}, {6}), (-8, {7}, {1}), (-8, {12}, {-4}), (-3, {-8}, {11}),
    (-3, {-3}, {6}), (-3, {2}, {1}), (-3, {7}, {-4}), (-3, {12}, {-9}), (2, {-13}, {11}),
    (2, {-8}, {6}), (2, {-3}, {1}), (2, {2}, {-4}), (2, {7}, {-9}), (7, {-13}, {6}), (7, {-8}, {1}),
    (7, {-3}, {-4}), (7, {2}, {-9}), (12, {-13}, {1}), (12, {-8}, {-4}), (12, {-3}, {-9})}

/-- For a `I : CodimensionOneConfig` and a `T : PotentialTerm`, the irreducible
  elements in `T.ChargeType` which if one occurs as a subset of
  `x : T.ChargeType` then `x` permits the term `T`.
  They are irreducible in the sense that they can't be broken down into smaller subsets which
  are also lead to the term `T`. -/
def irreducibleSet: (I : CodimensionOneConfig) → (T : PotentialTerm) → Multiset T.ChargeType
  | same, T => irreducibleSetSame T
  | nearestNeighbor, T => irreducibleSetNN T
  | nextToNearestNeighbor, T => irreducibleSetNToNN T


lemma irreducibleSet_countP_not_isIrreducible (I : CodimensionOneConfig) (T : PotentialTerm) :
    ((irreducibleSet I T).countP (fun x => ¬ IsIrreducible x)) = 0 := by
  revert T I
  decide

lemma isIrreducible_of_mem_irreducibleSet
    {I : CodimensionOneConfig} {T : PotentialTerm} (x : T.ChargeType)
    (h : x ∈ irreducibleSet I T) : IsIrreducible x := by
  have h1 := irreducibleSet_countP_not_isIrreducible I T
  simp only [Multiset.countP_eq_zero, Decidable.not_not] at h1
  exact h1 x h

lemma irreducibleSet_nodup (I : CodimensionOneConfig) (T : PotentialTerm) :
    (irreducibleSet I T).Nodup := by
  revert T I
  decide

lemma isPresent_of_mem_irreducibleSet
    {I : CodimensionOneConfig} {T : PotentialTerm} (x : T.ChargeType)
    (h : x ∈ irreducibleSet I T) : IsPresent T x :=  by
  apply isPresent_of_isIrreducible
  exact isIrreducible_of_mem_irreducibleSet x h

lemma irreducibleSet_card_eq (I : CodimensionOneConfig) (T : PotentialTerm) :
    (irreducibleSet I T).card = irreducibleSetCard I T := by
  revert T I
  decide

lemma irreducibleSet_subset_chargeSubsetFull (I : CodimensionOneConfig) (T : PotentialTerm) :
    irreducibleSet I T ⊆ (chargeSubsetFull I T).val := by
  refine Multiset.subset_iff.mpr ?_
  intro x hx
  fin_cases T
  all_goals
    simp only [chargeSubsetFull, Finset.product_eq_sprod, Finset.product_val]
    repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
    simp only [Finset.mem_val, Finset.mem_powerset]
    revert I x
    decide

/-!

## Auxillary results: Multisets from Finsets of given cardinality.

-/

def toMultisetsOne (s : Finset ℤ) : Multiset (Multiset ℤ) :=
  let X1 := (s.powersetCard 1).val.map fun X => X.val
  X1

@[simp]
lemma mem_toMultisetsOne_iff {s : Finset ℤ} (X : Multiset ℤ) :
    X ∈ toMultisetsOne s ↔ X.toFinset ⊆ s ∧ X.card = 1 := by
  simp [toMultisetsOne]
  intro h
  rw [Multiset.card_eq_one] at h
  obtain ⟨x, h1, h2⟩ := h
  simp

def toMultisetsTwo (s : Finset ℤ) : Multiset (Multiset ℤ) :=
  let X1 := (s.powersetCard 1).val.map (fun X => X.val.bind (fun x => Multiset.replicate 2 x))
  let X2 := (s.powersetCard 2).val.map fun X => X.val
  X1 + X2

@[simp]
lemma mem_toMultisetsTwo_iff {s : Finset ℤ} (X : Multiset ℤ) :
    X ∈ toMultisetsTwo s ↔ X.toFinset ⊆ s ∧ X.card = 2 := by
  simp [toMultisetsTwo]
  constructor
  · intro h
    rcases h with ⟨a, ⟨hasub, hacard⟩, hbind⟩ | ⟨h1, hcard⟩
    · rw [Finset.card_eq_one] at hacard
      obtain ⟨a, rfl⟩ := hacard
      simp at hbind
      subst hbind
      simpa using hasub
    · simp_all only [and_true]
      refine Finset.subset_def.mpr ?_
      simp only [Multiset.toFinset_val, Multiset.dedup_subset']
      exact Multiset.subset_of_le h1
  · intro ⟨hsub, hcard⟩
    simp_all
    rw [Multiset.card_eq_two] at hcard
    obtain ⟨a, b, rfl⟩ := hcard
    by_cases hab : a = b
    · subst hab
      left
      use {a}
      simpa using hsub
    · right
      refine (Multiset.le_iff_subset ?_).mpr ?_
      · simpa using hab
      · exact Multiset.dedup_subset'.mp hsub

def toMultisetsThree (s : Finset ℤ) : Multiset (Multiset ℤ) :=
  let X1 := (s.powersetCard 1).val.map (fun X => X.val.bind (fun x => Multiset.replicate 3 x))
  let X2 := s.val.bind (fun x => (s \ {x}).val.map (fun y => {x} + Multiset.replicate 2 y))
  let X3 := (s.powersetCard 3).val.map fun X => X.val
  X1 + X2 + X3

@[simp]
lemma mem_toMultisetsThree_iff {s : Finset ℤ} (X : Multiset ℤ) :
    X ∈ toMultisetsThree s ↔ X.toFinset ⊆ s ∧ X.card = 3 := by
  simp [toMultisetsThree]
  constructor
  · intro h
    rw [or_assoc] at h
    rcases h with ⟨a, ⟨hasub, hacard⟩, hbind⟩ | ⟨a, ha, ⟨b, hb, rfl⟩⟩ | ⟨h1, hcard⟩
    · rw [Finset.card_eq_one] at hacard
      obtain ⟨a, rfl⟩ := hacard
      simp at hbind
      subst hbind
      simpa using hasub
    · simp only [Multiset.toFinset_cons, Multiset.toFinset_singleton, Finset.mem_insert,
      Finset.mem_singleton, or_true, Finset.insert_eq_of_mem, Multiset.card_cons,
      Multiset.card_singleton, Nat.reduceAdd, and_true]
      refine Finset.insert_subset ha ?_
      rw [← @Multiset.mem_toFinset] at hb
      simp at hb
      simp only [Finset.singleton_subset_iff]
      exact Finset.mem_of_mem_erase hb
    · simp_all only [and_true]
      refine Finset.subset_def.mpr ?_
      simp only [Multiset.toFinset_val, Multiset.dedup_subset']
      exact Multiset.subset_of_le h1
  · intro ⟨hsub, hcard⟩
    simp_all
    rw [Multiset.card_eq_three] at hcard
    obtain ⟨a, b, c, rfl⟩ := hcard
    by_cases hab : a = b
    · subst hab
      left
      by_cases hac : a = c
      · subst hac
        left
        use {a}
        simpa using hsub
      · right
        simp [@Finset.insert_subset_iff] at hsub
        use c
        simp_all
        use a
        apply And.intro
        · refine (Multiset.mem_erase_of_ne hac).mpr ?_
          simp_all
        · simp
          rw [← Multiset.insert_eq_cons, Multiset.pair_comm c a]
          simp
    · rw [or_assoc]
      right
      by_cases hac : a = c
      · subst hac
        simp [@Finset.insert_subset_iff] at hsub
        left
        use b
        simp_all
        use a
        simp
        refine (Multiset.mem_erase_of_ne (by omega)).mpr ?_
        simp_all
      · by_cases hbc : b = c
        · subst hbc
          left
          simp [@Finset.insert_subset_iff] at hsub
          use a
          simp_all
          use b
          apply And.intro
          · refine (Multiset.mem_erase_of_ne (by omega)).mpr ?_
            simp_all
          exact Multiset.cons_swap b a {b}
        · right
          refine (Multiset.le_iff_subset ?_).mpr ?_
          · simp
            omega
          · exact Multiset.dedup_subset'.mp hsub

/-!

## irreducibleSet'

-/

def irreducibleSet' (I : CodimensionOneConfig) : (T : PotentialTerm) → Multiset T.ChargeType
  | μ =>
    let SqHd := I.allowedBarFiveCharges.val
    let SqHu := I.allowedBarFiveCharges.val
    let prod := SqHd.product (SqHu)
    let Filt := prod.filter (fun x => - x.1 + x.2 = 0)
    (Filt.map (fun x => (x.1, x.2)))
  | K2 =>
    let SqHd := I.allowedBarFiveCharges.val
    let SqHu := I.allowedBarFiveCharges.val
    let Q10 := toMultisetsOne I.allowedTenCharges
    let prod := SqHd.product (SqHu.product Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.1, x.2.2.toFinset)))
  | K1 =>
    let Q5 := toMultisetsOne I.allowedBarFiveCharges
    let Q10 := toMultisetsTwo I.allowedTenCharges
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => - x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (x.1.toFinset, x.2.toFinset)))
  | W4 =>
    let SqHd := I.allowedBarFiveCharges.val
    let SqHu := I.allowedBarFiveCharges.val
    let Q5 := toMultisetsOne I.allowedBarFiveCharges
    let prod := SqHd.product (SqHu.product Q5)
    let Filt := prod.filter (fun x => x.1 - 2 * x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.1, x.2.2.toFinset)))
  | W3 =>
    let SqHu := I.allowedBarFiveCharges.val
    let Q5 := toMultisetsTwo I.allowedBarFiveCharges
    let prod := SqHu.product Q5
    let Filt := prod.filter (fun x => - 2 * x.1 + x.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.toFinset)))
  | W2 =>
    let SqHd := I.allowedBarFiveCharges.val
    let Q10 := toMultisetsThree I.allowedTenCharges
    let prod := SqHd.product Q10
    let Filt := prod.filter (fun x => x.1 + x.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.toFinset))).filter fun x => IsIrreducible x
  | W1 =>
    let Q5 := toMultisetsOne I.allowedBarFiveCharges
    let Q10 := toMultisetsThree I.allowedTenCharges
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (x.1.toFinset, x.2.toFinset))).filter fun x => IsIrreducible x
  | Λ =>
    let Q5 := toMultisetsTwo I.allowedBarFiveCharges
    let Q10 := toMultisetsOne I.allowedTenCharges
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (x.1.toFinset, x.2.toFinset)))
  | β =>
    let SqHu := I.allowedBarFiveCharges.val
    let Q5 := toMultisetsOne I.allowedBarFiveCharges
    let prod := SqHu.product Q5
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.toFinset)))
  | topYukawa =>
    let SqHu := I.allowedBarFiveCharges.val
    let Q10 := toMultisetsTwo I.allowedTenCharges
    let prod := SqHu.product Q10
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.toFinset)))
  | bottomYukawa =>
    let SqHd := I.allowedBarFiveCharges.val
    let Q5 := toMultisetsOne I.allowedBarFiveCharges
    let Q10 := toMultisetsOne I.allowedTenCharges
    let prod := SqHd.product (Q5.product Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1.sum + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.1.toFinset, x.2.2.toFinset)))

lemma irreducibleSet'_card_eq (I : CodimensionOneConfig) (T : PotentialTerm) :
    (irreducibleSet' I T).card = irreducibleSetCard I T := by
  revert I T
  decide

lemma mem_irreducibleSet'_of_irreducible {I : CodimensionOneConfig} {T : PotentialTerm}
    (x : ChargeType T) (h : IsIrreducible x) (hx : x ∈ chargeSubsetFull I T) :
    x ∈ irreducibleSet' I T := by
  match T, x with
  | μ, (qHd, qHu) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simpa using hx
    · -- sum
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map,
        Prod.mk.injEq, true_and, exists_eq_right]
      repeat rw [SProd.sprod]
      simp only [Multiset.instSProd]
      rw [Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton, and_self,
        true_and]
      omega
  | K1, (Q5, Q10) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨{q1}, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [chargeSubsetFull] at hx
      rw [Finset.mem_product] at hx
      obtain ⟨h5, h10⟩ := hx
      simp at h5 h10
      exact ⟨h5 h1, h10 h2, h10 h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right,]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.toFinset_singleton, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Finset.insert_val, Multiset.mem_ndinsert,
        true_or, or_true, and_self, true_and]
      omega
  | K2, (qHd, qHu, Q10) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb, hc⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb, hc h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | W1, (Q5, Q10) =>
    simp [irreducibleSet']
    apply And.intro _ h
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := x_isPresent
    refine ⟨{q1}, {q2, q3, q4}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [chargeSubsetFull] at hx
      rw [Finset.mem_product] at hx
      obtain ⟨h5, h10⟩ := hx
      simp at h5 h10
      exact ⟨h5 h1, h10 h2, h10 h3, h10 h4⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3, q4
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right,]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.toFinset_singleton, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Finset.insert_val, Multiset.mem_ndinsert,
        true_or, or_true, and_self, true_and]
      omega
  | W2, (qHd, Q10) =>
    simp [irreducibleSet']
    apply And.intro _ h
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3, q4}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb h2, hb h3, hb h4⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3, q4
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | W3, (qHu, Q5) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb h2, hb h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | W4, (qHd, qHu, Q5) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb, hc⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb, hc h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | Λ, (Q5, Q10) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨{q1, q2}, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [chargeSubsetFull] at hx
      rw [Finset.mem_product] at hx
      obtain ⟨h5, h10⟩ := hx
      simp at h5 h10
      exact ⟨⟨h5 h1, h5 h2⟩, h10 h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right,]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.toFinset_singleton, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Finset.insert_val, Multiset.mem_ndinsert,
        true_or, or_true, and_self, true_and]
      omega
  | β, (qHu, Q5) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb h2⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | topYukawa, (qHu, Q10) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb h2, hb h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega
  | bottomYukawa, (qHd, Q5, Q10) =>
    simp [irreducibleSet']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2}, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [chargeSubsetFull, Finset.product_eq_sprod, Finset.mem_product] at hx
      simp at hx
      obtain ⟨ha, hb, hc⟩ := hx
      simpa [Finset.insert_subset_iff] using ⟨ha, hb h2, hc h3⟩
    · -- sum
      simp
      omega
    · -- mem powerset
      apply subset_of_iff_mem_powerset.mp
      simp_all [Subset]
    · -- is present
      simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists]
      use q1, q2, q3
      simp only [Finset.singleton_product, Finset.map_val, Finset.product_val, Finset.insert_val,
        Finset.singleton_val, Function.Embedding.coeFn_mk, Multiset.mem_map, Prod.mk.injEq, true_and,
        exists_eq_right]
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Option.toFinset_some, Finset.singleton_val, Multiset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.toFinset_cons, Multiset.toFinset_singleton,
        Finset.insert_val, Multiset.mem_ndinsert, true_or, or_true, and_self, true_and]
      omega

lemma irreducibleSet_eq_irreducibleSet' (I : CodimensionOneConfig) (T : PotentialTerm) :
    irreducibleSet I T = irreducibleSet' I T := by
  apply Multiset.eq_of_le_of_card_le
  · refine (Multiset.le_iff_subset ?_).mpr ?_
    · exact irreducibleSet_nodup I T
    refine Multiset.subset_iff.mpr ?_
    intro x hx
    apply mem_irreducibleSet'_of_irreducible
    · exact isIrreducible_of_mem_irreducibleSet x hx
    · apply irreducibleSet_subset_chargeSubsetFull
      exact hx
  · rw [irreducibleSet'_card_eq, irreducibleSet_card_eq]

lemma mem_irreducibleSet_iff_isIrreducible {I : CodimensionOneConfig} {T : PotentialTerm}
    (x : ChargeType T) (hx : x ∈ chargeSubsetFull I T) :
    x ∈ irreducibleSet I T ↔ IsIrreducible x := by
  constructor
  · intro h
    apply isIrreducible_of_mem_irreducibleSet
    exact h
  · intro h
    rw [irreducibleSet_eq_irreducibleSet']
    apply mem_irreducibleSet'_of_irreducible
    · exact h
    · exact hx

end PotentialTerm
end SU5U1
end FTheory
