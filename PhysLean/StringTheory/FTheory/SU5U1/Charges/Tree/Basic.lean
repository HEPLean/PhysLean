/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Combinatorics.Additive.Dissociation
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
/-!

# Trees of charges

Naively one might which to store charges in `Mutliset Charges`.
However, this is not very efficent in terms of memory not membership checks.
Thus in this section we define a tree structure to store charges.
Our tree type is isomorphic to
`Option ℤ × Multiset (Option ℤ × Multiset (Finset ℤ × Multiset (Finset ℤ)))`,
although defined inductively.

We give definitions converting to and from `Mutliset Charges`.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges

open PotentialTerm

/-!

## Definition of the tree type

-/

namespace Tree

/-- A leaf of a tree contains the finite set of 10d representation charges, `Q10`. -/
inductive Leaf
  | leaf : Finset ℤ → Leaf
deriving DecidableEq

/-- A twig of a tree contains the finite set of 5d representation charges, `Q5`,
  and a multiset of leafs (`Q10`s). -/
inductive Twig
  | twig : Finset ℤ → Multiset Leaf → Twig

/-- A twig of a tree contains the charge `qHu`, and a multiset of twigs (`Q5` and `Q10`s). -/
inductive Branch
  | branch : Option ℤ → Multiset Twig → Branch

/-- A trunk of a tree contains the charge `qHd`, and a multiset of
  branches (`QHu`, `Q5` and `Q10`s). -/
inductive Trunk
  | trunk : Option ℤ → Multiset Branch → Trunk

end Tree

/-- A charge tree contains is an inductive type equivalent to
  `Option ℤ × Multiset (Option ℤ × Multiset (Finset ℤ × Multiset (Finset ℤ)))`.
  It contains charges in a tree-like structure to make membership tests etc. easier, and
  storage smaller. -/
inductive Tree
  | root : Multiset Tree.Trunk → Tree

namespace Tree

open Leaf Twig Branch Trunk

/-!

## Repr instances for the tree type

These instances allow the tree to be printed in a human-readable format,
and copied and pasted.

-/

unsafe instance : Repr Leaf where
  reprPrec x _ :=
    match x with
    | .leaf xs => "leaf " ++ reprStr xs

unsafe instance : Repr Twig where
  reprPrec x _ :=
    match x with
    | .twig xs a => "twig " ++ reprStr xs ++ " " ++ reprStr a

unsafe instance : Repr Branch where
  reprPrec x _ :=
    match x with
    | .branch xa a => "branch (" ++ reprStr xa ++ ") " ++ reprStr a

unsafe instance : Repr Trunk where
  reprPrec x _ :=
    match x with
    | .trunk xa a => "trunk (" ++ reprStr xa ++ ") " ++ reprStr a

unsafe instance : Repr Tree where
  reprPrec x _ :=
    match x with
    | .root xs => "root " ++ reprStr xs

/-!

## Conversion functions between the tree type and multiset of charges

-/

/-- A charge tree from a multiset of charges. -/
def fromMultiset (l : Multiset Charges) : Tree :=
  let A1 : Multiset (Option ℤ) := (l.map fun x => x.1).dedup
  root <| A1.map fun xa => trunk xa <|
    let B2 := (l.filter fun y => y.1 = xa)
    let C2 : Multiset (Option ℤ × Finset ℤ × Finset ℤ) := (B2.map fun y => y.2).dedup
    let A2 : Multiset (Option ℤ) := (C2.map fun x => x.1).dedup
    A2.map fun xb => branch xb <|
      let B3 := (C2.filter fun y => y.1 = xb)
      let C3 : Multiset (Finset ℤ × Finset ℤ) := (B3.map fun y => y.2).dedup
      let A3 : Multiset (Finset ℤ) := (C3.map fun x => x.1).dedup
      A3.map fun xc => twig xc <|
        let B4 := (C3.filter fun y => y.1 = xc)
        let C4 : Multiset (Finset ℤ) := (B4.map fun y => y.2).dedup
        C4.map fun xd => leaf xd

/-- A charge tree to a multiset of charges. -/
def toMultiset (T : Tree) : Multiset Charges :=
  match T with
  | .root trunks =>
    trunks.bind fun (trunk xT branches) =>
        branches.bind fun (branch xB twigs) =>
            twigs.bind fun (twig xTw leafs) =>
                leafs.map fun (leaf xL) => (xT, xB, xTw, xL)

/-!

## Cardinality of the tree

-/

/-- The cardinality of a `twig` is the number of leafs. -/
def Twig.card (T : Twig) : Nat :=
  match T with
  | .twig _ leafs => leafs.card

/-- The cardinality of a `branch` is the total number of leafs. -/
def Branch.card (T : Branch) : Nat :=
  match T with
  | .branch _ twigs => (twigs.map Twig.card).sum

/-- The cardinality of a `trunk` is the total number of leafs. -/
def Trunk.card (T : Trunk) : Nat :=
  match T with
  | .trunk _ branches => (branches.map Branch.card).sum

/-- The cardinality of a `tree` is the total number of leafs. -/
def card (T : Tree) : Nat :=
  match T with
  | .root trunks => (trunks.map Trunk.card).sum

lemma card_eq_toMultiset_card (T : Tree) : T.card = T.toMultiset.card := by
  match T with
  | .root trunks =>
    simp only [card, toMultiset, Multiset.card_bind, Function.comp_apply, Multiset.card_map]
    rfl

/-!

## Membership of a tree

Based on the tree structure we can define a faster membership criterion, which
is equivalent to membership based on charges.

-/

/-- Membership criterion for `x : Finset ℤ` in a leaf. -/
def Leaf.mem (T : Leaf) (x : Finset ℤ) : Prop :=
  match T with
  | .leaf xs => xs = x

instance (T : Leaf) (x : Finset ℤ) : Decidable (T.mem x) :=
  inferInstanceAs (Decidable (match T with | .leaf xs => xs = x))

/-- Membership criterion for `Finset ℤ × Finset ℤ` in a twig. -/
def Twig.mem (T : Twig) (x : Finset ℤ × Finset ℤ) : Prop :=
  match T with
  | .twig xs leafs => xs = x.1 ∧ ∃ leaf ∈ leafs, leaf.mem x.2

instance (T : Twig) (x : Finset ℤ × Finset ℤ) : Decidable (T.mem x) :=
  match T with
  | .twig _ leafs =>
    haveI : Decidable (∃ leaf ∈ leafs, leaf.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- Membership criterion for `Option ℤ × Finset ℤ × Finset ℤ` in a branch. -/
def Branch.mem (T : Branch) (x : Option ℤ × Finset ℤ × Finset ℤ) : Prop :=
  match T with
  | .branch xo twigs => xo = x.1 ∧ ∃ twig ∈ twigs, twig.mem x.2

instance (T : Branch) (x : Option ℤ × Finset ℤ × Finset ℤ) : Decidable (T.mem x) :=
  match T with
  | .branch _ twigs =>
    haveI : Decidable (∃ twig ∈ twigs, twig.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- Membership criterion for `Charges` in a trunk. -/
def Trunk.mem (T : Trunk) (x : Charges) : Prop :=
  match T with
  | .trunk xo branches => xo = x.1 ∧ ∃ branch ∈ branches, branch.mem x.2

instance (T : Trunk) (x : Charges) : Decidable (T.mem x) :=
  match T with
  | .trunk _ branches =>
    haveI : Decidable (∃ branch ∈ branches, branch.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- Membership criterion for `Charges` in a tree. -/
def mem (T : Tree) (x : Charges) : Prop :=
  match T with
  | .root trunks => ∃ trunk ∈ trunks, trunk.mem x

instance (T : Tree) (x : Charges) : Decidable (T.mem x) :=
  Multiset.decidableExistsMultiset

instance : Membership Charges Tree where
  mem := mem

instance (T : Tree) (x : Charges) : Decidable (x ∈ T) :=
  Multiset.decidableExistsMultiset

lemma mem_iff_mem_toMultiset (T : Tree) (x : Charges) :
    x ∈ T ↔ x ∈ T.toMultiset := by
  match T with
  | .root trunks =>
  conv_lhs => simp [Membership.mem, mem]
  simp [toMultiset]
  constructor
  · intro h
    obtain ⟨trunk, hTrunkMem, hbranch⟩ := h
    refine ⟨trunk, hTrunkMem, ?_⟩
    match trunk with
    | .trunk qHd branches =>
    simp [Trunk.mem] at hbranch
    obtain ⟨hqHu, branch, hBranchMem, htwig⟩ := hbranch
    simp only
    refine ⟨branch, hBranchMem, ?_⟩
    match branch with
    | .branch qHu twigs =>
    simp [Branch.mem] at htwig
    obtain ⟨hqHu, twig, hTwigMem, hleaf⟩ := htwig
    simp only
    refine ⟨twig, hTwigMem, ?_⟩
    match twig with
    | .twig Q5 leafs =>
    simp [Twig.mem] at hleaf
    obtain ⟨hqHu, leaf, hLeafMem, hxs⟩ := hleaf
    simp only
    refine ⟨leaf, hLeafMem, ?_⟩
    match leaf with
    | .leaf Q10 =>
    simp [Leaf.mem] at hxs
    simp_all
  · intro h
    obtain ⟨trunk, hTrunkMem, ⟨branch, hbranchMem, ⟨twig, htwigMem, ⟨leaf, hleafMem, heq⟩⟩⟩⟩ := h
    use trunk
    subst heq
    refine ⟨hTrunkMem, ?_⟩
    simp [Trunk.mem]
    use branch
    refine ⟨hbranchMem, ?_⟩
    simp [Branch.mem]
    use twig
    refine ⟨htwigMem, ?_⟩
    simp [Twig.mem]
    use leaf
    refine ⟨hleafMem, ?_⟩
    simp [Leaf.mem]

lemma mem_of_parts {T : Tree} {C : Charges} (trunk : Trunk) (branch : Branch)
    (twig : Twig) (leaf : Leaf)
    (trunk_mem : trunk ∈ T.1) (branch_mem : branch ∈ trunk.2)
    (twig_mem : twig ∈ branch.2) (leaf_mem : leaf ∈ twig.2)
    (heq : C = (trunk.1, branch.1, twig.1, leaf.1)) :
    C ∈ T := by
  rw [mem_iff_mem_toMultiset]
  simp [toMultiset]
  use trunk
  simp_all
  use branch
  simp_all
  use twig
  simp_all
  use leaf

end Tree

end Charges

end SU5U1

end FTheory
