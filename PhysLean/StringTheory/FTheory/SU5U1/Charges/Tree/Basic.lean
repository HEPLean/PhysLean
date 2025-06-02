/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Data.Finset.Sort
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

inductive Leaf
  | leaf : Finset ℤ → Leaf
deriving DecidableEq

inductive Twig
  | twig : Finset ℤ → Multiset Leaf → Twig

inductive Branch
  | branch : Option ℤ → Multiset Twig → Branch

inductive Trunk
  | trunk : Option ℤ → Multiset Branch → Trunk

end Tree

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
    | .twig xs a => "twig " ++ reprStr xs  ++ " " ++ reprStr a

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
                leafs.map fun (leaf xL)  => (xT, xB, xTw, xL)

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
  inferInstanceAs (Decidable (match T with | .leaf xs => xs = x ))

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
    simp
    refine ⟨branch, hBranchMem, ?_⟩
    match branch with
    | .branch qHu twigs =>
    simp [Branch.mem] at htwig
    obtain ⟨hqHu, twig, hTwigMem, hleaf⟩ := htwig
    simp
    refine ⟨twig, hTwigMem, ?_⟩
    match twig with
    | .twig Q5 leafs =>
    simp [Twig.mem] at hleaf
    obtain ⟨hqHu, leaf, hLeafMem, hxs⟩ := hleaf
    simp
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


/-!

## Inserting charges.

-/

def Leaf.insertQ10 (T : Leaf) (x : ℤ) : Leaf :=
  match T with
  | .leaf xs => .leaf (insert x xs)

def Twig.insertQ10 (T : Twig) (x : ℤ) : Twig :=
  match T with
  | .twig xs leafs =>
    let leafFinst := leafs.map (fun l => match l with
      | .leaf ys => ys)
    let sub : Multiset (Finset ℤ) := leafFinst.filterMap (fun ys =>
      if ¬ insert x ys ∈ leafFinst then
        some (insert x ys)
      else
        none)
    .twig xs (sub.map (fun ys => .leaf ys))

def Branch.insertQ10 (T : Branch) (x : ℤ) : Branch :=
  match T with
  | .branch xo twigs =>
    .branch xo (twigs.map fun ts => (Twig.insertQ10 ts x))

def Trunk.insertQ10 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk xo branches =>
    .trunk xo (branches.map fun bs => (Branch.insertQ10 bs x))

def insertQ10 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.insertQ10 ts x))

lemma insert_mem_insertQ10 {T : Tree} (x : Charges) (hx : x ∈ T) (q10 : ℤ) :
    (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ insertQ10 T q10 ∨
    (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ T := by
  by_cases hnotMem  : (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [ mem_iff_mem_toMultiset, toMultiset] at ⊢ hx
  obtain ⟨trunk, htrunk, branch, hbranch, twig, htwig, leaf, hleaf, heq⟩ := hx
  rw [mem_iff_mem_toMultiset]
  simp [toMultiset]
  use (Trunk.insertQ10 trunk q10)
  constructor
  · simp [insertQ10]
    use trunk
  use (Branch.insertQ10 branch q10)
  constructor
  · simp [Trunk.insertQ10]
    use branch
  use (Twig.insertQ10 twig q10)
  constructor
  · simp [Branch.insertQ10]
    use twig
  use (Leaf.insertQ10 leaf q10)
  constructor
  · simp [Twig.insertQ10]
    use insert q10 leaf.1
    constructor
    · use leaf
      simp_all
      intro y  hx hn
      apply hnotMem
      rw [mem_iff_mem_toMultiset]
      simp [toMultiset]
      use trunk
      simp_all
      use branch
      simp_all
      use twig
      simp_all
      use y
      simp_all
      subst heq
      simp
    · rfl
  subst heq
  simp_all only
  rfl


lemma exists_of_mem_insertQ10 {T : Tree} (C : Charges) (q10 : ℤ)
    (h : C ∈ insertQ10 T q10) :
    ∃ qHd qHu Q5 Q10, C = (qHd, qHu, Q5, insert q10 Q10) ∧
      (qHd, qHu, Q5, Q10) ∈ T := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [insertQ10] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.insertQ10] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.insertQ10, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp only [Twig.insertQ10, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨Q10, ⟨leafT, leafT_mem, hQ10⟩, hPresent⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.insertQ10]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.insertQ10]
  have hC21 : C.2.2.1 = twigT.1 := by
    subst heq
    simp [Twig.insertQ10]
  have hC22 : C.2.2.2 = Q10 := by
    subst heq
    simp [Leaf.insertQ10, ← hPresent]
  have C_eq : C = (trunkT.1, branchT.1, twigT.1, Q10) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- The goal
  subst C_eq
  use trunkT.1, branchT.1, twigT.1, leafT.1
  simp [hQ10]
  apply mem_of_parts trunkT branchT twigT leafT
  all_goals simp_all


/-!

## Inserting a Q5 charge

-/

def Twig.insertQ5 (T : Twig) (x : ℤ) : Twig :=
  match T with
  | .twig xs leafs => .twig (insert x xs) leafs

def Branch.insertQ5 (T : Branch) (x : ℤ) : Branch :=
  match T with
  | .branch qHu twigs =>
    let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (insert x Q5)
      (leafs.filter (fun (.leaf Q10) => ¬ Branch.mem (.branch qHu twigs) (qHu, (insert x Q5), Q10))))
    .branch qHu insertTwigs

def Trunk.insertQ5 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun bs => (Branch.insertQ5 bs x))

def insertQ5 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.insertQ5 ts x))

lemma insert_mem_insertQ5 {T : Tree} (x : Charges) (hx : x ∈ T) (q5 : ℤ) :
    (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ insertQ5 T q5 ∨
    (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ T := by
  by_cases hnotMem  : (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [ mem_iff_mem_toMultiset, toMultiset] at ⊢ hx
  obtain ⟨trunk, htrunk, branch, hbranch, twig, htwig, leaf, hleaf, heq⟩ := hx
  rw [mem_iff_mem_toMultiset]
  simp [toMultiset]
  use (Trunk.insertQ5 trunk q5)
  constructor
  · simp [insertQ5]
    use trunk
  use (Branch.insertQ5 branch q5)
  constructor
  · simp [Trunk.insertQ5]
    use branch
  match branch with
  | .branch qHu twigs =>
  match twig with
  | .twig Q5 leafs =>
  use Twig.twig (insert q5 Q5)
      (leafs.filter (fun (.leaf Q10) => ¬ Branch.mem (.branch qHu twigs) (qHu, (insert q5 Q5), Q10)))
  constructor
  · simp [Branch.insertQ5]
    use .twig Q5 leafs
  simp
  use leaf
  simp_all
  constructor
  · by_contra hn
    apply hnotMem
    subst heq
    simp [Membership.mem, mem]
    use trunk
    refine ⟨htrunk, ?_⟩
    simp [Trunk.mem]
    use FTheory.SU5U1.Charges.Tree.Branch.branch qHu twigs
  · subst heq
    rfl


lemma exists_of_mem_insertQ5 {T : Tree} (C : Charges) (q5 : ℤ)
    (h : C ∈ insertQ5 T q5) :
    ∃ qHd qHu Q5 Q10, C = (qHd, qHu, insert q5 Q5, Q10) ∧
      (qHd, qHu, Q5, Q10) ∈ T := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [insertQ5] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.insertQ5] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.insertQ5, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp [Twig.insertQ5, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨leftI_mem, h_not_mem⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.insertQ5]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.insertQ5]
  have hC21 : C.2.2.1 = insert q5 twigT.1 := by
    subst heq
    simp [Twig.insertQ5]
  have hC22 : C.2.2.2 = leafI.1 := by
    subst heq
    simp [Leaf.insertQ10]
  have C_eq : C = (trunkT.1, branchT.1, insert q5 twigT.1, leafI.1) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- The goal
  subst C_eq
  use trunkT.1, branchT.1, twigT.1, leafI.1
  simp
  apply mem_of_parts trunkT branchT twigT leafI
  all_goals simp_all


/-!

## Inserting charges and minimal super sets

-/

lemma insert_filter_card_zero (T : Tree) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hComplet : ∀ x ∈ T, IsComplete x)
    (h10 : ∀ q10 : S10, (insertQ10 T q10).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (insertQ5 T q5).toMultiset.filter p = ∅) :
    ∀ x ∈ T, ∀ y ∈ minimalSuperSet S5 S10 x, y ∉ T → ¬ p y := by
  intro (xqHd, xqHu, xQ5, xQ10) x_mem_T y y_mem_minimalSuperSet y_not_in_T
  have x_isComplete : IsComplete (xqHd, xqHu, xQ5, xQ10) := hComplet _ x_mem_T
  have xqHd_isSome : xqHd.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHd_isSome
  obtain ⟨xqHd, rfl⟩ := xqHd_isSome
  have xqHu_isSome : xqHu.isSome := by
    simp [IsComplete] at x_isComplete
    exact x_isComplete.1
  rw [Option.isSome_iff_exists] at xqHu_isSome
  obtain ⟨xqHu, rfl⟩ := xqHu_isSome
  simp [minimalSuperSet] at y_mem_minimalSuperSet
  simp_all
  rcases y_mem_minimalSuperSet with ⟨y_neq_x, ⟨q5, q5_mem_S5, rfl⟩ | ⟨q10, q10_mem_S10, rfl⟩⟩
  · have h5' := h5 q5 q5_mem_S5
    rw [Multiset.filter_eq_nil] at h5'
    apply h5'
    rw [← mem_iff_mem_toMultiset]
    have h1 := insert_mem_insertQ5 (some xqHd, some xqHu, xQ5,  xQ10) x_mem_T q5
    simp_all
  · have h10' := h10 q10 q10_mem_S10
    rw [Multiset.filter_eq_nil] at h10'
    apply h10'
    rw [← mem_iff_mem_toMultiset]
    have h1 := insert_mem_insertQ10 (some xqHd, some xqHu, xQ5,  xQ10) x_mem_T q10
    simp_all

lemma subset_insert_filter_card_zero_inductive (T : Tree) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈  ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (insertQ10 T q10).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (insertQ5 T q5).toMultiset.filter p = ∅) :
    (n : ℕ) → (hn : n = y.card - x.card) →  y ∉ T → ¬ p y
  | 0, hn, hnot_in_T => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : x.card ≤ y.card := card_subset_le hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn, hnot_in_T => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    have hz' := insert_filter_card_zero T S5 S10 p hComplet h10 h5 x hx z hz
    by_cases hz_not_in_T : z ∉ T
    · apply hnotSubset
      · exact hsubsetz
      · exact hz' hz_not_in_T
    apply subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet z (n := n)
    · simpa using hz_not_in_T
    · exact hsubsetz
    · exact hy
    · exact fun q10 => h10 q10
    · exact fun q5 => h5 q5
    · rw [card_of_mem_minimalSuperSet z hz]
      omega
    · exact hnot_in_T

lemma subset_insert_filter_card_zero (T : Tree) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈  ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (insertQ10 T q10).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (insertQ5 T q5).toMultiset.filter p = ∅) :
     y ∉ T → ¬ p y  :=
  subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet x hx y hsubset hy h10 h5
   (y.card - x.card) rfl

end Tree

end Charges

end SU5U1

end FTheory
