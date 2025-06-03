/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Basic
/-!

# Inserting charges into trees

For a tree of charges `T` we make two definitions.
One corresponding to getting all the new charges when
inserting a `q10` into each of the `Q10` finsets in `T`.
The other corresponding to getting all the new charges when
inserting a `q5` into each of the `Q5` finsets in `T`.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges

open PotentialTerm

namespace Tree

/-!

## Inserting a Q10 charge

-/

/-- The insertion of a charge `q10` into the finset underlying a leaf. -/
def Leaf.insertQ10 (T : Leaf) (x : ℤ) : Leaf :=
  match T with
  | .leaf xs => .leaf (insert x xs)

/-- The twig obtained by taking the new charges obtained by inserting `q10` into all
  leafs of a twig. -/
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

/-- The branch obtained by taking the new charges obtained by inserting `q10` into all
  leafs of a branch. -/
def Branch.insertQ10 (T : Branch) (x : ℤ) : Branch :=
  match T with
  | .branch xo twigs =>
    .branch xo (twigs.map fun ts => (Twig.insertQ10 ts x))

/-- The trunk obtained by taking the new charges obtained by inserting `q10` into all
  leafs of a trunk. -/
def Trunk.insertQ10 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk xo branches =>
    .trunk xo (branches.map fun bs => (Branch.insertQ10 bs x))

/-- The tree obtained by taking the new charges obtained by inserting `q10` into all
  leafs of a tree. -/
def insertQ10 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.insertQ10 ts x))

lemma insert_mem_insertQ10 {T : Tree} (x : Charges) (hx : x ∈ T) (q10 : ℤ) :
    (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ insertQ10 T q10 ∨
    (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ T := by
  by_cases hnotMem : (x.1, x.2.1, x.2.2.1, insert q10 x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [mem_iff_mem_toMultiset, toMultiset] at ⊢ hx
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
      intro y hx hn
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

/-- The twig obtained by taking the new charges obtained by inserting `q5` into the
  twig. -/
def Twig.insertQ5 (T : Twig) (x : ℤ) : Twig :=
  match T with
  | .twig xs leafs => .twig (insert x xs) leafs

/-- The branch obtained by taking the new charges obtained by inserting `q5` into the
  all the twigs. -/
def Branch.insertQ5 (T : Branch) (x : ℤ) : Branch :=
  match T with
  | .branch qHu twigs =>
    let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (insert x Q5)
      (leafs.filter (fun (.leaf Q10) => ¬ Branch.mem (.branch qHu twigs)
      (qHu, (insert x Q5), Q10))))
    .branch qHu insertTwigs

/-- The trunk obtained by taking the new charges obtained by inserting `q5` into the
  all the twigs. -/
def Trunk.insertQ5 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun bs => (Branch.insertQ5 bs x))

/-- The tree obtained by taking the new charges obtained by inserting `q5` into the
  all the twigs. -/
def insertQ5 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.insertQ5 ts x))

lemma insert_mem_insertQ5 {T : Tree} (x : Charges) (hx : x ∈ T) (q5 : ℤ) :
    (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ insertQ5 T q5 ∨
    (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ T := by
  by_cases hnotMem : (x.1, x.2.1, insert q5 x.2.2.1, x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [mem_iff_mem_toMultiset, toMultiset] at ⊢ hx
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
      (leafs.filter (fun (.leaf Q10) =>
        ¬ Branch.mem (.branch qHu twigs) (qHu, (insert q5 Q5), Q10)))
  constructor
  · simp [Branch.insertQ5]
    use .twig Q5 leafs
  simp only [Multiset.mem_filter]
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
  simp only [true_and]
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
    have h1 := insert_mem_insertQ5 (some xqHd, some xqHu, xQ5, xQ10) x_mem_T q5
    simp_all
  · have h10' := h10 q10 q10_mem_S10
    rw [Multiset.filter_eq_nil] at h10'
    apply h10'
    rw [← mem_iff_mem_toMultiset]
    have h1 := insert_mem_insertQ10 (some xqHd, some xqHu, xQ5, xQ10) x_mem_T q10
    simp_all

lemma subset_insert_filter_card_zero_inductive (T : Tree) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (insertQ10 T q10).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (insertQ5 T q5).toMultiset.filter p = ∅) :
    (n : ℕ) → (hn : n = y.card - x.card) → y ∉ T → ¬ p y
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

/-- For a proposition `p` if `(insertQ10 T q10).toMultiset.filter p`
  and `(insertQ5 T q5).toMultiset.filter p` for all `q5 ∈ S5` and `q10 ∈ S10` then
  if `x ∈ T` and `x ⊆ y` if `y ∉ T` then `¬ p y`.
  This assumes that all charges in `T` are complete, and that `p` satisfies
  `x ⊆ y → ¬ p x → ¬ p y`. -/
lemma subset_insert_filter_card_zero (T : Tree) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (insertQ10 T q10).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (insertQ5 T q5).toMultiset.filter p = ∅) :
      y ∉ T → ¬ p y :=
  subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet x hx y hsubset hy h10 h5
    (y.card - x.card) rfl

end Tree

end Charges

end SU5U1

end FTheory
