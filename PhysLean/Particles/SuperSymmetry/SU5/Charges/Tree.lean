/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.DataStructures.FourTree.UniqueMap
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Completions
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimalSuperSet
/-!

# Trees of charges

It is convient to use `FourTree` to store charges. In this file we make
some auxillary definitions and lemmas which will help us in proofs
and make things faster.

In particular we define the `root`, `trunk`, `branch`, `twig` and `leaf`
specifically for `FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)`, this
allows Lean to read in large trees of charges more quickly.

We also prove some results related to `(T.uniqueMap3 (insert q5.1))` and
`(T.uniqueMap4 (insert q10.1))`, and their filters by a predicate `p : Charges → Prop`.

-/
namespace SuperSymmetry

namespace SU5

namespace Charges

namespace Tree
open PhysLean FourTree

instance (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (x : Charges) :
    Decidable (x ∈ T) :=
  inferInstanceAs (Decidable (x.toProd ∈ T))

/-- An explicit form of `FourTree.root` for charges. -/
def root : Multiset (Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) →
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) := fun b => .root b

/-- An explicit form of `FourTree.Trunk.trunk` for charges. -/
def trunk : (Option ℤ) → Multiset (Branch (Option ℤ) (Finset ℤ) (Finset ℤ)) →
    Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) := fun qHd b => .trunk qHd b

/-- An explicit form of `FourTree.Branch.branch` for charges. -/
def branch : (Option ℤ) → Multiset (Twig (Finset ℤ) (Finset ℤ)) →
    Branch (Option ℤ) (Finset ℤ) (Finset ℤ) := fun qHu b => .branch qHu b

/-- An explicit form of `FourTree.Twig.twig` for charges. -/
def twig : Finset ℤ → Multiset (Leaf (Finset ℤ)) → Twig (Finset ℤ) (Finset ℤ) :=
  fun q5 q10s => .twig q5 q10s

/-- An explicit form of `FourTree.Leaf.leaf` for charges. -/
def leaf : Finset ℤ → Leaf (Finset ℤ) := fun q10 => .leaf q10

/-!

## Inserting charges and minimal super sets

-/

lemma insert_filter_card_zero
    (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hComplet : ∀ x ∈ T, IsComplete x)
    (h10 : ∀ q10 : S10, (T.uniqueMap4 (insert q10.1)).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (T.uniqueMap3 (insert q5.1)).toMultiset.filter p = ∅) :
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
    have h1 := map_mem_uniqueMap3 (some xqHd, some xqHu, xQ5, xQ10) x_mem_T (insert q5)
    simp_all
  · have h10' := h10 q10 q10_mem_S10
    rw [Multiset.filter_eq_nil] at h10'
    apply h10'
    rw [← mem_iff_mem_toMultiset]
    have h1 := map_mem_uniqueMap4 (some xqHd, some xqHu, xQ5, xQ10) x_mem_T (insert q10)
    simp_all

lemma subset_insert_filter_card_zero_inductive
    (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ))
    (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (T.uniqueMap4 (insert q10.1)).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (T.uniqueMap3 (insert q5.1)).toMultiset.filter p = ∅) :
    (n : ℕ) → (hn : n = y.card - x.card) → y ∉ T → ¬ p y
  | 0, hn, hnot_in_T => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : x.card ≤ y.card := card_mono hsubset
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

/-- For a proposition `p` if `(T.uniqueMap4 (insert q10.1)).toMultiset.filter p`
  and `(T.uniqueMap3 (insert q5.1)).toMultiset.filter p` for all `q5 ∈ S5` and `q10 ∈ S10` then
  if `x ∈ T` and `x ⊆ y` if `y ∉ T` then `¬ p y`.
  This assumes that all charges in `T` are complete, and that `p` satisfies
  `x ⊆ y → ¬ p x → ¬ p y`. -/
lemma subset_insert_filter_card_zero
    (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ))
    (S5 S10 : Finset ℤ)
    (p : Charges → Prop) [DecidablePred p]
    (hnotSubset : ∀ (x y : Charges), x ⊆ y → ¬ p x → ¬ p y)
    (hComplet : ∀ x ∈ T, IsComplete x)
    (x : Charges)
    (hx : x ∈ T) (y : Charges) (hsubset : x ⊆ y)
    (hy : y ∈ ofFinset S5 S10)
    (h10 : ∀ q10 : S10, (T.uniqueMap4 (insert q10.1)).toMultiset.filter p = ∅)
    (h5 : ∀ q5 : S5, (T.uniqueMap3 (insert q5.1)).toMultiset.filter p = ∅) :
      y ∉ T → ¬ p y :=
  subset_insert_filter_card_zero_inductive T S5 S10 p hnotSubset hComplet x hx y hsubset hy h10 h5
    (y.card - x.card) rfl

end Tree

end Charges

end SU5

end SuperSymmetry
