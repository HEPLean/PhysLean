/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Fluxes.NoExotics.Completeness
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Basic
/-!

# Fluxes into list

The types `FluxesFive` and `FluxesTen` are defined as multisets, but
when combining them with charges, they are needed as lists. Usually turning
a multiset into a list is done using choice, and therefore is not computable.
However, in the cases when `NoExotics` and `HasNoZero` hold, the elements of
`FluxesFive` and `FluxesTen` are known. Thus we can use those
elements to construct a list of the fluxes from multisets, in a way which is computable.
This file provides the definitions and lemmas needed to do this.

-/
namespace FTheory

namespace SU5U1

/-!

## `FluxesFive` to lists

-/

namespace FluxesFive

/-- The allowed pairs of fluxes in `FluxesFive` which have no exotics.

This can be found using:
  `(elemsNoExotics.bind (fun x => x.1)).toFinset`
-/
def allowedPairs : List (ℤ × ℤ) :=
  [(1, -1), (2, 1), (1, 0), (2, 0), (1, 1), (2, -1), (1, 2),
    (2, -2), (3, -3), (0, 3), (3, -2), (0, 2), (3, -1), (0, 1), (3, 0)]

lemma mem_allowedPairs_count_one (x : ℤ × ℤ) (hx : x ∈ allowedPairs) :
    @List.count (ℤ × ℤ) instBEqOfDecidableEq x allowedPairs = 1 := by
  revert x hx
  decide

lemma mem_allowedPairs_of_mem_noExotics (F : FluxesFive)
    (hf : F.NoExotics ∧ F.HasNoZero) (x : ℤ × ℤ)
    (h : x ∈ F) : x ∈ allowedPairs := by
  rw [noExotics_iff_mem_elemsNoExotics] at hf
  revert x
  revert F
  decide

/-- Constructs a list of `ℤ × ℤ` from a `F : FluxesFive`, if `F` is obeys
    `NoExotics` and `HasNoZero`, then this returns a list equivalent
    to the underlying multiset of `F`, else it returns junk. -/
def toList (F : FluxesFive) : List (ℤ × ℤ) :=
  allowedPairs.flatMap (fun x => List.replicate (F.count x) x)

lemma mem_allowedPairs_of_mem_toList (F : FluxesFive) (x : ℤ × ℤ)
    (h : x ∈ F.toList) : x ∈ allowedPairs := by
  simp [toList] at h
  exact h.1

lemma zero_not_mem_toList (F : FluxesFive) : (0, 0) ∉ F.toList := by
  by_contra h
  have h0 : (0, 0) ∈ allowedPairs := by
    exact mem_allowedPairs_of_mem_toList F (0, 0) h
  simp [allowedPairs] at h0

lemma mem_toList_iff {F : FluxesFive}
    (hf : F.NoExotics ∧ F.HasNoZero) {a : ℤ × ℤ} : a ∈ F.toList ↔ a ∈ F := by
  simp [toList]
  intro a_1
  obtain ⟨fst, snd⟩ := a
  exact mem_allowedPairs_of_mem_noExotics F hf (fst, snd) a_1

lemma toList_count {F : FluxesFive} {a : ℤ × ℤ} (hf : F.NoExotics ∧ F.HasNoZero)
    (hmema : a ∈ allowedPairs) : F.toList.count a = F.count a := by
  by_cases hS : a ∈ F
  · have hmem : a ∈ F.toList := by
      rw [mem_toList_iff hf]
      exact hS
    simp [toList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x F) x) =
        fun x => if a = x then Multiset.count x F else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : @List.count (ℤ × ℤ) instBEqOfDecidableEq a allowedPairs = 1 := by
      revert hmema
      clear * -
      intro h
      revert a
      decide
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    intro hn
    exact fun a_1 => ha' (id (Eq.symm hn))
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [mem_toList_iff hf]
      simp_all

lemma coe_toList(F : FluxesFive) (h : F.NoExotics ∧ F.HasNoZero) : ↑(F.toList) = F := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ allowedPairs
  · simp
    trans F.toList.count a
    · congr
      exact lawful_beq_subsingleton instBEqOfDecidableEq instBEqProd
    rw [toList_count h ha]
  · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
    · by_contra hn
      exact ha (mem_allowedPairs_of_mem_noExotics F h a hn)
    · by_contra hn
      rw [Multiset.mem_coe, mem_toList_iff h] at hn
      exact ha (mem_allowedPairs_of_mem_noExotics F h a hn)

lemma toList_length (F : FluxesFive) (h : F.NoExotics ∧ F.HasNoZero) :
    F.toList.length = F.card := by
  conv_rhs => rw [← coe_toList F h]
  exact rfl

end FluxesFive

/-!

## `FluxesTen` to lists

-/

namespace FluxesTen

/-- The allowed pairs of fluxes in `FluxesTen` which have no exotics.

This can be found using:
  `(elemsNoExotics.bind (fun x => x.1)).toFinset`
-/
def allowedPairs : List (ℤ × ℤ) :=
  [(1, 0), (2, 0), (1, -1), (2, 1), (1, 1), (2, -1), (3, 0)]

lemma mem_allowedPairs_count_one (x : ℤ × ℤ) (hx : x ∈ allowedPairs) :
    @List.count (ℤ × ℤ) instBEqOfDecidableEq x allowedPairs = 1 := by
  revert x hx
  decide

lemma mem_allowedPairs_of_mem_noExotics (F : FluxesTen)
    (hf : F.NoExotics ∧ F.HasNoZero) (x : ℤ × ℤ)
    (h : x ∈ F) : x ∈ allowedPairs := by
  rw [noExotics_iff_mem_elemsNoExotics] at hf
  revert x
  revert F
  decide

/-- Constructs a list of `ℤ × ℤ` from a `F : FluxesTen`, if `F` is obeys
    `NoExotics` and `HasNoZero`, then this returns a list equivalent
    to the underlying multiset of `F`, else it returns junk. -/
def toList (F : FluxesTen) : List (ℤ × ℤ) :=
  allowedPairs.flatMap (fun x => List.replicate (F.count x) x)

lemma mem_allowedPairs_of_mem_toList (F : FluxesTen) (x : ℤ × ℤ)
    (h : x ∈ F.toList) : x ∈ allowedPairs := by
  simp [toList] at h
  exact h.1

lemma zero_not_mem_toList (F : FluxesTen) : (0, 0) ∉ F.toList := by
  by_contra h
  have h0 : (0, 0) ∈ allowedPairs := by
    exact mem_allowedPairs_of_mem_toList F (0, 0) h
  simp [allowedPairs] at h0

lemma mem_toList_iff {F : FluxesTen}
    (hf : F.NoExotics ∧ F.HasNoZero) {a : ℤ × ℤ} : a ∈ F.toList ↔ a ∈ F := by
  simp [toList]
  intro a_1
  obtain ⟨fst, snd⟩ := a
  exact mem_allowedPairs_of_mem_noExotics F hf (fst, snd) a_1

lemma toList_count {F : FluxesTen} {a : ℤ × ℤ} (hf : F.NoExotics ∧ F.HasNoZero)
    (hmema : a ∈ allowedPairs) : F.toList.count a = F.count a := by
  by_cases hS : a ∈ F
  · have hmem : a ∈ F.toList := by
      rw [mem_toList_iff hf]
      exact hS
    simp [toList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x F) x) =
        fun x => if a = x then Multiset.count x F else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : @List.count (ℤ × ℤ) instBEqOfDecidableEq a allowedPairs = 1 := by
      revert hmema
      clear * -
      intro h
      revert a
      decide
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    intro hn
    exact fun a_1 => ha' (id (Eq.symm hn))
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [mem_toList_iff hf]
      simp_all

lemma coe_toList(F : FluxesTen) (h : F.NoExotics ∧ F.HasNoZero) : ↑(F.toList) = F := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ allowedPairs
  · simp
    trans F.toList.count a
    · congr
      exact lawful_beq_subsingleton instBEqOfDecidableEq instBEqProd
    rw [toList_count h ha]
  · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
    · by_contra hn
      exact ha (mem_allowedPairs_of_mem_noExotics F h a hn)
    · by_contra hn
      rw [Multiset.mem_coe, mem_toList_iff h] at hn
      exact ha (mem_allowedPairs_of_mem_noExotics F h a hn)

lemma toList_length (F : FluxesTen) (h : F.NoExotics ∧ F.HasNoZero) :
    F.toList.length = F.card := by
  conv_rhs => rw [← coe_toList F h]
  exact rfl

end FluxesTen

end SU5U1

end FTheory
