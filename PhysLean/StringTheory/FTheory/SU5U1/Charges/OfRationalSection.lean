/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.TODO.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.BigOperators.Group.List.Basic
/-!

# Allowed charges

For an SU(5) GUT model in F-theory with an additional U(1) symmetry,
this module gives the possible charges of the matter fields.

## References

Lawrie, Schafer-Nameki and Wong.
F-theory and All Things Rational: Surveying U(1) Symmetries with Rational Sections
<https://arxiv.org/pdf/1504.05593>. Page 6.

## TODO

The results in this file are currently stated, but not proved.

-/

TODO "AETF6" "The results in this file are currently stated, but not proved.
  They should should be proved following e.g. https://arxiv.org/pdf/1504.05593.
  This is a large project."

namespace FTheory

namespace SU5U1

/-- The distinct codimension one configurations of the
  zero-section (`σ₀`) relativity to the additional rational section (`σ₁`s). -/
inductive CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the same `ℙ¹` of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(01)}` -/
  | same : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0|1)}` -/
  | nearestNeighbor : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the next to nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0||1)}` -/
  | nextToNearestNeighbor : CodimensionOneConfig
deriving DecidableEq

namespace CodimensionOneConfig

instance : Fintype CodimensionOneConfig where
  elems := {same, nearestNeighbor, nextToNearestNeighbor}
  complete := by
    intro I
    cases I <;> decide

/-- The allowed `U(1)`-charges of matter in the 5-bar representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedBarFiveCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-14, -9, -4, 1, 6, 11}
  | nextToNearestNeighbor => {-13, -8, -3, 2, 7, 12}

instance : (I : CodimensionOneConfig) → Fintype I.allowedBarFiveCharges
  | same => inferInstance
  | nearestNeighbor => inferInstance
  | nextToNearestNeighbor => inferInstance

/-- The allowed `U(1)`-charges of matter in the 5-bar representation of `SU(5)`
  given a `CodimensionOneConfig`, as ordered lists. -/
def allowedBarFiveChargesList : CodimensionOneConfig → List ℤ
  | same => [-3, -2, -1, 0, 1, 2, 3]
  | nearestNeighbor => [-14, -9, -4, 1, 6, 11]
  | nextToNearestNeighbor => [-13, -8, -3, 2, 7, 12]

@[simp]
lemma mem_allowedBarFiveChargesList_iff {I : CodimensionOneConfig} (x : ℤ) :
    x ∈ I.allowedBarFiveChargesList ↔ x ∈ I.allowedBarFiveCharges := by
  cases I <;> simp [allowedBarFiveChargesList, allowedBarFiveCharges]

lemma allowedBarFiveChargesList_nodup (I : CodimensionOneConfig) :
    I.allowedBarFiveChargesList.Nodup := by
  cases I <;> decide

/-- The allowed `U(1)`-charges of matter in the 10d representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedTenCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-12, -7, -2, 3, 8, 13}
  | nextToNearestNeighbor => {-9, -4, 1, 6, 11}

instance : (I : CodimensionOneConfig) → Fintype I.allowedTenCharges
  | same => inferInstance
  | nearestNeighbor => inferInstance
  | nextToNearestNeighbor => inferInstance

/-- The allowed `U(1)`-charges of matter in the 10d representation of `SU(5)`
  given a `CodimensionOneConfig`, as ordered lists. -/
def allowedTenChargesList : CodimensionOneConfig → List ℤ
  | same => [-3, -2, -1, 0, 1, 2, 3]
  | nearestNeighbor => [-12, -7, -2, 3, 8, 13]
  | nextToNearestNeighbor => [-9, -4, 1, 6, 11]

@[simp]
lemma mem_allowedTenChargesList_iff {I : CodimensionOneConfig} (x : ℤ) :
    x ∈ I.allowedTenChargesList ↔ x ∈ I.allowedTenCharges := by
  cases I <;> simp [allowedTenChargesList, allowedTenCharges]

lemma allowedTenChargesList_nodup (I : CodimensionOneConfig) :
    I.allowedTenChargesList.Nodup := by
  cases I <;> decide

/-!

## Multisets of charges

-/

/-- Given a multiset `S : Multiset ℤ` for which all elements are members of
    `I.allowedBarFiveCharges`, `fiveChargeMultisetToList I S` is a computable
    list whose underlying multiset is `S`. -/
def fiveChargeMultisetToList (I : CodimensionOneConfig) (S : Multiset ℤ) : List ℤ :=
  I.allowedBarFiveChargesList.flatMap (fun x => List.replicate (S.count x) x)

/-- Given a multiset `S : Multiset ℤ` for which all elements are members of
    `I.allowedTenCharges`, `tenChargeMultisetToList I S` is a computable
    list whose underlying multiset is `S`. -/
def tenChargeMultisetToList (I : CodimensionOneConfig) (S : Multiset ℤ) : List ℤ :=
  I.allowedTenChargesList.flatMap (fun x => List.replicate (S.count x) x)

lemma fiveChargeMultisetToList_mem_iff {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}:
    a ∈ fiveChargeMultisetToList I S ↔ (a ∈ S ∧ a ∈ I.allowedBarFiveCharges) := by
  simp [fiveChargeMultisetToList]
  aesop

lemma tenChargeMultisetToList_mem_iff {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}:
    a ∈ tenChargeMultisetToList I S ↔ (a ∈ S ∧ a ∈ I.allowedTenCharges) := by
  simp [tenChargeMultisetToList]
  aesop

lemma fiveChargeMultisetToList_count {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}
    (hmem : a ∈ I.allowedBarFiveCharges) :
    (fiveChargeMultisetToList I S).count a = S.count a := by
  by_cases hS : a ∈ S
  · have hmem : a ∈ (fiveChargeMultisetToList I S) := by
      rw [fiveChargeMultisetToList_mem_iff]
      exact ⟨hS, hmem⟩
    simp [fiveChargeMultisetToList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x S) x) =
        fun x => if a = x then Multiset.count x S else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : List.count a I.allowedBarFiveChargesList = 1 := by
      refine List.count_eq_one_of_mem ?_ ?_
      exact CodimensionOneConfig.allowedBarFiveChargesList_nodup I
      rw [fiveChargeMultisetToList_mem_iff] at hmem
      simpa using hmem.2
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    omega
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [fiveChargeMultisetToList_mem_iff]
      simp_all

lemma tenChargeMultisetToList_count {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}
    (hmem : a ∈ I.allowedTenCharges) :
    (tenChargeMultisetToList I S).count a = S.count a := by
  by_cases hS : a ∈ S
  · have hmem : a ∈ (tenChargeMultisetToList I S) := by
      rw [tenChargeMultisetToList_mem_iff]
      exact ⟨hS, hmem⟩
    simp [tenChargeMultisetToList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x S) x) =
        fun x => if a = x then Multiset.count x S else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : List.count a I.allowedTenChargesList = 1 := by
      refine List.count_eq_one_of_mem ?_ ?_
      exact CodimensionOneConfig.allowedTenChargesList_nodup I
      rw [tenChargeMultisetToList_mem_iff] at hmem
      simpa using hmem.2
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    omega
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [tenChargeMultisetToList_mem_iff]
      simp_all

lemma coe_fiveChargeMultisetToList_of_all_mem (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedBarFiveCharges) :
    ↑(fiveChargeMultisetToList I S) = S := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ I.allowedBarFiveCharges
  · simp
    rw [fiveChargeMultisetToList_count ha]
  · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
    · aesop
    · simp [fiveChargeMultisetToList_mem_iff]
      aesop

lemma coe_tenChargeMultisetToList_of_all_mem (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedTenCharges) :
    ↑(tenChargeMultisetToList I S) = S := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ I.allowedTenCharges
  · simp
    rw [tenChargeMultisetToList_count ha]
  · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
    · aesop
    · simp [tenChargeMultisetToList_mem_iff]
      aesop

lemma fiveChargeMultisetToList_length (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedBarFiveCharges) :
    (fiveChargeMultisetToList I S).length = S.card := by
  trans Multiset.card (Multiset.ofList (fiveChargeMultisetToList I S))
  · rfl
  rw [coe_fiveChargeMultisetToList_of_all_mem I S hs]

lemma tenChargeMultisetToList_length (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedTenCharges) :
    (I.tenChargeMultisetToList S).length = S.card := by
  trans Multiset.card (Multiset.ofList (tenChargeMultisetToList I S))
  · rfl
  rw [coe_tenChargeMultisetToList_of_all_mem I S hs]

end CodimensionOneConfig
end SU5U1

end FTheory
