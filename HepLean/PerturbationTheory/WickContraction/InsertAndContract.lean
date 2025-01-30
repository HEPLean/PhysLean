/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.UncontractedList
/-!

# Inserting an element into a contraction based on a list

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/-!

## Inserting an element into a list

-/

/-- Given a Wick contraction `c` associated to a list `φs`,
  a position `i : Fin n.succ`, an element `φ`, and an optional uncontracted element
  `j : Option (c.uncontracted)` of `c`.
  The Wick contraction associated with `(φs.insertIdx i φ).length` formed by 'inserting' `φ`
  into `φs` after the first `i` elements and contracting it optionally with j. -/
def insertAndContract {φs : List 𝓕.States} (φ : 𝓕.States) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : Option φsΛ.uncontracted) :
    WickContraction (φs.insertIdx i φ).length :=
  congr (by simp) (φsΛ.insertAndContractNat i j)

@[inherit_doc insertAndContract]
scoped[WickContraction] notation φs "↩Λ" φ:max i:max j => insertAndContract φ φs i j

@[simp]
lemma insertAndContract_fstFieldOfContract (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option φsΛ.uncontracted)
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).fstFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.fstFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_sndFieldOfContract (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option (φsΛ.uncontracted))
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).sndFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.sndFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_fstFieldOfContract_some_incl (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
      (insertAndContract φ φsΛ i (some j)).fstFieldOfContract
      (congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩) =
      if i < i.succAbove j.1 then
      finCongr (insertIdx_length_fin φ φs i).symm i else
      finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j.1) := by
  split
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm i) (j :=
        finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (j := finCongr (insertIdx_length_fin φ φs i).symm i) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all only [Nat.succ_eq_add_one, Fin.val_fin_lt, not_lt, finCongr_apply, Fin.coe_cast]
      have hi : i.succAbove j ≠ i := Fin.succAbove_ne i j
      omega

/-!

## insertAndContract and getDual?

-/
@[simp]
lemma insertAndContract_none_getDual?_self (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm i) = none := by
  simp only [Nat.succ_eq_add_one, insertAndContract, getDual?_congr, finCongr_apply, Fin.cast_trans,
    Fin.cast_eq_self, Option.map_eq_none']
  have h1 := φsΛ.insertAndContractNat_none_getDual?_isNone i
  simpa using h1

lemma insertAndContract_isSome_getDual?_self (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)).isSome := by
  simp [insertAndContract, getDual?_congr]

lemma insertAndContract_some_getDual?_self_not_none (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ¬ ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)) = none := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_getDual?_self_eq (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm i))
    = some (Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)) := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_getDual?_some_eq (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
      (Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)))
    = some (Fin.cast (insertIdx_length_fin φ φs i).symm i) := by
  rw [getDual?_eq_some_iff_mem]
  rw [@Finset.pair_comm]
  rw [← getDual?_eq_some_iff_mem]
  simp

@[simp]
lemma insertAndContract_none_succAbove_getDual?_eq_none_iff (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length) :
    (φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
      (i.succAbove j)) = none ↔ φsΛ.getDual? j = none := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_succAbove_getDual?_eq_option (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length)
    (k : φsΛ.uncontracted) (hkj : j ≠ k.1) :
    (φsΛ ↩Λ φ i (some k)).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j)) = Option.map (Fin.cast (insertIdx_length_fin φ φs i).symm ∘ i.succAbove)
    (φsΛ.getDual? j) := by
  simp only [Nat.succ_eq_add_one, insertAndContract, getDual?_congr, finCongr_apply, Fin.cast_trans,
    Fin.cast_eq_self, ne_eq, hkj, not_false_eq_true, insertAndContractNat_some_getDual?_of_neq,
    Option.map_map]
  rfl

@[simp]
lemma insertAndContract_none_succAbove_getDual?_isSome_iff (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length) :
    ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
      (i.succAbove j))).isSome ↔ (φsΛ.getDual? j).isSome := by
  rw [← not_iff_not]
  simp

@[simp]
lemma insertAndContract_none_getDual?_get_eq (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length)
    (h : ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j))).isSome) :
    ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j))).get h = Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove ((φsΛ.getDual? j).get (by simpa using h))) := by
  simp [insertAndContract, getDual?_congr_get]

/-........................................... -/
@[simp]
lemma insertAndContract_sndFieldOfContract_some_incl (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).sndFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
      simp [insertAndContractNat]⟩) =
    if i < i.succAbove j.1 then
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j.1) else
    finCongr (insertIdx_length_fin φ φs i).symm i := by
  split
  · rename_i h
    refine (φsΛ ↩Λ φ i (some j)).eq_sndFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm i) (j :=
        finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all
  · rename_i h
    refine (φsΛ ↩Λ φ i (some j)).eq_sndFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (j := finCongr (insertIdx_length_fin φ φs i).symm i) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all only [Nat.succ_eq_add_one, Fin.val_fin_lt, not_lt, finCongr_apply, Fin.coe_cast]
      have hi : i.succAbove j ≠ i := Fin.succAbove_ne i j
      omega

lemma insertAndContract_none_prod_contractions (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ)
    (f : (φsΛ ↩Λ φ i none).1 → M) [CommMonoid M] :
    ∏ a, f a = ∏ (a : φsΛ.1), f (congrLift (insertIdx_length_fin φ φs i).symm
      (insertLift i none a)) := by
  let e1 := Equiv.ofBijective (φsΛ.insertLift i none) (insertLift_none_bijective i)
  let e2 := Equiv.ofBijective (congrLift (insertIdx_length_fin φ φs i).symm)
    ((φsΛ.insertAndContractNat i none).congrLift_bijective ((insertIdx_length_fin φ φs i).symm))
  erw [← e2.prod_comp]
  erw [← e1.prod_comp]
  rfl

lemma insertAndContract_some_prod_contractions (φ : 𝓕.States) (φs : List 𝓕.States)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted)
    (f : (φsΛ ↩Λ φ i (some j)).1 → M) [CommMonoid M] :
    ∏ a, f a = f (congrLift (insertIdx_length_fin φ φs i).symm
      ⟨{i, i.succAbove j}, by simp [insertAndContractNat]⟩) *
    ∏ (a : φsΛ.1), f (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i (some j) a)) := by
  let e2 := Equiv.ofBijective (congrLift (insertIdx_length_fin φ φs i).symm)
    ((φsΛ.insertAndContractNat i (some j)).congrLift_bijective ((insertIdx_length_fin φ φs i).symm))
  erw [← e2.prod_comp]
  let e1 := Equiv.ofBijective (φsΛ.insertLiftSome i j) (insertLiftSome_bijective i j)
  erw [← e1.prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Nat.succ_eq_add_one, Finset.prod_singleton,
    Finset.univ_eq_attach]
  rfl

/-- Given a finite set of `Fin φs.length` the finite set of `(φs.insertIdx i φ).length`
  formed by mapping elements using `i.succAboveEmb` and `finCongr`. -/
def insertAndContractLiftFinset (φ : 𝓕.States) {φs : List 𝓕.States}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    Finset (Fin (φs.insertIdx i φ).length) :=
    (a.map i.succAboveEmb).map (finCongr (insertIdx_length_fin φ φs i).symm).toEmbedding

@[simp]
lemma self_not_mem_insertAndContractLiftFinset (φ : 𝓕.States) {φs : List 𝓕.States}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    Fin.cast (insertIdx_length_fin φ φs i).symm i ∉ insertAndContractLiftFinset φ i a := by
  simp only [Nat.succ_eq_add_one, insertAndContractLiftFinset, Finset.mem_map_equiv, finCongr_symm,
    finCongr_apply, Fin.cast_trans, Fin.cast_eq_self]
  simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
  intro x
  exact fun a => Fin.succAbove_ne i x

lemma succAbove_mem_insertAndContractLiftFinset (φ : 𝓕.States) {φs : List 𝓕.States}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) (j : Fin φs.length) :
    Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)
    ∈ insertAndContractLiftFinset φ i a ↔ j ∈ a := by
  simp only [insertAndContractLiftFinset, Finset.mem_map_equiv, finCongr_symm, finCongr_apply,
    Fin.cast_trans, Fin.cast_eq_self]
  simp only [Finset.mem_map, Fin.succAboveEmb_apply]
  apply Iff.intro
  · intro h
    obtain ⟨x, hx1, hx2⟩ := h
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hx2
    simp_all
  · intro h
    use j

lemma insert_fin_eq_self (φ : 𝓕.States) {φs : List 𝓕.States}
    (i : Fin φs.length.succ) (j : Fin (List.insertIdx i φ φs).length) :
    j = Fin.cast (insertIdx_length_fin φ φs i).symm i
    ∨ ∃ k, j = Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) := by
  obtain ⟨k, hk⟩ := (finCongr (insertIdx_length_fin φ φs i).symm).surjective j
  subst hk
  by_cases hi : k = i
  · simp [hi]
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hi
    obtain ⟨z, hk⟩ := hi
    subst hk
    right
    use z
    rfl

lemma insertLift_sum (φ : 𝓕.States) {φs : List 𝓕.States}
    (i : Fin φs.length.succ) [AddCommMonoid M] (f : WickContraction (φs.insertIdx i φ).length → M) :
    ∑ c, f c =
    ∑ (φsΛ : WickContraction φs.length), ∑ (k : Option φsΛ.uncontracted), f (φsΛ ↩Λ φ i k) := by
  rw [sum_extractEquiv_congr (finCongr (insertIdx_length_fin φ φs i).symm i) f
    (insertIdx_length_fin φ φs i)]
  rfl

/-!

## Uncontracted list

-/
lemma insertAndContract_uncontractedList_none_map (φ : 𝓕.States) {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    [φsΛ ↩Λ φ i none]ᵘᶜ = List.insertIdx (φsΛ.uncontractedListOrderPos i) φ [φsΛ]ᵘᶜ := by
  simp only [Nat.succ_eq_add_one, insertAndContract, uncontractedListGet]
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_none]
  rw [orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx]
  rw [insertIdx_map, insertIdx_map]
  congr 1
  · simp
  rw [List.map_map, List.map_map]
  congr
  conv_rhs => rw [get_eq_insertIdx_succAbove φ φs i]
  rfl

@[simp]
lemma insertAndContract_uncontractedList_none_zero (φ : 𝓕.States) {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length) :
    [φsΛ ↩Λ φ 0 none]ᵘᶜ = φ :: [φsΛ]ᵘᶜ := by
  rw [insertAndContract_uncontractedList_none_map]
  simp [uncontractedListOrderPos]

end WickContraction
