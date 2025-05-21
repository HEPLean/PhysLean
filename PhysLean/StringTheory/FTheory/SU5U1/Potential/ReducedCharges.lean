/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Reduced charges of a potential term

For a `I : CodimensionOneConfig` and a `T : PotentialTerm`,
if `x : T.ChargeType` then `x` may have more (say) Q10 charges then 10d representations appearing
in `T`. The type `T.reducedCharges I` is the finite set of `T.ChargeType` that have
less then or equal to the number of `Q10` charges appearing in `T`, likwise for
`Q5`.

## Important results

- `reducedCharges`: The subset of `Finset T.ChargeType` of those sets of charges with
  with a number of 5-bar or 10d charges less then or
  equal to the times these representations appear in the term `T`.
- `isPresent_iff_subset_reducedCharges` the statement that a charge `x : T.ChargeType`
  leads to a potential term `T` if and only if there is a reduced charge `y : T.reducedCharges I`
  such that `y.1 ⊆ x` and `T.IsPresent y`.

-/
namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace PotentialTerm

open CodimensionOneConfig

/-- The subset of `Finset T.ChargeType` of those sets of charges with
  with a number of 5-bar or 10d charges less then or
  equal to the times these representations appear in the term `T`. -/
def reducedCharges (I : CodimensionOneConfig) : (T : PotentialTerm) → Finset T.ChargeType
  | μ =>
    let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    SqHd.product SqHu
  | K2 =>
    let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 1)
    SqHd.product (SqHu.product SQ10)
  | K1 =>
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)
    SQ5.product SQ10
  | W4 =>
    let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
    SqHd.product (SqHu.product SQ5)
  | W3 =>
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 2)
    SqHu.product SQ5
  | W2 =>
    let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)
    SqHd.product SQ10
  | W1 =>
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)
    SQ5.product SQ10
  | Λ =>
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 2)
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 1)
    SQ5.product SQ10
  | β =>
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
    SqHu.product SQ5
  | topYukawa =>
    let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 2)
    SqHu.product SQ10
  | bottomYukawa =>
    let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
    let SQ5 := I.allowedBarFiveCharges.powerset.filter (fun x => x.card ≤ 1)
    let SQ10 := I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 1)
    SqHd.product (SQ5.product SQ10)

/-- The reduced charges form a subset of `chargeSubsetFull`. -/
lemma reducedCharges_subset_chargeSubsetFull (I : CodimensionOneConfig) (T : PotentialTerm) :
    T.reducedCharges I ⊆ T.chargeSubsetFull I := by
  match T with
  | μ => simp [reducedCharges, chargeSubsetFull]
  | K2 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · apply Finset.product_subset_product
      · exact fun ⦃a⦄ a => a
      · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedTenCharges.powerset
  | K1 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedBarFiveCharges.powerset
    · exact Finset.filter_subset (fun x => x.card ≤ 2) I.allowedTenCharges.powerset
  | W4 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · apply Finset.product_subset_product
      · exact fun ⦃a⦄ a => a
      · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedBarFiveCharges.powerset
  | W3 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · exact Finset.filter_subset (fun x => x.card ≤ 2) I.allowedBarFiveCharges.powerset
  | W2 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · exact Finset.filter_subset (fun x => x.card ≤ 3) I.allowedTenCharges.powerset
  | W1 =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedBarFiveCharges.powerset
    · exact Finset.filter_subset (fun x => x.card ≤ 3) I.allowedTenCharges.powerset
  | Λ =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact Finset.filter_subset (fun x => x.card ≤ 2) I.allowedBarFiveCharges.powerset
    · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedTenCharges.powerset
  | β =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedBarFiveCharges.powerset
  | topYukawa =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · exact Finset.filter_subset (fun x => x.card ≤ 2) I.allowedTenCharges.powerset
  | bottomYukawa =>
    simp only [reducedCharges, Finset.product_eq_sprod, chargeSubsetFull]
    apply Finset.product_subset_product
    · exact fun ⦃a⦄ a => a
    · apply Finset.product_subset_product
      · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedBarFiveCharges.powerset
      · exact Finset.filter_subset (fun x => x.card ≤ 1) I.allowedTenCharges.powerset

/-- A charge `x : T.ChargeType` leads to a potential term `T` if and only if
  there is a reduced charge `y : T.reducedCharges I` such that `y.1 ⊆ x` and `T.IsPresent y`. -/
lemma isPresent_iff_subset_reducedCharges
    (I : CodimensionOneConfig) (T : PotentialTerm) (x : T.ChargeType)
    (hmem : x ∈ T.chargeSubsetFull I) :
    T.IsPresent x ↔ ∃ (y : T.reducedCharges I), y.1 ⊆ x ∧ T.IsPresent y := by
  apply Iff.intro _ (fun ⟨y, hsub, hy⟩ => isPresent_of_subset T hsub hy)
  intro h
  match T, x with
  | μ, (qHd, qHu) =>
    refine ⟨⟨(qHd, qHu), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      simp [reducedCharges]
      simp [chargeSubsetFull] at hmem
      rw [Finset.mem_product] at hmem ⊢
      simp_all [Finset.insert_subset_iff]
    · -- subset of charges
      simp [Subset]
    · -- is present
      simp_all [IsPresent, charges]
  | K2, (qHd, qHu, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    -- remove higgs
    simp at h1 h2
    subst h1 h2
    -- give subset
    refine ⟨⟨(q1, q2, {q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp at ⊢ hmem
      exact ⟨hmem.1, hmem.2.1, hmem.2.2 h3⟩
    · -- subset of charges
      simp [Subset]
      exact h3
    · -- is present
      simp [IsPresent, charges]
      omega
  | K1, (Q5, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    refine ⟨⟨({q1}, {q2, q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1 h1, ⟨hmem.2 h2, hmem.2 h3⟩, Finset.card_le_two⟩
    · -- subset of charges
      simp [Subset]
      exact ⟨h1, h2, h3⟩
    · -- is present
      simp [IsPresent, charges]
      use q2, q3
      rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, or_true, and_self,
        true_and]
      omega
  | W4, (qHd, qHu, Q5) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    -- remove higgs
    simp at h1 h2
    subst h1 h2
    -- give subset
    refine ⟨⟨(q1, q2, {q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, hmem.2.1, hmem.2.2 h3⟩
    · -- subset of charges
      simp [Subset]
      exact h3
    · -- is present
      simp [IsPresent, charges]
      omega
  | W3, (qHu, Q5) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    -- remove higgs
    simp at h1
    subst h1
    -- give subset
    refine ⟨⟨(q1, {q2, q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, ⟨hmem.2 h2, hmem.2 h3⟩, Finset.card_le_two⟩
    · -- subset of charges
      simp only [Subset, Option.toFinset_some, Finset.mem_singleton, imp_self, implies_true,
        Finset.mem_insert, forall_eq_or_imp, forall_eq, true_and]
      exact ⟨h2, h3⟩
    · -- is present
      simp [IsPresent, charges]
      use q2, q3
      rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, or_true, and_self,
        true_and]
      omega
  | W2, (qHd, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := h
    -- remove higgs
    simp at h1
    subst h1
    -- give subset
    refine ⟨⟨(q1, {q2, q3, q4}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, ⟨hmem.2 h2, hmem.2 h3, hmem.2 h4⟩, Finset.card_le_three⟩
    · -- subset of charges
      simp only [Subset, Option.toFinset_some, Finset.mem_singleton, imp_self, implies_true,
        Finset.mem_insert, forall_eq_or_imp, forall_eq, true_and]
      exact ⟨h2, h3, h4⟩
    · -- is present
      simp [IsPresent, charges]
      use q2, q3, q4
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, or_true, and_self,
        true_and]
      omega
  | W1, (Q5, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := h
    refine ⟨⟨({q1}, {q2, q3, q4}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1 h1, ⟨hmem.2 h2, hmem.2 h3, hmem.2 h4⟩, Finset.card_le_three⟩
    · -- subset of charges
      simp [Subset]
      exact ⟨h1, h2, h3, h4⟩
    · -- is present
      simp [IsPresent, charges]
      use q2, q3, q4
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, or_true, and_self,
        true_and]
      omega
  | Λ, (Q5, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    refine ⟨⟨({q1, q2}, {q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨⟨⟨hmem.1 h1, hmem.1 h2⟩, Finset.card_le_two⟩, hmem.2 h3⟩
    · -- subset of charges
      simp [Subset]
      exact ⟨⟨h1, h2⟩, h3⟩
    · -- is present
      simp [IsPresent, charges]
      use q1, q2, q3
      rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, Prod.mk.injEq, and_true,
        or_true, and_self, true_and]
      omega
  | β, (qHu, Q5) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := h
    -- remove higgs
    simp at h1
    subst h1
    -- give subset
    refine ⟨⟨(q1, {q2}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, hmem.2 h2⟩
    · -- subset of charges
      simp only [Subset, Option.toFinset_some, Finset.mem_singleton, imp_self, implies_true,
        Finset.mem_insert, forall_eq_or_imp, forall_eq, true_and]
      exact h2
    · -- is present
      simp [IsPresent, charges]
      omega
  | topYukawa, (qHu, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    -- remove higgs
    simp at h1
    subst h1
    -- give subset
    refine ⟨⟨(q1, {q2, q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, ⟨hmem.2 h2, hmem.2 h3⟩, Finset.card_le_two⟩
    · -- subset of charges
      simp only [Subset, Option.toFinset_some, Finset.mem_singleton, imp_self, implies_true,
        Finset.mem_insert, forall_eq_or_imp, forall_eq, true_and]
      exact ⟨h2, h3⟩
    · -- is present
      simp [IsPresent, charges]
      use q2, q3
      repeat rw [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      simp only [Multiset.mem_ndinsert, Multiset.mem_singleton, true_or, or_true, and_self,
        true_and]
      omega
  | bottomYukawa, (qHd, Q5, Q10) =>
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at h
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at h
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := h
    -- remove higgs
    simp at h1
    subst h1
    -- give subset
    refine ⟨⟨(q1, {q2}, {q3}), ?_⟩, ?_, ?_⟩
    · -- Member of the reduced charges
      rw [reducedCharges]
      rw [chargeSubsetFull] at hmem
      simp only [Finset.product_eq_sprod] at ⊢ hmem
      repeat rw [Finset.mem_product] at ⊢ hmem
      simp [Finset.insert_subset_iff] at ⊢ hmem
      exact ⟨hmem.1, hmem.2.1 h2, hmem.2.2 h3⟩
    · -- subset of charges
      simp only [Subset, Option.toFinset_some, Finset.mem_singleton, imp_self, implies_true,
        Finset.mem_insert, forall_eq_or_imp, forall_eq, true_and]
      exact ⟨h2, h3⟩
    · -- is present
      simp [IsPresent, charges]
      omega

/-!

## IsPresent

-/

/-- The finite set of reduced charges for which the corresponding potential term is present. -/
def reducedChargesIsPresent (I : CodimensionOneConfig) (T : PotentialTerm) : Finset T.ChargeType :=
  (reducedCharges I T).filter fun x => IsPresent T x

lemma reducedChargesIsPresent_subset_reducedCharges (I : CodimensionOneConfig) (T : PotentialTerm) :
    T.reducedChargesIsPresent I ⊆ T.reducedCharges I := by
  simp [reducedChargesIsPresent, reducedCharges]

end PotentialTerm
end SU5U1
end FTheory
