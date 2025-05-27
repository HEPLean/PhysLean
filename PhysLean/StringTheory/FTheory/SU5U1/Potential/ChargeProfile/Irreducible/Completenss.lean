/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Elems
/-!

# Completeness of irreducibleElems

This module proves the result
- `isIrreducible_iff_mem_irreducibleElems`
which states that an `x : T.ChargeProfile` which is in
`finsetOfCodimensionOneConfig I T` is irreducible if and only if it is in
`irreducibleElems I T`.

That is to say, that the multisets `irreducibleElems I T` contain all the irreducible
charge profiles for the given `CodimensionOneConfig` `I`.

The proof of this result is done by defining
`irreducibleElems'`
which is a multiset of all charge profiles for the given `CodimensionOneConfig` `I`
We show that all irreducible charge profiles are in `irreducibleElems' I T`.
Indeed, `irreducibleElems'` is defined to make easy.

We then show that `irreducibleElems' I T` has the same cardinality as `irreducibleElems I T`,
and therefore that the two are equal.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace PotentialTerm

namespace ChargeProfile


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

## irreducibleElems'

-/

def irreducibleElems' (I : CodimensionOneConfig) : (T : PotentialTerm) → Multiset T.ChargeProfile
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

lemma irreducibleElems'_card_eq (I : CodimensionOneConfig) (T : PotentialTerm) :
    (irreducibleElems' I T).card = irreducibleElemsCard I T := by
  revert I T
  decide

lemma mem_irreducibleElems'_of_irreducible {I : CodimensionOneConfig} {T : PotentialTerm}
    (x : ChargeProfile T) (h : IsIrreducible x) (hx : x ∈ finsetOfCodimensionOneConfig I T) :
    x ∈ irreducibleElems' I T := by
  match T, x with
  | μ, (qHd, qHu) =>
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨{q1}, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [finsetOfCodimensionOneConfig] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    apply And.intro _ h
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := x_isPresent
    refine ⟨{q1}, {q2, q3, q4}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [finsetOfCodimensionOneConfig] at hx
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
    simp [irreducibleElems']
    apply And.intro _ h
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, q4, ⟨h1, h2, h3, h4⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3, q4}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, q2, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1 h2
      subst h1 h2
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨{q1, q2}, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      simp [Finset.insert_subset_iff]
      simp [finsetOfCodimensionOneConfig] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2, q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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
    simp [irreducibleElems']
    have x_isPresent := isPresent_of_isIrreducible h
    simp only [IsPresent, charges, Finset.product_eq_sprod, Multiset.mem_map, Prod.exists] at x_isPresent
    simp only [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at x_isPresent
    obtain ⟨q1, q2, q3, ⟨h1, h2, h3⟩, hsum⟩ := x_isPresent
    refine ⟨q1, {q2}, {q3}, ⟨?_, ?_⟩, (h _ ?_).mpr ?_⟩
    · -- membership of Multiset
      rw [Option.mem_toFinset, Option.mem_def] at h1
      subst h1
      rw [finsetOfCodimensionOneConfig, Finset.product_eq_sprod, Finset.mem_product] at hx
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

/-!

## Completeness

-/

lemma irreducibleElems_eq_irreducibleElems' (I : CodimensionOneConfig) (T : PotentialTerm) :
    irreducibleElems I T = irreducibleElems' I T := by
  apply Multiset.eq_of_le_of_card_le
  · refine (Multiset.le_iff_subset ?_).mpr ?_
    · exact irreducibleElems_nodup I T
    refine Multiset.subset_iff.mpr ?_
    intro x hx
    apply mem_irreducibleElems'_of_irreducible
    · exact isIrreducible_of_mem_irreducibleElems x hx
    · apply irreducibleElems_subset_finsetOfCodimensionOneConfig
      exact hx
  · rw [irreducibleElems'_card_eq, irreducibleElems_card_eq]

lemma isIrreducible_iff_mem_irreducibleElems {I : CodimensionOneConfig} {T : PotentialTerm}
    (x : ChargeProfile T) (hx : x ∈ finsetOfCodimensionOneConfig I T) :
    IsIrreducible x ↔ x ∈ irreducibleElems I T := by
  symm
  constructor
  · intro h
    apply isIrreducible_of_mem_irreducibleElems
    exact h
  · intro h
    rw [irreducibleElems_eq_irreducibleElems']
    apply mem_irreducibleElems'_of_irreducible
    · exact h
    · exact hx

end ChargeProfile

end PotentialTerm

end SU5U1

end FTheory
