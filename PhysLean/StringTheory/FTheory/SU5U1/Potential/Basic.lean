/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype
import PhysLean.StringTheory.FTheory.SU5U1.Charges
/-!

# Potential of the SU(5) + U(1) GUT for F-Theory

This file contains properties of the potential terms of the `SU(5)` SUSY GUT with an
additional `U(1)` gauge group in F-theory.

The terms from the superpotential considered are (arXiv:0912.0853) :
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

The terms of the Kahler potential are (arXiv:0912.0853) :
`K ⊃ K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

## Important results

- `PotentialTerm` : The inductive type indexing the potential terms.
- `violateRParity` : The finite set of terms which violate R-parity.
  `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
- `causeProtonDecay` : The finite set of terms which contribute to proton decay.
  `W¹`, `W²`, `K¹`, `λ`
- `IsPresent`: The condition on the potential terms for them to be present
  based on the `U(1)` charges.
-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT. -/
inductive PotentialTerm
  /-- The term `μ 5Hu 5̄Hd`. -/
  | μ : PotentialTerm
  /-- The term `𝛽ᵢ 5̄Mⁱ5Hu`. -/
  | β : PotentialTerm
  /-- The term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`. -/
  | Λ : PotentialTerm
  /-- The term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` -/
  | W1 : PotentialTerm
  /-- The term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`. -/
  | W2 : PotentialTerm
  /-- The term `W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu`. -/
  | W3 : PotentialTerm
  /-- The term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`. -/
  | W4 : PotentialTerm
  /-- The term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`. -/
  | K1 : PotentialTerm
  /-- The term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` -/
  | K2 : PotentialTerm
  /-- The term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`. -/
  | topYukawa : PotentialTerm
  /-- The term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd`. -/
  | bottomYukawa : PotentialTerm
deriving DecidableEq, Fintype

namespace PotentialTerm

/-- The finite set of terms in the superpotential and Kahler potential which violate R-parity.
- `𝛽ᵢ 5̄Mⁱ5Hu`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
These correspond to the terms with an odd number of matter fields.
-/
def violateRParity : Finset PotentialTerm :=
  {β, Λ, W2, W4, K1, K2}

/-- The finite set of terms in the superpotential and Kahler potential which are involved in
  proton decay.
- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
-/
def causeProtonDecay : Finset PotentialTerm :=
  {W1, Λ, W2, K1}

/-- The type of charges associated with the potential terms.
  The implicit order of the charges is: `qHd`, `qHu`, `Q5`, `Q10`.
  The types correspond to:
- `μ` : `qHd × qHu`
- `β` : `qHu × Q5`
- `Λ` : `Q5 × Q10`
- `W1` : `Q5 × Q10`
- `W2` : `qHd × Q10`
- `W3` : `qHu × Q5`
- `W4` : `qHd × qHu × Q5`
- `K1` : `Q5 × Q10`
- `K2` : `qHd × qHu × Q10`
- `topYukawa` : `qHu × Q10`
- `bottomYukawa` : `qHd × Q5 × Q10`
-/
def ChargeType : PotentialTerm → Type
    /- qHd × qHu -/
  | μ => Option ℤ × Option ℤ
  /- qHu × Q5 -/
  | β => Option ℤ × Finset ℤ
  /- Q5 × Q10 -/
  | Λ => Finset ℤ × Finset ℤ
  /- Q5 × Q10 -/
  | W1 => Finset ℤ × Finset ℤ
  /- qHd × Q10 -/
  | W2 => Option ℤ × Finset ℤ
  /- qHu × Q5 -/
  | W3 => Option ℤ × Finset ℤ
  /- qHd × qHu × Q5 -/
  | W4 =>Option ℤ × Option ℤ × Finset ℤ
  /- Q5 × Q10 -/
  | K1 => Finset ℤ × Finset ℤ
  /- qHd × qHu × Q10 -/
  | K2 => Option ℤ × Option ℤ × Finset ℤ
  /- qHu × Q10 -/
  | topYukawa => Option ℤ × Finset ℤ
  /- qHd × Q5 × Q10 -/
  | bottomYukawa => Option ℤ × Finset ℤ × Finset ℤ

instance : (T : PotentialTerm) → DecidableEq T.ChargeType
  | μ => inferInstanceAs (DecidableEq (Option ℤ × Option ℤ))
  | β => inferInstanceAs (DecidableEq (Option ℤ × Finset ℤ))
  | Λ => inferInstanceAs (DecidableEq (Finset ℤ × Finset ℤ))
  | W1 => inferInstanceAs (DecidableEq (Finset ℤ × Finset ℤ))
  | W2 => inferInstanceAs (DecidableEq (Option ℤ × Finset ℤ))
  | W3 => inferInstanceAs (DecidableEq (Option ℤ × Finset ℤ))
  | W4 => inferInstanceAs (DecidableEq (Option ℤ × Option ℤ × Finset ℤ))
  | K1 => inferInstanceAs (DecidableEq (Finset ℤ × Finset ℤ))
  | K2 => inferInstanceAs (DecidableEq (Option ℤ × Option ℤ × Finset ℤ))
  | topYukawa => inferInstanceAs (DecidableEq (Option ℤ × Finset ℤ))
  | bottomYukawa => inferInstanceAs (DecidableEq (Option ℤ × Finset ℤ × Finset ℤ))

/-!

## Subset relation on `ChargeType`

-/

instance (T : PotentialTerm) : HasSubset T.ChargeType where Subset x y :=
  match T with
  | μ => x.1.toFinset ⊆ y.1.toFinset ∧ x.2.toFinset ⊆ y.2.toFinset
  | β => x.1.toFinset ⊆ y.1.toFinset ∧ x.2 ⊆ y.2
  | Λ => x.1 ⊆ y.1 ∧ x.2 ⊆ y.2
  | W1 => x.1 ⊆ y.1 ∧ x.2 ⊆ y.2
  | W2 => x.1.toFinset ⊆ y.1.toFinset ∧ x.2 ⊆ y.2
  | W3 => x.1.toFinset ⊆ y.1.toFinset ∧ x.2 ⊆ y.2
  | W4 => x.1.toFinset ⊆ y.1.toFinset ∧ x.2.1.toFinset ⊆ y.2.1.toFinset ∧ x.2.2 ⊆ y.2.2
  | K1 => x.1 ⊆ y.1 ∧ x.2 ⊆ y.2
  | K2 => x.1.toFinset ⊆ y.1.toFinset ∧ x.2.1.toFinset ⊆ y.2.1.toFinset ∧ x.2.2 ⊆ y.2.2
  | topYukawa => x.1.toFinset ⊆ y.1.toFinset ∧ x.2 ⊆ y.2
  | bottomYukawa => x.1.toFinset ⊆ y.1.toFinset ∧ x.2.1 ⊆ y.2.1 ∧ x.2.2 ⊆ y.2.2

instance subsetDecidable : (T : PotentialTerm) → (x y : T.ChargeType) → Decidable (x ⊆ y)
  | μ, _, _ => instDecidableAnd
  | β, _, _ => instDecidableAnd
  | Λ, _, _ => instDecidableAnd
  | W1, _, _ => instDecidableAnd
  | W2, _, _ => instDecidableAnd
  | W3, _, _ => instDecidableAnd
  | W4, _, _ => instDecidableAnd
  | K1, _, _ => instDecidableAnd
  | K2, _, _ => instDecidableAnd
  | topYukawa, _, _ => instDecidableAnd
  | bottomYukawa, _, _ => instDecidableAnd

@[simp, refl]
lemma subset_refl {T : PotentialTerm} (x : T.ChargeType) : x ⊆ x := by
  fin_cases T <;> simp [Subset]

@[trans]
lemma subset_trans {T : PotentialTerm} {x y z : T.ChargeType} (h1 : x ⊆ y) (h2 : y ⊆ z) :
    x ⊆ z := by
  fin_cases T <;>
    simp_all [Subset]

def _root_.Option.powerset (x : Option ℤ) : Finset (Option ℤ) :=
  match x with
  | none => {none}
  | some x => {none, some x}

@[simp]
lemma _root_.Option.mem_powerset_iff {x : Option ℤ} (y : Option ℤ) :
    y ∈ x.powerset ↔ y.toFinset ⊆ x.toFinset :=
  match x, y with
  | none, none => by
    simp [Option.powerset]
  | none, some _ => by
    simp [Option.powerset]
  | some _, none => by
    simp [Option.powerset]
  | some _, some _ => by
    simp [Option.powerset]

def powerset {T : PotentialTerm} (x : T.ChargeType) : Finset T.ChargeType :=
  match T, x with
  | μ, (qHd, qHu) => qHd.powerset.product qHu.powerset
  | β, (qHu, Q5) => qHu.powerset.product Q5.powerset
  | Λ, (Q5, Q10) => Q5.powerset.product Q10.powerset
  | W1, (Q5, Q10) => Q5.powerset.product Q10.powerset
  | W2, (qHd, Q10) => qHd.powerset.product Q10.powerset
  | W3, (qHu, Q5) => qHu.powerset.product Q5.powerset
  | W4, (qHd, qHu, Q5) => qHd.powerset.product (qHu.powerset.product Q5.powerset)
  | K1, (Q5, Q10) => Q5.powerset.product Q10.powerset
  | K2, (qHd, qHu, Q10) => qHd.powerset.product (qHu.powerset.product Q10.powerset)
  | topYukawa, (qHu, Q10) => qHu.powerset.product Q10.powerset
  | bottomYukawa, (qHd, Q5, Q10) => qHd.powerset.product (Q5.powerset.product Q10.powerset)

lemma subset_of_iff_mem_powerset {T : PotentialTerm} {x y : T.ChargeType} :
    x ⊆ y ↔ x ∈ powerset y := by
  fin_cases T
  all_goals
    cases x
    cases y
    simp only [powerset, Finset.product_eq_sprod]
    rw [Finset.mem_product]
    simp_all [Subset]

@[simp]
lemma self_mem_powerset {T : PotentialTerm} (x : T.ChargeType) :
    x ∈ powerset x := by
  rw [← subset_of_iff_mem_powerset]

/-!

## The charges associated with the potential terms

-/

/-- The U(1) charges of each potential term given an element of the corresponding `ChargeType`.
  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 3` then
  the charges of this term would be `{-3, -1}`. -/
def charges : (T : PotentialTerm) → T.ChargeType → Multiset ℤ
  | μ, (qHd, qHu) => (qHd.toFinset.product <| qHu.toFinset).val.map (fun x => x.1 - x.2)
  | β, (qHu, Q5) => (qHu.toFinset.product <| Q5).val.map (fun x => - x.1 + x.2)
  | Λ, (Q5, Q10) => (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1, (Q5, Q10) => (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2, (qHd, Q10) => (qHd.toFinset.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W3, (qHu, Q5) => (qHu.toFinset.product <| Q5.product <| Q5).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2)
  | W4, (qHd, qHu, Q5) => (qHd.toFinset.product <| qHu.toFinset.product <| Q5).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2)
  | K1, (Q5, Q10) => (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2, (qHd, qHu, Q10) => (qHd.toFinset.product <| qHu.toFinset.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)
  | topYukawa, (qHu, Q10) => (qHu.toFinset.product <| Q10.product <| Q10).val.map
    (fun x => -x.1 + x.2.1 + x.2.2)
  | bottomYukawa, (qHd, Q5, Q10) => (qHd.toFinset.product <| Q5.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)

lemma charges_of_subset (T : PotentialTerm) {x y : T.ChargeType} (h : x ⊆ y) :
    charges T x ⊆ charges T y := by
  match T, x, y with
  | μ, (qHd, qHu), (qHd', qHu') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2⟩
  | β, (qHu, Q5), (qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2⟩
  | Λ, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.1 h'.2.1, h.2 h'.2.2⟩
  | W1, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3, q4) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2.1, h.2 h'.2.2.2⟩
  | W2, (qHd, Q10), (qHd', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3, q4) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2.1, h.2 h'.2.2.2⟩
  | W3, (qHu, Q5), (qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | W4, (qHd, qHu, Q5), (qHd', qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩
  | K1, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | K2, (qHd, qHu, Q10), (qHd', qHu', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩
  | topYukawa, (qHu, Q10), (qHu', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | bottomYukawa, (qHd, Q5, Q10), (qHd', Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubsetChargeType] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩

/-- Given a `I : CodimensionOneConfig`, and a potential term `PotentialTerm`, the
  possible finite set of elements of `T.ChargeType` which orginate from charges allowed by `I`. -/
def chargeSubsetFull (I : CodimensionOneConfig) (T : PotentialTerm) : Finset T.ChargeType :=
  let SqHd := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
  let SqHu := {none} ∪ I.allowedBarFiveCharges.map ⟨Option.some, Option.some_injective ℤ⟩
  let SQ5 := I.allowedBarFiveCharges.powerset
  let SQ10 := I.allowedTenCharges.powerset
  match T with
  | μ => SqHd.product SqHu
  | K2 => SqHd.product (SqHu.product SQ10)
  | K1 => SQ5.product SQ10
  | W4 => SqHd.product (SqHu.product SQ5)
  | W3 => SqHu.product SQ5
  | W2 => SqHd.product SQ10
  | W1 => SQ5.product SQ10
  | Λ => SQ5.product SQ10
  | β => SqHu.product SQ5
  | topYukawa => SqHu.product SQ10
  | bottomYukawa => SqHd.product (SQ5.product SQ10)

/-!

## Excluded terms based on `U(1)` charges

The terms in the potential can be excluded based on the presences of `U(1)` charges
they carry.

-/

/-- Given a potential term `T` with an element of it's associated `ChargeType`, the proposition
  corresonding to there been no `zero` in the charges of that term. That is to say, it is excluded
  by the `U(1)` charges.

  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 3`
  the charges of this term are `{-3, -1}`, and this is excluded by the `U(1)` charges.
  Thus `IsExcluded β (3, {0, 2})` would be `true`.
  -/
def IsExcluded (T : PotentialTerm) (x : T.ChargeType) : Prop :=
  0 ∉ T.charges x

/-!

### Decidability of `IsExcluded`

-/

/-- The decidability of `IsExcluded` for the potential terms. -/
instance : (T : PotentialTerm) → DecidablePred T.IsExcluded
  | μ => fun _ => instDecidableNot
  | β => fun _ => instDecidableNot
  | Λ => fun _ => instDecidableNot
  | W1 => fun _ => instDecidableNot
  | W2 => fun _ => instDecidableNot
  | W3 => fun _ => instDecidableNot
  | W4 => fun _ => instDecidableNot
  | K1 => fun _ =>instDecidableNot
  | K2 => fun _ => instDecidableNot
  | topYukawa => fun _ => instDecidableNot
  | bottomYukawa => fun _ => instDecidableNot

/-!

## Present terms based on `U(1)` charges

The terms in the potential can be present based on the presences of `U(1)` charges
they carry.

Of particular intrest is the presence of the top Yukawa term.

-/

/-- Given a potential term `T` with an element of it's associated `ChargeType`, the proposition
  corresonding to there been `zero` in the charges of that term. That is to say, it is present
  by the `U(1)` charges.

  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 2`
  the charges of this term are `{-2, 0}`, and this is excluded by the `U(1)` charges.
  Thus `IsPresent β (3, {0, 2})` would be `true`.
  -/
def IsPresent (T : PotentialTerm) (x : T.ChargeType) : Prop :=
  0 ∈ T.charges x

lemma not_isExcluded_iff_isPresent : (T : PotentialTerm) → (x : T.ChargeType) →
    ¬ T.IsExcluded x ↔ T.IsPresent x
  | μ => fun (qHd, qHu) => by simp [IsExcluded, IsPresent]
  | β => fun (qHu, Q5) => by simp [IsExcluded, IsPresent]
  | Λ => fun (Q5, Q10) => by simp [IsExcluded, IsPresent]
  | W1 => fun (Q5, Q10) => by simp [IsExcluded, IsPresent]
  | W2 => fun (qHd, Q10) => by simp [IsExcluded, IsPresent]
  | W3 => fun (qHu, Q5) => by simp [IsExcluded, IsPresent]
  | W4 => fun (qHd, qHu, Q5) => by simp [IsExcluded, IsPresent]
  | K1 => fun (Q5, Q10) => by simp [IsExcluded, IsPresent]
  | K2 => fun (qHd, qHu, Q10) => by simp [IsExcluded, IsPresent]
  | topYukawa => fun (qHu, Q10) => by simp [IsExcluded, IsPresent]
  | bottomYukawa => fun (qHd, Q5, Q10) => by simp [IsExcluded, IsPresent]

/-- The decidability of `IsPresent` for the potential terms. -/
instance (T : PotentialTerm) : DecidablePred T.IsPresent := fun _ => Multiset.decidableMem _ _

lemma isPresent_of_subset (T : PotentialTerm) {y x : T.ChargeType}
    (h : y ⊆ x) (hy : T.IsPresent y) : T.IsPresent x := T.charges_of_subset h hy

end PotentialTerm

end SU5U1

end FTheory
