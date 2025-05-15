/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Meta.Informal.SemiFormal
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
deriving DecidableEq

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
  | μ => ℤ × ℤ
  /- qHu × Q5 -/
  | β => ℤ × Multiset ℤ
  /- Q5 × Q10 -/
  | Λ => Multiset ℤ × Multiset ℤ
  /- Q5 × Q10 -/
  | W1 => Multiset ℤ × Multiset ℤ
  /- qHd × Q10 -/
  | W2 => ℤ × Multiset ℤ
  /- qHu × Q5 -/
  | W3 => ℤ × Multiset ℤ
  /- qHd × qHu × Q5 -/
  | W4 => ℤ × ℤ × Multiset ℤ
  /- Q5 × Q10 -/
  | K1 => Multiset ℤ × Multiset ℤ
  /- qHd × qHu × Q10 -/
  | K2 => ℤ × ℤ × Multiset ℤ
  /- qHu × Q10 -/
  | topYukawa => ℤ × Multiset ℤ
  /- qHd × Q5 × Q10 -/
  | bottomYukawa => ℤ × Multiset ℤ × Multiset ℤ

/-- The U(1) charges of each potential term given an element of the corresponding `ChargeType`.
  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 3` then
  the charges of this term would be `{-3, -1}`. -/
def charges : (T : PotentialTerm) → T.ChargeType → Multiset ℤ
  | μ => fun (qHd, qHu) => {- qHu + qHd}
  | β => fun (qHu, Q5) => Q5.map (fun x => x + (- qHu))
  | Λ => fun (Q5, Q10) => (Q5.product (Q5.product Q10)).map
    (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => fun (Q5, Q10) => (Q10.product (Q10.product (Q10.product Q5))).map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 => fun (qHd, Q10) => (Q10.product (Q10.product Q10)).map
    (fun x => x.1 + x.2.1 + x.2.2 + qHd)
  | W3 => fun (qHu, Q5) => (Q5.product Q5).map
    (fun x => x.1 + x.2 - qHu - qHu)
  | W4 => fun (qHd, qHu, Q5) => Q5.map (fun x => x + qHd + (- qHu) + (- qHu))
  | K1 => fun (Q5, Q10) => (Q10.product (Q10.product Q5)).map
    (fun x => x.1 + x.2.1 + (- x.2.2))
  | K2 => fun (qHd, qHu, Q10) => Q10.map (fun x => qHu + qHd + x)
  | topYukawa => fun (qHu, Q10) => ((Q10.product Q10)).map (fun x => x.1 + x.2 + (- qHu))
  | bottomYukawa => fun (qHd, Q5, Q10) => (Q10.product Q5).map (fun x => x.1 + x.2 + qHd)

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
def IsExcluded : (T : PotentialTerm) → T.ChargeType → Prop
  | μ => fun (qHd, qHu) => 0 ∉ charges μ (qHd, qHu)
  | β => fun (qHu, Q5) => 0 ∉ charges β (qHu, Q5)
  | Λ => fun (Q5, Q10) => 0 ∉ charges Λ (Q5, Q10)
  | W1 => fun (Q5, Q10) => 0 ∉ charges W1 (Q5, Q10)
  | W2 => fun (qHd, Q10) => 0 ∉ charges W2 (qHd, Q10)
  | W3 => fun (qHu, Q5) => 0 ∉ charges W3 (qHu, Q5)
  | W4 => fun (qHd, qHu, Q5) => 0 ∉ charges W4 (qHd, qHu, Q5)
  | K1 => fun (Q5, Q10) => 0 ∉ charges K1 (Q5, Q10)
  | K2 => fun (qHd, qHu, Q10) => 0 ∉ charges K2 (qHd, qHu, Q10)
  | topYukawa => fun (qHu, Q10) => 0 ∉ charges topYukawa (qHu, Q10)
  | bottomYukawa => fun (qHd, Q5, Q10) => 0 ∉ charges bottomYukawa (qHd, Q5, Q10)

/-!

### Equivalent conditions to `IsExcluded`

For different potential terms, the `IsExcluded` condition can be expressed in different ways,
which are faster to check with `decide`.

-/

lemma isExcluded_Λ_iff_Q5_intersect_Q5 (Q5Q10 : Multiset ℤ × Multiset ℤ) :
    IsExcluded Λ Q5Q10 ↔
    ((Q5Q10.1.product Q5Q10.1).map (fun x => - (x.1 + x.2)) ∩ Q5Q10.2 = ∅) := by
  obtain ⟨Q5, Q10⟩ := Q5Q10
  constructor
  · intro h
    simp only [IsExcluded, charges, Multiset.mem_map, Multiset.mem_product, Finset.mem_val,
      Prod.exists, not_exists, not_and, and_imp] at h
    simp only [Finset.product_eq_sprod, Finset.product_val, neg_add_rev, Multiset.empty_eq_zero]
    rw [Multiset.eq_zero_iff_forall_not_mem]
    simp only [Multiset.mem_inter, Multiset.mem_map, Prod.exists, Finset.mem_val, not_and,
      forall_exists_index, and_imp]
    intro q10 q51 q52 hq5 hsum hq10
    simp only [SProd.sprod, Multiset.mem_product, Finset.mem_val] at hq5
    have h1 := h q51 q52 q10 hq5.1 hq5.2 hq10
    omega
  · intro h
    simp only [IsExcluded, charges, Multiset.mem_map, Multiset.mem_product, Finset.mem_val,
      Prod.exists, not_exists, not_and, and_imp]
    intro q51 q52 q10 hq51 hq52 hq10 hsum
    simp only [Finset.product_eq_sprod, Finset.product_val, neg_add_rev, Multiset.empty_eq_zero,
      Multiset.eq_zero_iff_forall_not_mem, Multiset.mem_inter, Multiset.mem_map, Prod.exists,
      Finset.mem_val, not_and, forall_exists_index, and_imp] at h
    have h1 := (h q10 q51 q52 (by simpa [SProd.sprod] using ⟨hq51, hq52⟩)).mt (by simpa using hq10)
    omega

/-- A rewriting of the condition for `0` is not in the charges associated with the term
  `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ` in terms of the intersection of finite sets. -/
lemma isExcluded_K1_iff_Q10_intersect_Q10 (Q5Q10 : Multiset ℤ × Multiset ℤ) :
    IsExcluded K1 Q5Q10 ↔
    ((Q5Q10.2.product Q5Q10.2).map (fun x => x.1 + x.2) ∩ Q5Q10.1 = ∅) := by
  constructor
  · intro h
    simp only [IsExcluded, charges, Multiset.mem_map, Multiset.mem_product, Prod.exists, not_exists,
      not_and, and_imp] at h
    simp only [Finset.product_eq_sprod, Finset.product_val, neg_add_rev, Multiset.empty_eq_zero]
    rw [Multiset.eq_zero_iff_forall_not_mem]
    simp only [Multiset.mem_inter, Multiset.mem_map, Prod.exists, Finset.mem_val, not_and,
      forall_exists_index, and_imp]
    intro q5 q101 q102 hq10 hsum hq5
    simp only [SProd.sprod, Multiset.mem_product, Finset.mem_val] at hq10
    have h1 := h q101 q102 q5 hq10.1 hq10.2 hq5
    omega
  · intro h
    simp only [IsExcluded, charges, Multiset.mem_map, Multiset.mem_product, Finset.mem_val,
      Prod.exists, not_exists, not_and, and_imp]
    intro q51 q52 q10 hq51 hq52 hq10 hsum
    simp only [Finset.product_eq_sprod, Finset.product_val, neg_add_rev, Multiset.empty_eq_zero,
      Multiset.eq_zero_iff_forall_not_mem, Multiset.mem_inter, Multiset.mem_map, Prod.exists,
      Finset.mem_val, not_and, forall_exists_index, and_imp] at h
    have h1 := (h q10 q51 q52 (by simpa [SProd.sprod] using ⟨hq51, hq52⟩)).mt (by simpa using hq10)
    omega
/-!

### Decidability of `IsExcluded`

-/

/-- The decidability of `IsExcluded` for the potential terms. -/
instance : (T : PotentialTerm) → DecidablePred T.IsExcluded
  | μ => fun _ => instDecidableNot
  | β => fun _ => instDecidableNot
  | Λ => fun Q5Q10 => decidable_of_decidable_of_iff (isExcluded_Λ_iff_Q5_intersect_Q5 Q5Q10).symm
  | W1 => fun _ => instDecidableNot
  | W2 => fun _ => instDecidableNot
  | W3 => fun _ => instDecidableNot
  | W4 => fun _ => instDecidableNot
  | K1 => fun Q5Q10 =>
    decidable_of_decidable_of_iff (isExcluded_K1_iff_Q10_intersect_Q10 Q5Q10).symm
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
def IsPresent : (T : PotentialTerm) → T.ChargeType → Prop
  | μ => fun (qHd, qHu) => 0 ∈ charges μ (qHd, qHu)
  | β => fun (qHu, Q5) => 0 ∈ charges β (qHu, Q5)
  | Λ => fun (Q5, Q10) => 0 ∈ charges Λ (Q5, Q10)
  | W1 => fun (Q5, Q10) => 0 ∈ charges W1 (Q5, Q10)
  | W2 => fun (qHd, Q10) => 0 ∈ charges W2 (qHd, Q10)
  | W3 => fun (qHu, Q5) => 0 ∈ charges W3 (qHu, Q5)
  | W4 => fun (qHd, qHu, Q5) => 0 ∈ charges W4 (qHd, qHu, Q5)
  | K1 => fun (Q5, Q10) => 0 ∈ charges K1 (Q5, Q10)
  | K2 => fun (qHd, qHu, Q10) => 0 ∈ charges K2 (qHd, qHu, Q10)
  | topYukawa => fun (qHu, Q10) => 0 ∈ charges topYukawa (qHu, Q10)
  | bottomYukawa => fun (qHd, Q5, Q10) => 0 ∈ charges bottomYukawa (qHd, Q5, Q10)

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

lemma isPresent_topYukawa_iff_Q10_product_Q10 (qHuQ10 : ℤ × Multiset ℤ) :
    IsPresent topYukawa qHuQ10 ↔
      qHuQ10.1 ∈ (qHuQ10.2.product qHuQ10.2).map (fun x => x.1 + x.2) := by
  obtain ⟨qHu, Q10⟩ := qHuQ10
  constructor
  · simp [IsPresent, charges]
    intro q1 q2 h1 h2 hsum
    use q1, q2
    simp_all
    omega
  · simp [IsPresent, charges]
    intro q1 q2 h1 h2 hsum
    use q1, q2
    simp_all

/-- The decidability of `IsPresent` for the potential terms. -/
instance : (T : PotentialTerm) → DecidablePred T.IsPresent
  | μ => fun _ => Multiset.decidableMem _ _
  | β => fun _ => Multiset.decidableMem _ _
  | Λ => fun _ => Multiset.decidableMem _ _
  | W1 => fun _ => Multiset.decidableMem _ _
  | W2 => fun _ => Multiset.decidableMem _ _
  | W3 => fun _ => Multiset.decidableMem _ _
  | W4 => fun _ => Multiset.decidableMem _ _
  | K1 => fun _ => Multiset.decidableMem _ _
  | K2 => fun _ => Multiset.decidableMem _ _
  | topYukawa => fun qHuQ10 =>
    decidable_of_decidable_of_iff (isPresent_topYukawa_iff_Q10_product_Q10 qHuQ10).symm
  | bottomYukawa => fun _ => Multiset.decidableMem _ _

end PotentialTerm

end SU5U1

end FTheory
