/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Charge profile

The charge profile is a data structure which can be associated with each term of the potential.

The charge profile is defined such that a given theory (that is specficication of
`SU(5) × U(1)` representations) gives for each term of the potential `T` an element of
`T.ChargeProfile`. This element specifies the possible values of charges
one can assign to the fields present in `T`.

For example for `T` the term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` the charge profile is `Finset ℤ × Finset ℤ`,
and a theory with 3 `5̄M` fields of charges `{-3, 2, 1}` and 2 `10` fields of charges `{0, 1}`
gives the charge profile `({-3, 2, 1}, {0, 1})` for this `T`.

## Related PRs

- See #562 for a first version of code related to charge profiles.

-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace PotentialTerm

/-- The charge profiles of the potential terms in the `SU(5) × U(1)` theory.
  This assigns to each potential term `T` a type `T.ChargeProfile`
  which specifies the possible values of charges one can assign to the fields present in `T`.

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
def ChargeProfile : PotentialTerm → Type
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
  | W4 => Option ℤ × Option ℤ × Finset ℤ
  /- Q5 × Q10 -/
  | K1 => Finset ℤ × Finset ℤ
  /- qHd × qHu × Q10 -/
  | K2 => Option ℤ × Option ℤ × Finset ℤ
  /- qHu × Q10 -/
  | topYukawa => Option ℤ × Finset ℤ
  /- qHd × Q5 × Q10 -/
  | bottomYukawa => Option ℤ × Finset ℤ × Finset ℤ

namespace ChargeProfile

/-- For each term in the potential the charge profile is a decidable type. -/
instance : (T : PotentialTerm) → DecidableEq T.ChargeProfile
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

## Subset relation on `ChargeProfile`

For each charge profile, there is the subset relation.
-/

instance (T : PotentialTerm) : HasSubset T.ChargeProfile where Subset x y :=
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

instance subsetDecidable : (T : PotentialTerm) → (x y : T.ChargeProfile) → Decidable (x ⊆ y)
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
lemma subset_refl {T : PotentialTerm} (x : T.ChargeProfile) : x ⊆ x := by
  fin_cases T <;> simp [Subset]

@[trans]
lemma subset_trans {T : PotentialTerm} {x y z : T.ChargeProfile} (h1 : x ⊆ y) (h2 : y ⊆ z) :
    x ⊆ z := by
  fin_cases T <;>
    simp_all [Subset]

lemma _root_.Option.toFinset_inj {x y : Option ℤ} :
    x = y ↔ x.toFinset = y.toFinset := by
  match x, y with
  | none, none => simp [Option.toFinset]
  | none, some a =>
    rw [show (none = some a) ↔ False by simp]
    simp only [Option.toFinset_none, Option.toFinset_some, false_iff, ne_eq]
    rw [Finset.eq_singleton_iff_unique_mem]
    simp
  | some _, none => simp [Option.toFinset]
  | some _, some _ => simp [Option.toFinset]

lemma subset_antisymm {T : PotentialTerm} {x y : T.ChargeProfile} (h1 : x ⊆ y) (h2 : y ⊆ x) :
    x = y := by
  match T, x, y with
  | μ, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2.toFinset = y2.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    rw [← Option.toFinset_inj] at hx1 hx2
    simp_all
  | β, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    rw [← Option.toFinset_inj] at hx1
    simp_all
  | Λ, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1 = y1 := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    simp_all
  | W1, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1 = y1 := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    simp_all
  | W2, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    rw [← Option.toFinset_inj] at hx1
    simp_all
  | W3, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    rw [← Option.toFinset_inj] at hx1
    simp_all
  | W4, (x1, x2, x3), (y1, y2, y3) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2.toFinset = y2.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.2.1, h2.2.1⟩
    have hx3 : x3 = y3 := Finset.Subset.antisymm_iff.mpr ⟨h1.2.2, h2.2.2⟩
    rw [← Option.toFinset_inj] at hx1 hx2
    simp_all
  | K1, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1 = y1 := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    simp_all
  | K2, (x1, x2, x3), (y1, y2, y3) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2.toFinset = y2.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.2.1, h2.2.1⟩
    have hx3 : x3 = y3 := Finset.Subset.antisymm_iff.mpr ⟨h1.2.2, h2.2.2⟩
    rw [← Option.toFinset_inj] at hx1 hx2
    simp_all
  | topYukawa, (x1, x2), (y1, y2) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2, h2.2⟩
    rw [← Option.toFinset_inj] at hx1
    simp_all
  | bottomYukawa, (x1, x2, x3), (y1, y2, y3) =>
    rw [Subset] at h1 h2
    dsimp [instHasSubset] at h1 h2
    have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨h1.1, h2.1⟩
    have hx2 : x2 = y2 := Finset.Subset.antisymm_iff.mpr ⟨h1.2.1, h2.2.1⟩
    have hx3 : x3 = y3 := Finset.Subset.antisymm_iff.mpr ⟨h1.2.2, h2.2.2⟩
    rw [← Option.toFinset_inj] at hx1
    simp_all

/-!

## The empty charge profile

-/

instance emptyInst (T : PotentialTerm) : EmptyCollection T.ChargeProfile where
  emptyCollection :=
  match T with
  | μ => (none, none)
  | β => (none, ∅)
  | Λ => (∅, ∅)
  | W1 => (∅, ∅)
  | W2 => (none, ∅)
  | W3 => (none, ∅)
  | W4 => (none, none, ∅)
  | K1 => (∅, ∅)
  | K2 => (none, none, ∅)
  | topYukawa => (none, ∅)
  | bottomYukawa => (none, ∅, ∅)

@[simp]
lemma empty_subset {T : PotentialTerm} (x : T.ChargeProfile) :
    ∅ ⊆ x := by
  fin_cases T <;>
    simp [Subset, instHasSubset, emptyInst]

@[simp]
lemma subset_of_empty_iff_empty {T : PotentialTerm} {x : T.ChargeProfile} :
    x ⊆ ∅ ↔ x = ∅ := by
  constructor
  · intro h
    apply subset_antisymm
    · exact h
    · exact empty_subset x
  · intro h
    subst h
    simp
/-!

## Powersets of charge profiles

-/

/-- The powerset of `x : Option ℤ` defined as `{none}` if `x` is `none`
  and `{none, some y}` is `x` is `some y`. -/
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

/-- The powerset of a charge profile. Given a charge profile `x : T.ChargeProfile`
  it's powerset is the finite set of all `T.ChargeProfile` which are subsets of `x`. -/
def powerset {T : PotentialTerm} (x : T.ChargeProfile) : Finset T.ChargeProfile :=
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

@[simp]
lemma mem_powerset_iff_subset {T : PotentialTerm} {x y : T.ChargeProfile} :
    x ∈ powerset y ↔ x ⊆ y := by
  fin_cases T
  all_goals
    cases x
    cases y
    simp only [powerset, Finset.product_eq_sprod]
    rw [Finset.mem_product]
    simp_all [Subset]

lemma self_mem_powerset {T : PotentialTerm} (x : T.ChargeProfile) :
    x ∈ powerset x := by simp

lemma empty_mem_powerset {T : PotentialTerm} (x : T.ChargeProfile) :
    ∅ ∈ powerset x := by simp

@[simp]
lemma powerset_of_empty {T : PotentialTerm} :
    powerset (∅ : T.ChargeProfile) = {∅} := by
  ext x
  simp

lemma powerset_subset_iff_subset {T : PotentialTerm} {x y : T.ChargeProfile} :
    powerset x ⊆ powerset y ↔ x ⊆ y := by
  constructor
  · intro h
    rw [← mem_powerset_iff_subset]
    apply h
    simp
  · intro h z
    simp only [mem_powerset_iff_subset]
    intro h1
    exact subset_trans h1 h

lemma min_exists_inductive {T : PotentialTerm} (S : Finset T.ChargeProfile) (hS : S ≠ ∅) :
    (n : ℕ) → (hn : S.card = n) →
    ∃ y ∈ S, powerset y ∩ S = {y}
  | 0, h => by simp_all
  | 1, h => by
    rw [Finset.card_eq_one] at h
    obtain ⟨y, rfl⟩ := h
    use y
    simp
  | n + 1 + 1, h => by
    rw [← Finset.nonempty_iff_ne_empty] at hS
    obtain ⟨y, hy⟩ := hS
    have hSremo : (S.erase y).card = n + 1 := by
      rw [Finset.card_erase_eq_ite]
      simp_all
    have hSeraseNeEmpty : (S.erase y) ≠ ∅ := by
        simp only [ne_eq]
        rw [← Finset.card_eq_zero]
        omega
    obtain ⟨x, hx1, hx2⟩ := min_exists_inductive (S.erase y) hSeraseNeEmpty (n + 1) hSremo
    have hxy : x ≠ y := by
      by_contra hn
      subst hn
      simp at hx1
    by_cases hyPx : y ∈ powerset x
    · use y
      constructor
      · exact hy
      · ext z
        constructor
        · intro hz
          simp at hz
          simp only [Finset.mem_singleton]
          rw [Finset.inter_erase] at hx2
          by_cases hn : z = y
          · exact hn
          apply False.elim
          have hlz : z ∈ (x.powerset ∩ S).erase y := by
            simp [hn, hz.2]
            simp at hyPx
            exact subset_trans hz.1 hyPx
          rw [hx2] at hlz
          simp at hlz
          simp_all
          have hx : y = x := by
            apply subset_antisymm
            · exact hyPx
            · exact hz
          exact hxy (id (Eq.symm hx))
        · intro hz
          simp at hz
          subst hz
          simp_all
    · use x
      constructor
      · apply Finset.erase_subset y S
        exact hx1
      · rw [← hx2]
        ext z
        simp only [Finset.mem_inter, mem_powerset_iff_subset, Finset.mem_erase, ne_eq,
          and_congr_right_iff, iff_and_self]
        intro hzx hzS hzy
        subst hzy
        simp_all

lemma min_exists {T : PotentialTerm} (S : Finset T.ChargeProfile) (hS : S ≠ ∅) :
    ∃ y ∈ S, powerset y ∩ S = {y} := min_exists_inductive S hS S.card rfl

/-!

## PartialOrder on `ChargeProfile`

The subset relation on `ChargeProfile` is a partial order.
It is not a linear order because subset inclusion is not total.

-/

instance {T : PotentialTerm} : PartialOrder T.ChargeProfile where
  le := (· ⊆ ·)
  le_refl := subset_refl
  le_antisymm := fun a b => subset_antisymm
  le_trans := fun a b c => subset_trans

/-!

## The charges associated with the potential terms

-/

/-- The U(1) charges of each potential term given an element of the corresponding `ChargeProfile`.
  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 3` then
  the charges of this term would be `{-3, -1}`. -/
def charges : {T : PotentialTerm} → T.ChargeProfile → Multiset ℤ
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

lemma charges_of_subset {T : PotentialTerm} {x y : T.ChargeProfile} (h : x ⊆ y) :
    charges x ⊆ charges y := by
  match T, x, y with
  | μ, (qHd, qHu), (qHd', qHu') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2⟩
  | β, (qHu, Q5), (qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2⟩
  | Λ, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.1 h'.2.1, h.2 h'.2.2⟩
  | W1, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3, q4) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2.1, h.2 h'.2.2.2⟩
  | W2, (qHd, Q10), (qHd', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3, q4) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product, Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2.1, h.2 h'.2.2.2⟩
  | W3, (qHu, Q5), (qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | W4, (qHd, qHu, Q5), (qHd', qHu', Q5') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩
  | K1, (Q5, Q10), (Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | K2, (qHd, qHu, Q10), (qHd', qHu', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩
  | topYukawa, (qHu, Q10), (qHu', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2 h'.2.1, h.2 h'.2.2⟩
  | bottomYukawa, (qHd, Q5, Q10), (qHd', Q5', Q10') =>
    simp only [charges, Finset.product_eq_sprod]
    simp only [Subset, instHasSubset] at h
    apply Multiset.map_subset_map
    refine Multiset.subset_iff.mpr ?_
    intro (q1, q2, q3) h'
    rw [← Multiset.mem_toFinset, Finset.val_toFinset, Finset.mem_product,
      Finset.mem_product] at ⊢ h'
    exact ⟨h.1 h'.1, h.2.1 h'.2.1, h.2.2 h'.2.2⟩

/-!

## Excluded terms based on `U(1)` charges

The terms in the potential can be excluded based on the presences of `U(1)` charges
they carry.

-/

/-- Given a potential term `T` with an element of it's associated `ChargeProfile`, the proposition
  corresonding to there been no `zero` in the charges of that term. That is to say, it is excluded
  by the `U(1)` charges.

  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 3`
  the charges of this term are `{-3, -1}`, and this is excluded by the `U(1)` charges.
  Thus `IsExcluded β (3, {0, 2})` would be `true`.
  -/
def IsExcluded {T : PotentialTerm} (x : T.ChargeProfile) : Prop :=
  0 ∉ charges x

/-!

### Decidability of `IsExcluded`

-/

/-- The decidability of `IsExcluded` for the potential terms. -/
instance : (T : PotentialTerm) → DecidablePred (IsExcluded (T := T))
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

/-- Given a potential term `T` with an element of it's associated `ChargeProfile`, the proposition
  corresonding to there been `zero` in the charges of that term. That is to say, it is present
  by the `U(1)` charges.

  For example, for the term `𝛽ᵢ 5̄Mⁱ5Hu` and `Q5 = {0, 2}` and `qHu = 2`
  the charges of this term are `{-2, 0}`, and this is excluded by the `U(1)` charges.
  Thus `IsPresent β (3, {0, 2})` would be `true`.
-/
def IsPresent (T : PotentialTerm) (x : T.ChargeProfile) : Prop :=
  0 ∈ x.charges

lemma not_isExcluded_iff_isPresent : (T : PotentialTerm) → (x : T.ChargeProfile) →
    ¬ x.IsExcluded ↔ x.IsPresent
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
instance (T : PotentialTerm) : DecidablePred (IsPresent (T := T)) :=
  fun _ => Multiset.decidableMem _ _

lemma isPresent_of_subset {T : PotentialTerm} {y x : T.ChargeProfile}
    (h : y ⊆ x) (hy : y.IsPresent) : x.IsPresent := charges_of_subset h hy

/-!

## Finsets of charge profiles

-/

/-- Given `S5 S10 : Finset ℤ` the finite set of charge profiles associated with
  a potential term `T` for which the 5-bar representation charges sit in `S5` and
  the 10d representation charges sit in `S10`. -/
def ofFinset (T : PotentialTerm) (S5 S10 : Finset ℤ) : Finset T.ChargeProfile :=
  let SqHd := {none} ∪ S5.map ⟨Option.some, Option.some_injective ℤ⟩
  let SqHu := {none} ∪ S5.map ⟨Option.some, Option.some_injective ℤ⟩
  let SQ5 := S5.powerset
  let SQ10 := S10.powerset
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

lemma mem_ofFinset_of_subset {T : PotentialTerm} (S5 S10 : Finset ℤ)
    {x y : T.ChargeProfile} (h : x ⊆ y) (hy : y ∈ ofFinset T S5 S10) :
    x ∈ ofFinset T S5 S10 := by
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  fin_cases T
  all_goals
    rw [ofFinset] at hy ⊢
    cases x
    cases y
    repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hy
    repeat rw [Finset.product_eq_sprod, Finset.mem_product]
    dsimp only at hy ⊢
    rw [Subset] at h
    dsimp only [instHasSubset] at h
    simp only [hoption, Finset.mem_powerset] at hy ⊢
    try exact ⟨h.1.trans hy.1, h.2.trans hy.2⟩
    try exact ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.trans hy.2.2⟩

/-- Given a `I : CodimensionOneConfig`, and a potential term `PotentialTerm`, the
  finite set of elements of `T.ChargeProfile` which orginate from charges allowed by `I`. -/
def finsetOfCodimensionOneConfig (I : CodimensionOneConfig) (T : PotentialTerm) :
    Finset T.ChargeProfile :=
  ofFinset T I.allowedBarFiveCharges I.allowedTenCharges

end ChargeProfile

end PotentialTerm

end SU5U1

end FTheory
