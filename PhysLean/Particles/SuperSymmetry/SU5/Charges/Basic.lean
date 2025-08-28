/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import PhysLean.Particles.SuperSymmetry.SU5.Potential
/-!

# Charges

The data structure associated with additional charges in the SU(5) GUT model.

These charges are permitted to sit within any type `𝓩` which is usually taken
to be `ℤ` (for `U(1)` charges) or multiples thereof.

-/

namespace SuperSymmetry

namespace SU5

/-- The type such that an element corresponds to the collection of
  charges associated with the matter content of the theory.
  The order of charges is implicitly taken to be `qHd`, `qHu`, `Q5`, `Q10`.

  The `Q5` and `Q10` charges are represented by `Finset` rather than
  `Multiset`, so multiplicity is not included.

  This is defined for a general type `𝓩`, which could be e.g.
- `ℤ` in the case of `U(1)`,
- `ℤ × ℤ` in the case of `U(1) × U(1)`,
- `Fin 2` in the case of `ℤ₂` etc.
-/
def Charges (𝓩 : Type := ℤ) : Type := Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩

namespace Charges

variable {𝓩 : Type}

/-- The explicit casting of a term of type `Charges 𝓩` to a term of
  `Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩`. -/
def toProd (x : Charges 𝓩) : Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩 := x

lemma eq_of_parts {x y : Charges 𝓩} (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1)
    (h3 : x.2.2.1 = y.2.2.1) (h4 : x.2.2.2 = y.2.2.2) : x = y := by
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
    simp_all

lemma eq_iff {x y : Charges 𝓩} :
    x = y ↔ x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2 = y.2.2.2 := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    exact eq_of_parts h1 h2 h3 h4

/-!

## Basic instances on the type `Charges 𝓩`.

-/

instance [DecidableEq 𝓩] : DecidableEq (Charges 𝓩) := inferInstanceAs
  (DecidableEq (Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩))

unsafe instance [Repr 𝓩] : Repr (Charges 𝓩) where
  reprPrec x _ := match x with
    | (qHd, qHu, Q5, Q10) =>
      let s1 := reprStr qHd
      let s2 := reprStr qHu
      let s5 := reprStr Q5
      let s10 := reprStr Q10
      s!"({s1}, {s2}, {s5}, {s10})"

/-!

## Subsest relation

-/

instance hasSubset : HasSubset (Charges 𝓩) where
  Subset x y := x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧
    x.2.2.1 ⊆ y.2.2.1 ∧
    x.2.2.2 ⊆ y.2.2.2

instance hasSSubset : HasSSubset (Charges 𝓩) where
  SSubset x y := x ⊆ y ∧ x ≠ y

instance subsetDecidable [DecidableEq 𝓩] (x y : Charges 𝓩) : Decidable (x ⊆ y) := instDecidableAnd

lemma subset_def {x y : Charges 𝓩} : x ⊆ y ↔ x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧ x.2.2.1 ⊆ y.2.2.1 ∧ x.2.2.2 ⊆ y.2.2.2 := by
  rfl

@[simp, refl]
lemma subset_refl (x : Charges 𝓩) : x ⊆ x := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

lemma _root_.Option.toFinset_inj {x y : Option 𝓩} :
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

lemma subset_trans {x y z : Charges 𝓩} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := by
  simp_all [Subset]

lemma subset_antisymm {x y : Charges 𝓩} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  rw [Subset] at hxy hyx
  dsimp [hasSubset] at hxy hyx
  rcases x with ⟨x1, x2, x3, x4⟩
  rcases y with ⟨y1, y2, y3, y4⟩
  have hx1 : x1.toFinset = y1.toFinset := Finset.Subset.antisymm_iff.mpr ⟨hxy.1, hyx.1⟩
  have hx2 : x2.toFinset = y2.toFinset := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.1, hyx.2.1⟩
  have hx3 : x3 = y3 := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.2.1, hyx.2.2.1⟩
  have hx4 : x4 = y4 := Finset.Subset.antisymm_iff.mpr ⟨hxy.2.2.2, hyx.2.2.2⟩
  rw [← Option.toFinset_inj] at hx1 hx2
  simp_all

/-!

## The empty charges

-/

instance emptyInst : EmptyCollection (Charges 𝓩) where
  emptyCollection := (none, none, {}, {})

@[simp]
lemma empty_subset (x : Charges 𝓩) : ∅ ⊆ x := by
  simp [Subset, emptyInst]

@[simp]
lemma subset_of_empty_iff_empty {x : Charges 𝓩} :
    x ⊆ ∅ ↔ x = ∅ := by
  constructor
  · intro h
    apply subset_antisymm
    · exact h
    · exact empty_subset x
  · intro h
    subst h
    simp

@[simp]
lemma empty_qHd : (∅ : Charges 𝓩).1 = none := by
  simp [emptyInst]

@[simp]
lemma empty_qHu : (∅ : Charges 𝓩).2.1 = none := by
  simp [emptyInst]

@[simp]
lemma empty_Q5 : (∅ : Charges 𝓩).2.2.1 = ∅ := by
  simp [emptyInst]

@[simp]
lemma empty_Q10 : (∅ : Charges 𝓩).2.2.2 = ∅ := by
  simp [emptyInst]

/-!

## Card

-/

/-- The cardinality of a `Charges` is defined to be the sum of the cardinalities
  of each of the underlying finite sets of charges, with `Option ℤ` turned to finsets. -/
def card (x : Charges 𝓩) : Nat :=
  x.1.toFinset.card + x.2.1.toFinset.card + x.2.2.1.card + x.2.2.2.card

@[simp]
lemma card_empty : card (∅ : Charges 𝓩) = 0 := by
  simp [card, emptyInst]

lemma card_mono {x y : Charges 𝓩} (h : x ⊆ y) : card x ≤ card y := by
  simp [hasSubset] at h
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  simp [card]
  omega

lemma eq_of_subset_card {x y : Charges 𝓩} (h : x ⊆ y) (hcard : card x = card y) : x = y := by
  simp [card] at hcard
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  have h1 : x.1.toFinset = y.1.toFinset := by
    apply Finset.eq_of_subset_of_card_le h.1
    omega
  have h2 : x.2.1.toFinset = y.2.1.toFinset := by
    apply Finset.eq_of_subset_of_card_le h.2.1
    omega
  have h3 : x.2.2.1 = y.2.2.1 := by
    apply Finset.eq_of_subset_of_card_le h.2.2.1
    omega
  have h4 : x.2.2.2 = y.2.2.2 := by
    apply Finset.eq_of_subset_of_card_le h.2.2.2
    omega
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  rw [← Option.toFinset_inj] at h1 h2
  simp_all

/-!

## Powerset

-/

variable [DecidableEq 𝓩]

/-- The powerset of `x : Option 𝓩` defined as `{none}` if `x` is `none`
  and `{none, some y}` is `x` is `some y`. -/
def _root_.Option.powerset (x : Option 𝓩) : Finset (Option 𝓩) :=
  match x with
  | none => {none}
  | some x => {none, some x}

@[simp]
lemma _root_.Option.mem_powerset_iff {x : Option 𝓩} (y : Option 𝓩) :
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

/-- The powerset of a charge . Given a charge `x : Charges`
  it's powerset is the finite set of all `Charges` which are subsets of `x`. -/
def powerset (x : Charges 𝓩) : Finset (Charges 𝓩) :=
  x.1.powerset.product <| x.2.1.powerset.product <| x.2.2.1.powerset.product <| x.2.2.2.powerset

@[simp]
lemma mem_powerset_iff_subset {x y : Charges 𝓩} :
    x ∈ powerset y ↔ x ⊆ y := by
  cases x
  cases y
  simp only [powerset, Finset.product_eq_sprod]
  rw [Finset.mem_product]
  simp_all [Subset]

lemma self_mem_powerset (x : Charges 𝓩) :
    x ∈ powerset x := by simp

lemma empty_mem_powerset (x : Charges 𝓩) :
    ∅ ∈ powerset x := by simp

@[simp]
lemma powerset_of_empty :
    powerset (∅ : Charges 𝓩) = {∅} := by
  ext x
  simp

lemma powerset_mono {x y : Charges 𝓩} :
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

lemma min_exists_inductive (S : Finset (Charges 𝓩)) (hS : S ≠ ∅) :
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

lemma min_exists (S : Finset (Charges 𝓩)) (hS : S ≠ ∅) :
    ∃ y ∈ S, powerset y ∩ S = {y} := min_exists_inductive S hS S.card rfl

/-!

## ofFinset

-/

/-- Given `S5 S10 : Finset 𝓩` the finite set of charges associated with
  for which the 5-bar representation charges sit in `S5` and
  the 10d representation charges sit in `S10`. -/
def ofFinset (S5 S10 : Finset 𝓩) : Finset (Charges 𝓩) :=
  let SqHd := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SqHu := {none} ∪ S5.map ⟨Option.some, Option.some_injective 𝓩⟩
  let SQ5 := S5.powerset
  let SQ10 := S10.powerset
  SqHd.product (SqHu.product (SQ5.product SQ10))

lemma qHd_mem_ofFinset (S5 S10 : Finset 𝓩) (z : 𝓩) (x2 : Option 𝓩 × Finset 𝓩 × Finset 𝓩)
    (hsub : (some z, x2) ∈ ofFinset S5 S10) :
    z ∈ S5 := by
  rw [ofFinset] at hsub
  cases x2
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hsub
  dsimp only at hsub
  simp only [Finset.mem_powerset] at hsub
  simp_all

lemma qHu_mem_ofFinset (S5 S10 : Finset 𝓩) (z : 𝓩) (x1 : Option 𝓩) (x2 : Finset 𝓩 × Finset 𝓩)
    (hsub : (x1, some z, x2) ∈ ofFinset S5 S10) :
    z ∈ S5 := by
  rw [ofFinset] at hsub
  cases x2
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hsub
  dsimp only at hsub
  simp only [Finset.mem_powerset] at hsub
  simp_all

lemma mem_ofFinset_Q5_subset (S5 S10 : Finset 𝓩)
    {x : Charges 𝓩} (hx : x ∈ ofFinset S5 S10) :
    x.2.2.1 ⊆ S5 := by
  rw [ofFinset] at hx
  cases x
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hx
  dsimp only at hx
  simp only [Finset.mem_powerset] at hx
  exact hx.2.2.1

lemma mem_ofFinset_Q10_subset (S5 S10 : Finset 𝓩)
    {x : Charges 𝓩} (hx : x ∈ ofFinset S5 S10) :
    x.2.2.2 ⊆ S10 := by
  rw [ofFinset] at hx
  cases x
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hx
  dsimp only at hx
  simp only [Finset.mem_powerset] at hx
  exact hx.2.2.2

lemma mem_ofFinset_antitone (S5 S10 : Finset 𝓩)
    {x y : Charges 𝓩} (h : x ⊆ y) (hy : y ∈ ofFinset S5 S10) :
    x ∈ ofFinset S5 S10 := by
  have hoption (x : Option 𝓩) (S : Finset 𝓩) :
      x ∈ ({none} : Finset (Option 𝓩)) ∪ S.map ⟨Option.some, Option.some_injective 𝓩⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset] at hy ⊢
  cases x
  cases y
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hy
  repeat rw [Finset.product_eq_sprod, Finset.mem_product]
  dsimp only at hy ⊢
  rw [Subset] at h
  dsimp only [hasSubset] at h
  simp only [hoption, Finset.mem_powerset] at hy ⊢
  exact ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1, h.2.2.2.trans hy.2.2.2⟩

lemma mem_ofFinset_iff {S5 S10 : Finset 𝓩} {x : Charges 𝓩} :
    x ∈ ofFinset S5 S10 ↔ x.1.toFinset ⊆ S5 ∧ x.2.1.toFinset ⊆ S5 ∧
      x.2.2.1 ⊆ S5 ∧ x.2.2.2 ⊆ S10 := by
  match x with
  | (qHd, qHu, Q5, Q10) =>
  have hoption (x : Option 𝓩) (S : Finset 𝓩) :
      x ∈ ({none} : Finset (Option 𝓩)) ∪ S.map ⟨Option.some, Option.some_injective 𝓩⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset]
  repeat rw [Finset.product_eq_sprod, Finset.mem_product]
  rw [hoption, hoption]
  simp

lemma ofFinset_subset_of_subset {S5 S5' S10 S10' : Finset 𝓩}
    (h5 : S5 ⊆ S5') (h10 : S10 ⊆ S10') :
    ofFinset S5 S10 ⊆ ofFinset S5' S10' := by
  intro x hx
  rw [mem_ofFinset_iff] at hx ⊢
  exact ⟨hx.1.trans h5, hx.2.1.trans h5, hx.2.2.1.trans h5, hx.2.2.2.trans h10⟩

lemma ofFinset_univ [Fintype 𝓩] (x : Charges 𝓩) :
    x ∈ ofFinset (Finset.univ : Finset 𝓩) (Finset.univ : Finset 𝓩) := by
  rw [mem_ofFinset_iff]
  simp

end Charges

end SU5

end SuperSymmetry
