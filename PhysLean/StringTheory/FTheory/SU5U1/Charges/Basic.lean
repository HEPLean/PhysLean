/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfRationalSection
/-!

# Charges

One of the data structures associated with the F-theory SU(5)+U(1) GUT model
are the charges assocatied with the matter fields. In this module we define
the type `Charges`, the elements of which correspond to the collection of
charges associated with the matter content of a theory.

-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- The type such that an element corresponds to the collection of
  charges associated with the matter content of the theory.
  The order of charges is implicitly taken to be qHd, qHu, Q5, Q10 -/
def Charges : Type := Option ℤ × Option ℤ × Finset ℤ × Finset ℤ

namespace Charges

instance : DecidableEq Charges := inferInstanceAs
  (DecidableEq (Option ℤ × Option ℤ × Finset ℤ × Finset ℤ))

unsafe instance : Repr Charges where
  reprPrec x _ := match x with
    | (qHd, qHu, Q5, Q10) =>
      let s1 := reprStr qHd
      let s2 := reprStr qHu
      let s5 := reprStr Q5
      let s10 := reprStr Q10
      s!"({s1}, {s2}, {s5}, {s10})"

/-- The explicit casting of a term of `Charges` to a term of
  `Option ℤ × Option ℤ × Finset ℤ × Finset ℤ`. -/
def toProd (x : Charges) : Option ℤ × Option ℤ × Finset ℤ × Finset ℤ := x

lemma eq_of_parts {x y : Charges} (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1)
    (h3 : x.2.2.1 = y.2.2.1) (h4 : x.2.2.2 = y.2.2.2) : x = y := by
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
    simp_all


/-!

## Subsest relation

-/

instance hasSubset : HasSubset Charges where
  Subset x y := x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧
    x.2.2.1 ⊆ y.2.2.1 ∧
    x.2.2.2 ⊆ y.2.2.2

instance hasSSubset : HasSSubset Charges where
  SSubset x y := x ⊆ y ∧ x ≠ y

instance subsetDecidable (x y : Charges) : Decidable (x ⊆ y) := instDecidableAnd

lemma subset_def {x y : Charges} : x ⊆ y ↔ x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧ x.2.2.1 ⊆ y.2.2.1 ∧ x.2.2.2 ⊆ y.2.2.2 := by
  rfl

@[simp, refl]
lemma subset_refl (x : Charges) : x ⊆ x := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

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


lemma subset_trans {x y z : Charges} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := by
  simp_all [Subset]

lemma subset_antisymm {x y : Charges} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
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

instance emptyInst : EmptyCollection Charges where
  emptyCollection := (none, none, {}, {})

@[simp]
lemma empty_subset (x : Charges) : ∅ ⊆ x := by
  simp [hasSubset, Subset, emptyInst]

@[simp]
lemma subset_of_empty_iff_empty {x : Charges} :
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

## Card

-/

/-- The cardinality of a `Charges` is defined to be the sum of the cardinalities
  of each of the underlying finite sets of charges, with `Option ℤ` turned to finsets. -/
def card (x : Charges) : Nat :=
  x.1.toFinset.card + x.2.1.toFinset.card + x.2.2.1.card + x.2.2.2.card

@[simp]
lemma card_empty : card (∅ : Charges) = 0 := by
  simp [card, emptyInst]

lemma card_subset_le {x y : Charges} (h : x ⊆ y) : card x ≤ card y := by
  simp [card, hasSubset] at h
  have h1 := Finset.card_le_card h.1
  have h2 := Finset.card_le_card h.2.1
  have h3 := Finset.card_le_card h.2.2.1
  have h4 := Finset.card_le_card h.2.2.2
  simp [card]
  omega

lemma eq_of_subset_card {x y : Charges} (h : x ⊆ y) (hcard : card x = card y) : x = y := by
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

/-- The powerset of a charge . Given a charge `x : Charges`
  it's powerset is the finite set of all `Charges` which are subsets of `x`. -/
def powerset (x : Charges) : Finset Charges :=
  x.1.powerset.product <| x.2.1.powerset.product <| x.2.2.1.powerset.product <| x.2.2.2.powerset

@[simp]
lemma mem_powerset_iff_subset {x y : Charges} :
    x ∈ powerset y ↔ x ⊆ y := by
  cases x
  cases y
  simp only [powerset, Finset.product_eq_sprod]
  rw [Finset.mem_product]
  simp_all [Subset]

lemma self_mem_powerset (x : Charges) :
    x ∈ powerset x := by simp

lemma empty_mem_powerset (x : Charges) :
    ∅ ∈ powerset x := by simp

@[simp]
lemma powerset_of_empty :
    powerset ∅ = {∅} := by
  ext x
  simp

lemma powerset_subset_iff_subset {x y : Charges} :
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


lemma min_exists_inductive (S : Finset Charges) (hS : S ≠ ∅) :
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

lemma min_exists (S : Finset Charges) (hS : S ≠ ∅) :
    ∃ y ∈ S, powerset y ∩ S = {y} := min_exists_inductive S hS S.card rfl

/-!

## ofFinset

-/

/-- Given `S5 S10 : Finset ℤ` the finite set of charges associated with
  for which the 5-bar representation charges sit in `S5` and
  the 10d representation charges sit in `S10`. -/
def ofFinset (S5 S10 : Finset ℤ) : Finset Charges :=
  let SqHd := {none} ∪ S5.map ⟨Option.some, Option.some_injective ℤ⟩
  let SqHu := {none} ∪ S5.map ⟨Option.some, Option.some_injective ℤ⟩
  let SQ5 := S5.powerset
  let SQ10 := S10.powerset
  SqHd.product (SqHu.product (SQ5.product SQ10))

lemma qHd_mem_ofFinset (S5 S10 : Finset ℤ) (z : ℤ) (x2 : Option ℤ × Finset ℤ × Finset ℤ)
    (hsub : (some z, x2) ∈ ofFinset S5 S10) :
    z ∈ S5 := by
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset] at hsub
  cases x2
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hsub
  dsimp only at hsub
  simp only [Finset.mem_powerset] at hsub
  simp_all

lemma qHu_mem_ofFinset (S5 S10 : Finset ℤ) (z : ℤ) (x1 : Option ℤ) (x2 : Finset ℤ × Finset ℤ)
    (hsub : (x1, some z, x2) ∈ ofFinset S5 S10) :
    z ∈ S5 := by
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset] at hsub
  cases x2
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hsub
  dsimp only at hsub
  simp only [Finset.mem_powerset] at hsub
  simp_all

lemma mem_ofFinset_Q5_subset (S5 S10 : Finset ℤ)
    {x : Charges} (hx : x ∈ ofFinset S5 S10) :
    x.2.2.1 ⊆ S5 := by
  rw [ofFinset] at hx
  cases x
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hx
  dsimp only at hx
  simp only [Finset.mem_powerset] at hx
  exact hx.2.2.1

lemma mem_ofFinset_Q10_subset (S5 S10 : Finset ℤ)
    {x : Charges} (hx : x ∈ ofFinset S5 S10) :
    x.2.2.2 ⊆ S10 := by
  rw [ofFinset] at hx
  cases x
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hx
  dsimp only at hx
  simp only [Finset.mem_powerset] at hx
  exact hx.2.2.2

lemma mem_ofFinset_of_subset (S5 S10 : Finset ℤ)
    {x y : Charges} (h : x ⊆ y) (hy : y ∈ ofFinset S5 S10) :
    x ∈ ofFinset S5 S10 := by
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
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

lemma mem_ofFinset_iff {S5 S10 : Finset ℤ} {x : Charges} :
    x ∈ ofFinset S5 S10 ↔ x.1.toFinset ⊆ S5 ∧ x.2.1.toFinset ⊆ S5 ∧
      x.2.2.1 ⊆ S5 ∧ x.2.2.2 ⊆ S10 := by
  match x with
  | (qHd, qHu, Q5, Q10) =>
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset]
  repeat rw [Finset.product_eq_sprod, Finset.mem_product]
  rw [hoption, hoption]
  simp

/-!

## Minimal super set

-/

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimimal charges `y` in `ofFinset S5 S10` which are a super sets of `x`. -/
def minimalSuperSet (S5 S10 : Finset ℤ) (x : Charges) : Finset Charges :=
  let SqHd := if x.1.isSome then ∅ else S5.val.map fun y => (some y, x.2)
  let SqHu := if x.2.1.isSome then ∅ else S5.val.map fun y => (x.1, some y, x.2.2)
  let SQ5 := S5.val.map (fun y => (x.1, x.2.1, insert y x.2.2.1, x.2.2.2))
  let SQ10 := S10.val.map (fun y => (x.1, x.2.1, x.2.2.1, insert y x.2.2.2))
  (SqHd ∪ SqHu ∪ SQ5 ∪ SQ10).toFinset.erase x

lemma self_subset_mem_minimalSuperSet (S5 S10 : Finset ℤ) (x y : Charges)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ⊆ y := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | (none, _, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | (some x1, _, _, _) =>
      simp at hr
  · match x with
    | (_, none, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
    | (_, some x2, _, _) =>
      simp at hr
  · match x with
    | (_, _, Q5, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]
  · match x with
    | (_, _, _, Q10) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rw [Subset]
      simp [hasSubset]

@[simp]
lemma self_not_mem_minimalSuperSet (S5 S10 : Finset ℤ) (x : Charges) :
    x ∉ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]

lemma self_neq_mem_minimalSuperSet (S5 S10 : Finset ℤ) (x y : Charges)
    (hy : y ∈ minimalSuperSet S5 S10 x) : x ≠ y := by
  by_contra h
  subst h
  simp at hy

lemma card_of_mem_minimalSuperSet {S5 S10 : Finset ℤ} {x : Charges}
    (y : Charges) (hy : y ∈ minimalSuperSet S5 S10 x) :
    card y = card x + 1 := by
  simp [minimalSuperSet] at hy
  rcases hy with ⟨hy1, hr | hr | hr | hr⟩
  · match x with
    | (none, _, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | (some x1, _, _, _) =>
      simp at hr
  · match x with
    | (_, none, _, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      omega
    | (_, some x2, _, _) =>
      simp at hr
  · match x with
    | (_, _, Q5, _) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1
  · match x with
    | (_, _, _, Q10) =>
      simp at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [card]
      rw [Finset.card_insert_of_notMem]
      omega
      by_contra h
      rw [Finset.insert_eq_of_mem h] at hy1
      simp at hy1

lemma insert_Q5_mem_minimalSuperSet {S5 S10 : Finset ℤ} {x : Charges}
    (z : ℤ) (hz : z ∈ S5) (hznot : z ∉ x.2.2.1) :
    (x.1, x.2.1, insert z x.2.2.1, x.2.2.2) ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | (qHd, qHu, Q5, Q10) =>
  apply And.intro
  · simpa using hznot
  · right
    right
    left
    use z

lemma insert_Q10_mem_minimalSuperSet {S5 S10 : Finset ℤ} {x : Charges}
    (z : ℤ) (hz : z ∈ S10) (hznot : z ∉ x.2.2.2) :
    (x.1, x.2.1, x.2.2.1, insert z x.2.2.2) ∈ minimalSuperSet S5 S10 x := by
  simp [minimalSuperSet]
  match x with
  | (qHd, qHu, Q5, Q10) =>
  apply And.intro
  · simpa using hznot
  · right
    right
    right
    use z

lemma some_qHd_mem_minimalSuperSet_of_none {S5 S10 : Finset ℤ} {x2 : Option ℤ × Finset ℤ × Finset ℤ}
    (z : ℤ) (hz : z ∈ S5) :
    (some z, x2) ∈ minimalSuperSet S5 S10 (none, x2) := by
  simp_all [minimalSuperSet]

lemma some_qHu_mem_minimalSuperSet_of_none {S5 S10 : Finset ℤ}
    {x1 : Option ℤ} {x2 : Finset ℤ × Finset ℤ} (z : ℤ) (hz : z ∈ S5) :
    (x1, some z, x2) ∈ minimalSuperSet S5 S10 (x1, none, x2) := by
  simp_all [minimalSuperSet]

lemma exists_minimalSuperSet (S5 S10 : Finset ℤ) {x y : Charges}
    (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y)
    (hxneqy : x ≠ y) : ∃ z ∈ minimalSuperSet S5 S10 x, z ⊆ y := by
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  simp [Prod.ext_iff] at hxneqy
  repeat rw [Prod.ext_iff] at hxneqy
  by_cases h3 : x3 ≠ y3
  · have h3Strict : x3 ⊂ y3 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h3Strict
    obtain ⟨z3, hz3, h3⟩ := h3Strict
    use (x1, x2, insert z3 x3, x4)
    constructor
    · apply insert_Q5_mem_minimalSuperSet
      · apply mem_ofFinset_Q5_subset S5 S10 hy
        simp only
        exact hz3
      · exact h3
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h3
  subst h3
  by_cases h4 : x4 ≠ y4
  · have h4Strict : x4 ⊂ y4 := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      simp_all
    rw [Finset.ssubset_iff_of_subset (by simp_all)] at h4Strict
    obtain ⟨z4, hz4, h4⟩ := h4Strict
    use (x1, x2, x3, insert z4 x4)
    constructor
    · apply insert_Q10_mem_minimalSuperSet
      · apply mem_ofFinset_Q10_subset S5 S10 hy
        simp only
        exact hz4
      · exact h4
    · rw [Subset]
      dsimp [hasSubset]
      simp_all
      rw [@Finset.insert_subset_iff]
      simp_all
  simp at h4
  subst h4
  simp_all
  match x1, y1, x2, y2 with
  | some x1, none, x2, y2 =>
    simp at hsubset
  | none, some y1, x2, y2 =>
    simp at hsubset
    use (some y1, x2, x3, x4)
    constructor
    · apply some_qHd_mem_minimalSuperSet_of_none
      exact qHd_mem_ofFinset S5 S10 _ _ hy
    · simp_all [hasSubset]
  | x1, y1, some x2, none =>
    simp at hsubset
  | x1, y1, none, some y2 =>
    simp at hsubset
    use (x1, some y2, x3, x4)
    constructor
    · apply some_qHu_mem_minimalSuperSet_of_none
      exact qHu_mem_ofFinset S5 S10 _ _ _ hy
    · simp_all [hasSubset]
  | none, none, none, none =>
    simp_all
  | some x1, some y1, none, none =>
    simp_all
  | none, none, some x2, some y2 =>
    simp_all
  | some x1, some y1, some x2, some y2 =>
    simp_all

lemma minimalSuperSet_induction_on_inductive {S5 S10 : Finset ℤ}
    (p : Charges → Prop) (hp : (x : Charges) → p x → ∀ y ∈ minimalSuperSet S5 S10 x, p y)
    (x : Charges) (hbase : p x)
    (y : Charges) (hy : y ∈ ofFinset S5 S10) (hsubset : x ⊆ y) :
    (n : ℕ) → (hn : n = y.card - x.card) → p y
  | 0, hn => by
    have hxy : x = y := by
      refine eq_of_subset_card hsubset ?_
      have hl : card x ≤ card y := card_subset_le hsubset
      omega
    subst hxy
    simp_all
  | Nat.succ n, hn => by
    have hxy : x ≠ y := by
      intro h
      subst h
      simp at hn
    obtain ⟨z, hz, hsubsetz⟩ := exists_minimalSuperSet S5 S10 hy hsubset hxy
    refine minimalSuperSet_induction_on_inductive p hp z ?_ y hy ?_ n ?_
    · exact hp x hbase z hz
    · exact hsubsetz
    · rw [card_of_mem_minimalSuperSet z hz]
      omega

/-!

## Completions

-/

/-- A collection of charges is complete if it has all types of fields. -/
def IsComplete (x : Charges) : Prop :=
  x.1.isSome ∧ x.2.1.isSome ∧ x.2.2.1 ≠ ∅ ∧ x.2.2.2 ≠ ∅

instance (x : Charges) : Decidable (IsComplete x) :=
  inferInstanceAs (Decidable (x.1.isSome ∧ x.2.1.isSome ∧ x.2.2.1 ≠ ∅ ∧ x.2.2.2 ≠ ∅))

/-- Given a collection of charges `x` in `ofFinset S5 S10`,
  the minimimal charges `y` in `ofFinset S5 S10` which are a super sets of `x` and are
  complete. -/
def completions (S5 S10 : Finset ℤ) (x : Charges) : Multiset Charges :=
  let SqHd := if x.1.isSome then {x.1} else S5.val.map fun y => some y
  let SqHu := if x.2.1.isSome then {x.2.1} else S5.val.map fun y => some y
  let SQ5 := if x.2.2.1 ≠ ∅ then {x.2.2.1} else S5.val.map fun y => {y}
  let SQ10 := if x.2.2.2 ≠ ∅ then {x.2.2.2} else S10.val.map fun y => {y}
  (SqHd.product (SqHu.product (SQ5.product SQ10)))

lemma completions_eq_singleton_of_complete {S5 S10 : Finset ℤ} (x : Charges)
    (hcomplete : IsComplete x) :
    completions S5 S10 x = {x} := by
  simp [completions]
  simp [IsComplete] at hcomplete
  by_cases h1 : x.1.isSome
  case' neg => simp_all
  by_cases h2 : x.2.1.isSome
  case' neg => simp_all
  by_cases h3 : x.2.2.1 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.2.2.2 ≠ ∅
  case' neg => simp_all
  simp_all
  rfl

@[simp]
lemma self_mem_completions_iff_isComplete {S5 S10 : Finset ℤ} (x : Charges) :
    x ∈ completions S5 S10 x ↔ IsComplete x := by
  simp [completions, IsComplete]
  repeat rw [Multiset.mem_product]
  by_cases h1 : x.1.isSome
  case' neg => simp_all
  by_cases h2 : x.2.1.isSome
  case' neg => simp_all
  by_cases h3 : x.2.2.1 ≠ ∅
  case' neg => simp_all
  by_cases h4 : x.2.2.2 ≠ ∅
  case' neg => simp_all
  simp_all

lemma mem_completions_isComplete {S5 S10 : Finset ℤ} {x y : Charges}
    (hx : y ∈ completions S5 S10 x) : IsComplete y := by
  match y with
  | (qHd, qHu, Q5, Q10) =>
  simp [completions] at hx
  repeat rw [Multiset.mem_product] at hx
  simp at hx
  match x with
  | (x1, x2, x3, x4) =>
  simp_all
  rw [IsComplete]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
    by_cases hs : x1.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.1
      simp
  · simp
    by_cases hs : x2.isSome
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.1
      simp
  · simp
    by_cases hs : x3 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.1
      simp
  · simp
    by_cases hs : x4 ≠ ∅
    · simp_all
    · simp_all
      obtain ⟨a, h, rfl⟩ := hx.2.2.2
      simp

lemma self_subset_mem_completions (S5 S10 : Finset ℤ) (x y : Charges)
    (hy : y ∈ completions S5 S10 x) : x ⊆ y := by
  simp [completions] at hy
  repeat rw [Multiset.mem_product] at hy
  rw [Subset]
  dsimp [hasSubset]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : x.1.isSome
    · simp_all
    · simp_all
  · by_cases h : x.2.1.isSome
    · simp_all
    · simp_all
  · by_cases h : x.2.2.1 ≠ ∅
    · simp_all
    · simp_all
  · by_cases h : x.2.2.2 ≠ ∅
    · simp_all
    · simp_all

lemma exist_completions_subset_of_complete (S5 S10 : Finset ℤ) (x y : Charges)
    (hsubset : x ⊆ y) (hy : y ∈ ofFinset S5 S10) (hycomplete : IsComplete y) :
    ∃ z ∈ completions S5 S10 x, z ⊆ y := by
  by_cases hx : IsComplete x
  · use x
    simp_all
  rw [Subset] at hsubset
  dsimp [hasSubset] at hsubset
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  simp [IsComplete] at hycomplete
  rw [Option.isSome_iff_exists, Option.isSome_iff_exists] at hycomplete
  obtain ⟨y1, rfl⟩ := hycomplete.1
  obtain ⟨y2, rfl⟩ := hycomplete.2.1
  rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem] at hycomplete
  simp at hycomplete
  obtain ⟨z3, hz3⟩ := hycomplete.1
  obtain ⟨z4, hz4⟩ := hycomplete.2
  have hz3Mem : z3 ∈ S5 := by
    apply mem_ofFinset_Q5_subset S5 S10 hy
    simp_all
  have hz4Mem : z4 ∈ S10 := by
    apply mem_ofFinset_Q10_subset S5 S10 hy
    simp_all
  have hy1' : some y1 ∈ if x1.isSome = true then {x1} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h1 : x1.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h1
      obtain ⟨a, rfl⟩ := h1
      simp_all
    · simp_all
      exact qHd_mem_ofFinset S5 S10 y1 (some y2, y3, y4) hy
  have hy2' : some y2 ∈ if x2.isSome = true then {x2} else
      Multiset.map (fun y => some y) S5.val := by
    by_cases h2 : x2.isSome
    · simp_all
      rw [Option.isSome_iff_exists] at h2
      obtain ⟨a, rfl⟩ := h2
      simp_all
    · simp_all
      exact qHu_mem_ofFinset S5 S10 y2 (some y1) (y3, y4) hy
  simp_all
  by_cases h3 : x3 ≠ ∅
  · by_cases h4 : x4 ≠ ∅
    · use (y1, y2, x3, x4)
      constructor
      · simp_all [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use (y1, y2, x3, {z4})
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
  · simp at h3
    subst h3
    by_cases h4 : x4 ≠ ∅
    · use (y1, y2, {z3}, x4)
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all
    · simp at h4
      subst h4
      use (y1, y2, {z3}, {z4})
      constructor
      · simp [completions]
        repeat rw [Multiset.mem_product]
        simp_all
      · rw [Subset]
        dsimp [hasSubset]
        simp_all

end Charges

end SU5U1

end FTheory
