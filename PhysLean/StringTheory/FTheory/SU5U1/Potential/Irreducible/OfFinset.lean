/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Irreducible.Basic

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges

/-!

## Auxillary results: Multisets from Finsets of given cardinality.

-/

/-- The multisets of cardinality `1` containing elements from a finite set `s`. -/
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

/-- The multisets of cardinality `2` containing elements from a finite set `s`. -/
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

/-- The multisets of cardinality `3` containing elements from a finite set `s`. -/
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
        simp only [and_true]
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

open PotentialTerm


def irreducibleOfFinset (S5 S10 : Finset ℤ) : (T : PotentialTerm) → Multiset Charges
  | μ =>
    let SqHd := S5.val
    let SqHu := S5.val
    let prod := SqHd.product (SqHu)
    let Filt := prod.filter (fun x => - x.1 + x.2 = 0)
    (Filt.map (fun x => (x.1, x.2, ∅, ∅)))
  | K2 =>
    let SqHd := S5.val
    let SqHu := S5.val
    let Q10 := toMultisetsOne S10
    let prod := SqHd.product (SqHu.product Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.1, ∅, x.2.2.toFinset)))
  | K1 =>
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsTwo S10
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => - x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (none, none, x.1.toFinset, x.2.toFinset)))
  | W4 =>
    let SqHd := S5.val
    let SqHu := S5.val
    let Q5 := toMultisetsOne S5
    let prod := SqHd.product (SqHu.product Q5)
    let Filt := prod.filter (fun x => x.1 - 2 * x.2.1 + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, x.2.1, x.2.2.toFinset, ∅)))
  | W3 =>
    let SqHu := S5.val
    let Q5 := toMultisetsTwo S5
    let prod := SqHu.product Q5
    let Filt := prod.filter (fun x => - 2 * x.1 + x.2.sum = 0)
    (Filt.map (fun x => (none, x.1, x.2.toFinset, ∅)))
  | W2 =>
    let SqHd := S5.val
    let Q10 := toMultisetsThree S10
    let prod := SqHd.product Q10
    let Filt := prod.filter (fun x => x.1 + x.2.sum = 0)
    (Filt.map (fun x => (x.1, none, ∅, x.2.toFinset))).filter fun x => IsIrreducible x W2
  | W1 =>
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsThree S10
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (none, none, x.1.toFinset, x.2.toFinset))).filter fun x => IsIrreducible x W1
  | Λ =>
    let Q5 := toMultisetsTwo S5
    let Q10 := toMultisetsOne S10
    let Prod := Q5.product Q10
    let Filt := Prod.filter (fun x => x.1.sum + x.2.sum = 0)
    (Filt.map (fun x => (none, none, x.1.toFinset, x.2.toFinset)))
  | β =>
    let SqHu := S5.val
    let Q5 := toMultisetsOne S5
    let prod := SqHu.product Q5
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => (none, x.1, x.2.toFinset, ∅)))
  | topYukawa =>
    let SqHu := S5.val
    let Q10 := toMultisetsTwo S10
    let prod := SqHu.product Q10
    let Filt := prod.filter (fun x => - x.1 + x.2.sum = 0)
    (Filt.map (fun x => (none, x.1, ∅, x.2.toFinset)))
  | bottomYukawa =>
    let SqHd := S5.val
    let Q5 := toMultisetsOne S5
    let Q10 := toMultisetsOne S10
    let prod := SqHd.product (Q5.product Q10)
    let Filt := prod.filter (fun x => x.1 + x.2.1.sum + x.2.2.sum = 0)
    (Filt.map (fun x => (x.1, none,x.2.1.toFinset, x.2.2.toFinset)))

lemma eq_allowsTermForm_of_mem_irreducibleOfFinset {S5 S10 : Finset ℤ} {T : PotentialTerm}
    {x : Charges} (hx : x ∈ irreducibleOfFinset S5 S10 T) :
    ∃ a b c, x = allowsTermForm a b c T := by
  cases T
  all_goals
    simp [irreducibleOfFinset] at hx
  case' W1 | W2 => have hx := hx.1
  case' μ | β | W1 | W2 | W3 | K1 | topYukawa | Λ => obtain ⟨a, b, h, rfl⟩ :=  hx
  case' bottomYukawa | K2 | W4 => obtain ⟨a, b, c, h, rfl⟩ := hx
  all_goals
    try rw [Multiset.card_eq_one] at h
    try rw [Multiset.card_eq_two] at h
    try rw [Multiset.card_eq_three] at h
  case' W1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, q103, rfl⟩ := h.1.2.2
  case' W2 =>
    obtain ⟨q101, q102, q103, rfl⟩  := h.1.2.2
  case' W3 =>
    obtain ⟨q51, q52, rfl⟩ := h.1.2.2
  case' W4 =>
    obtain ⟨q51, rfl⟩ := h.1.2.2.2
  case' K1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' K2 =>
    obtain ⟨q101, rfl⟩ := h.1.2.2.2
  case' topYukawa =>
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' bottomYukawa =>
    obtain ⟨q51, rfl⟩ := h.1.2.1.2
    rw [Multiset.card_eq_one] at h
    obtain ⟨q101, rfl⟩  := h.1.2.2.2
  case' Λ =>
    obtain ⟨q101, rfl⟩ := h.1.2.2
    obtain ⟨q51, q52, rfl⟩ := h.1.1.2
  case' β =>
    obtain ⟨q51, rfl⟩ := h.1.2.2
  all_goals
    simp [allowsTermForm]
  case' bottomYukawa => use a, q51
  case' K2 => use a, b
  case' K1 => use -q51, q101
  case' W1 => use q101, q102, q103
  case' W2 => use q101, q102, q103
  case' W3 => use (-a), q51
  case' W4 => use - b, q51
  case' Λ => use q51, q52
  case' β => use a
  case' topYukawa => use -a, q101
  case' μ => use a
  all_goals
    apply eq_of_parts
    any_goals rfl
  all_goals
    simp_all
    try omega
  all_goals
    congr 2
    omega

lemma allowsTerm_of_mem_irreducibleOfFinset {S5 S10 : Finset ℤ} {T : PotentialTerm}
    {x : Charges} (hx : x ∈ irreducibleOfFinset S5 S10 T) :
    x.AllowsTerm T := by
  obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_mem_irreducibleOfFinset hx
  exact allowsTermForm_allowsTerm

lemma mem_irreducibleOfFinset_of_irreducible {S5 S10  : Finset ℤ } {T : PotentialTerm}
    (x : Charges) (h : x.IsIrreducible T) (hx : x ∈ ofFinset S5 S10) :
    x ∈ irreducibleOfFinset S5 S10 T := by
  obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_isIrreducible h
  cases T
  all_goals
    simp [allowsTermForm, irreducibleOfFinset]
    rw [mem_ofFinset_iff] at hx
  case' μ =>
    use a, a
    simp_all [allowsTermForm]
  case' β =>
    use a, {a}
    simp_all [allowsTermForm]
  case' Λ =>
    use {a, b}, {- a - b}
    simp_all [allowsTermForm]
  case' W1 =>
    apply And.intro
    · use {- a - b - c}, {a, b, c}
      simp_all [allowsTermForm]
      omega
    · exact h
  case' W2 =>
    apply And.intro
    · use (- a - b - c), {a, b, c}
      simp_all [allowsTermForm]
      omega
    · exact h
  case' W3 =>
    use (-a), {b, - b - 2 * a}
    simp_all [allowsTermForm]
    omega
  case' W4 =>
    use (- c - 2 * b), (-b), {c}
    simp_all [allowsTermForm]
    omega
  case' K1 =>
    use {-a}, {b, - a - b}
    simp_all [allowsTermForm]
  case' K2 =>
    use a, b, {- a - b}
    simp_all [allowsTermForm]
  case' topYukawa =>
    use (-a), {b, - a - b}
    simp_all [allowsTermForm]
  case' bottomYukawa =>
    use a, {b}, {- a - b}
    simp_all [allowsTermForm]

lemma isIrreducible_of_mem_irreducibleOfFinset {S5 S10 : Finset ℤ} {T : PotentialTerm}
    {x : Charges} (hx : x ∈ irreducibleOfFinset S5 S10 T) :
    x.IsIrreducible T := by
  by_cases hT : T ≠  W1 ∧ T ≠ W2
  · obtain ⟨a, b, c, rfl⟩ := eq_allowsTermForm_of_mem_irreducibleOfFinset hx
    exact allowsTermForm_isIrreducible hT
  · simp at hT
    by_cases h : T = W1
    · subst h
      simp [irreducibleOfFinset] at hx
      exact hx.2
    · simp_all
      subst hT
      simp [irreducibleOfFinset] at hx
      exact hx.2

lemma ofFinset_of_mem_irreducibleOfFinset {S5 S10 : Finset ℤ} {T : PotentialTerm}
    {x : Charges} (hx : x ∈ irreducibleOfFinset S5 S10 T) :
    x ∈ ofFinset S5 S10 := by
  cases T
  all_goals
    simp [irreducibleOfFinset] at hx
  case' W1 | W2 => have hx := hx.1
  case' μ | β | W1 | W2 | W3 | K1 | topYukawa | Λ => obtain ⟨a, b, h, rfl⟩ :=  hx
  case' bottomYukawa | K2 | W4 => obtain ⟨a, b, c, h, rfl⟩ := hx
  all_goals
    try rw [Multiset.card_eq_one] at h
    try rw [Multiset.card_eq_two] at h
    try rw [Multiset.card_eq_three] at h
  case' W1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, q103, rfl⟩ := h.1.2.2
  case' W2 =>
    obtain ⟨q101, q102, q103, rfl⟩  := h.1.2.2
  case' W3 =>
    obtain ⟨q51, q52, rfl⟩ := h.1.2.2
  case' W4 =>
    obtain ⟨q51, rfl⟩ := h.1.2.2.2
  case' K1 =>
    obtain ⟨q51, rfl⟩ := h.1.1.2
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' K2 =>
    obtain ⟨q101, rfl⟩ := h.1.2.2.2
  case' topYukawa =>
    obtain ⟨q101, q102, rfl⟩ := h.1.2.2
  case' bottomYukawa =>
    obtain ⟨q51, rfl⟩ := h.1.2.1.2
    rw [Multiset.card_eq_one] at h
    obtain ⟨q101, rfl⟩  := h.1.2.2.2
  case' Λ =>
    obtain ⟨q101, rfl⟩ := h.1.2.2
    obtain ⟨q51, q52, rfl⟩ := h.1.1.2
  case' β =>
    obtain ⟨q51, rfl⟩ := h.1.2.2
  all_goals
    rw [mem_ofFinset_iff]
    simp_all

lemma isIrreducible_iff_mem_irreducibleOfFinset {S5 S10 : Finset ℤ} {T : PotentialTerm}
    {x : Charges} (hx : x ∈ ofFinset S5 S10) :
    x.IsIrreducible T ↔ x ∈ irreducibleOfFinset S5 S10 T := by
  constructor
  · intro h
    exact mem_irreducibleOfFinset_of_irreducible x h hx
  · intro h
    exact isIrreducible_of_mem_irreducibleOfFinset h


end Charges


end SU5U1

end FTheory
