/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Basic
/-!

# Charges

One of the data structures associated with the F-theory SU(5)+U(1) GUT model
are the charges assocatied with the matter fields. In this module we define
the type `Charges`, the elements of which correspond to the collection of
charges associated with the matter content of a theory.

We relate this type to the charge profiles of the potential terms.

-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- The type such that an element corresponds to the collection of
  charges associated with the matter content of the theory.
  The order of charges is implicitly taken to be qHd, qHu, Q5, Q10 -/
def Charges : Type := Option ℤ × Option ℤ × Finset ℤ × Finset ℤ

namespace Charges

open PotentialTerm

instance : DecidableEq Charges := inferInstanceAs
  (DecidableEq (Option ℤ × Option ℤ × Finset ℤ × Finset ℤ))

/-!

## Subsest relation

-/

instance hasSubset : HasSubset Charges where
  Subset x y := x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧
    x.2.2.1 ⊆ y.2.2.1 ∧
    x.2.2.2 ⊆ y.2.2.2

instance subsetDecidable (x y : Charges) : Decidable (x ⊆ y) := instDecidableAnd

@[simp, refl]
lemma subset_refl (x : Charges) : x ⊆ x := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

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

## Powerset

-/


/-- The powerset of a charge . Given a charge `x : Charges`
  it's powerset is the finite set of all `Charges` which are subsets of `x`. -/
def powerset (x : Charges): Finset Charges :=
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

/-!

## Relationship to charge profiles

-/

/-- The collection of charges associated with a charge profile. -/
def fromChargeProfile : (T : PotentialTerm) → T.ChargeProfile → Charges
  | μ, (qHd, qHu) => (qHd, qHu, {}, {})
  | β, (qHu, Q5) => (none, qHu, Q5, {})
  | Λ, (Q5, Q10) => (none, none, Q5, Q10)
  | W1, (Q5, Q10) => (none, none, Q5, Q10)
  | W2, (qHd, Q10) => (qHd, none, {}, Q10)
  | W3, (qHu, Q5) => (none, qHu, Q5, {})
  | W4, (qHd, qHu, Q5) => (qHd, qHu, Q5, {})
  | K1, (Q5, Q10) => (none, none, Q5, Q10)
  | K2, (qHd, qHu, Q10) => (qHd, qHu, {}, Q10)
  | topYukawa, (qHu, Q10) => (qHu, none, {}, Q10)
  | bottomYukawa, (qHd, Q5, Q10) => (qHd, none, Q5, Q10)

/-- For a given potential term `T`, the charge profile associated with a collection of charges. -/
def toChargeProfile : (T : PotentialTerm) → Charges → T.ChargeProfile
  | μ, (qHd, qHu, _, _) => (qHd, qHu)
  | β, (_, qHu, Q5, _) => (qHu, Q5)
  | Λ, (_, _, Q5, Q10) => (Q5, Q10)
  | W1, (_, _, Q5, Q10) => (Q5, Q10)
  | W2, (qHd, _, _, Q10) => (qHd, Q10)
  | W3, (_, qHu, Q5, _) => (qHu, Q5)
  | W4, (qHd, qHu, Q5, _) => (qHd, qHu, Q5)
  | K1, (_, _, Q5, Q10) => (Q5, Q10)
  | K2, (qHd, qHu, _, Q10) => (qHd, qHu, Q10)
  | topYukawa, (qHu, _, _, Q10) => (qHu, Q10)
  | bottomYukawa, (qHd, _, Q5, Q10) => (qHd, Q5, Q10)

@[simp]
lemma fromChargeProfile_toChargeProfile (T : PotentialTerm) (cp : T.ChargeProfile) :
    toChargeProfile T (fromChargeProfile T cp) = cp := by
  cases T <;> rfl

lemma fromChargeProfile_injective (T : PotentialTerm) :
    Function.Injective (fromChargeProfile T) := by
  intro cp1 cp2 h
  have h' := congrArg (toChargeProfile T) h
  rw [fromChargeProfile_toChargeProfile, fromChargeProfile_toChargeProfile] at h'
  exact h'

lemma toChargeProfile_surjective (T : PotentialTerm) :
    Function.Surjective (toChargeProfile T) := by
  intro cp
  use fromChargeProfile T cp
  rw [fromChargeProfile_toChargeProfile]

@[simp]
lemma toChargeProfile_empty (T : PotentialTerm) :
    toChargeProfile T ∅ = ∅ := by
  cases T <;> rfl

@[simp]
lemma fromChargeProfile_empty (T : PotentialTerm) :
    fromChargeProfile T ∅ = ∅ := by
  cases T <;> rfl

lemma toChargeProfile_subset_of_subset (T : PotentialTerm) {x y : Charges} (h : x ⊆ y) :
    toChargeProfile T x ⊆ toChargeProfile T y := by
  rcases x with ⟨x1, x2, x3, x4⟩
  rcases y with ⟨y1, y2, y3, y4⟩
  rw [Subset] at h
  dsimp [hasSubset] at h
  fin_cases T
  all_goals
    rw [Subset]
    dsimp [ChargeProfile.instHasSubset, toChargeProfile]
    simp_all

lemma fromChargeProfile_subset_of_subset {T : PotentialTerm} {x y : T.ChargeProfile} (h : x ⊆ y) :
    fromChargeProfile T x ⊆ fromChargeProfile T y := by
  rw [Subset]
  dsimp [hasSubset, fromChargeProfile]
  fin_cases T
  all_goals
    cases x
    cases y
    rw [Subset] at h
    dsimp [ChargeProfile.instHasSubset] at h
    simp_all

@[simp]
lemma fromChargeProfile_subset_iff_subset {T : PotentialTerm} {x y : T.ChargeProfile} :
    fromChargeProfile T x ⊆ fromChargeProfile T y ↔ x ⊆ y := by
  constructor
  · intro h
    simpa using toChargeProfile_subset_of_subset T h
  · exact fun h => fromChargeProfile_subset_of_subset h

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
  exact ⟨h.1.trans hy.1, h.2.1.trans hy.2.1, h.2.2.1.trans hy.2.2.1,  h.2.2.2.trans hy.2.2.2⟩

lemma toChargeProfile_mem_ofFinset_of_mem_ofFinset (T : PotentialTerm)
    {x : Charges} (S5 S10 : Finset ℤ) (hx : x ∈ ofFinset S5 S10) :
    toChargeProfile T x ∈ ChargeProfile.ofFinset T S5 S10 := by
  have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
    match x with
    | none => simp
    | some x => simp
  rw [ofFinset] at hx
  cases x
  repeat rw [Finset.product_eq_sprod, Finset.mem_product] at hx
  dsimp at hx
  simp only [hoption, Finset.mem_powerset] at hx
  fin_cases T
  all_goals
    rw [ChargeProfile.ofFinset, toChargeProfile]
    repeat rw [Finset.product_eq_sprod, Finset.mem_product]
    dsimp only
    simp only [hoption, Finset.mem_powerset]
    aesop

@[simp]
lemma fromChargeProfile_mem_ofFinset_iff_mem_ofFinset {T : PotentialTerm}
    {x : T.ChargeProfile} (S5 S10 : Finset ℤ) :
    fromChargeProfile T x ∈ ofFinset S5 S10 ↔ x ∈ ChargeProfile.ofFinset T S5 S10 := by
  constructor
  · intro h
    simpa using toChargeProfile_mem_ofFinset_of_mem_ofFinset T S5 S10 h
  · intro h
    have hoption (x : Option ℤ) (S : Finset ℤ) :
      x ∈ ({none} : Finset (Option ℤ)) ∪ S.map ⟨Option.some, Option.some_injective ℤ⟩ ↔
      x.toFinset ⊆ S := by
      match x with
      | none => simp
      | some x => simp
    fin_cases T
    all_goals
      cases x
      dsimp [fromChargeProfile, ofFinset]
      repeat rw [Finset.mem_product]
      dsimp only
      simp only [hoption, Finset.mem_powerset]
      rw [ChargeProfile.ofFinset] at h
      repeat rw [Finset.product_eq_sprod, Finset.mem_product] at h
      dsimp only at h
      simp only [hoption, Finset.mem_powerset] at h
      aesop

end Charges

end SU5U1

end FTheory
