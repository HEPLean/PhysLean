/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Charges associated with a potential term

-/

namespace FTheory
namespace SU5U1

namespace Charges

def ofFieldKind (x : Charges) : FieldKinds → Finset ℤ
  | .fiveBarHd => x.1.toFinset
  | .fiveBarHu => x.2.1.toFinset
  | .fiveBarMatter => x.2.2.1
  | .tenMatter => x.2.2.2
  | .fiveHd => x.1.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveHu => x.2.1.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveMatter => x.2.2.1.map ⟨Neg.neg, neg_injective⟩

@[simp]
lemma mem_ofFieldKind_fiveHd (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldKind FieldKinds.fiveHd ↔ -x ∈ y.ofFieldKind .fiveBarHd := by
  simp [ofFieldKind, FieldKinds.fiveHd]
  aesop

@[simp]
lemma mem_ofFieldKind_fiveHu (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldKind FieldKinds.fiveHu ↔ -x ∈ y.ofFieldKind .fiveBarHu := by
  simp [ofFieldKind, FieldKinds.fiveHu]
  aesop

@[simp]
lemma mem_ofFieldKind_fiveMatter (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldKind FieldKinds.fiveMatter ↔ -x ∈ y.ofFieldKind .fiveBarMatter := by
  simp [ofFieldKind, FieldKinds.fiveBarHd]
  aesop

lemma ofFieldKind_subset_of_subset {x y : Charges} (h : x ⊆ y) (F : FieldKinds) :
    x.ofFieldKind F ⊆ y.ofFieldKind F := by
  rw [subset_def] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases F
  all_goals simp_all [ofFieldKind]

def ofPotentialTerm (x : Charges) (T : PotentialTerm) : Multiset ℤ :=
  let add : Multiset ℤ → Multiset ℤ → Multiset ℤ := fun a b => (a.product b).map
      fun (x, y) => x + y
  (T.toFieldKinds.map fun F => (ofFieldKind x F).val).foldl add {0}

lemma ofPotentialTerm_subset_of_subset {x y : Charges} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ y.ofPotentialTerm T := by
  have h1 {S1 S2 T1 T2 : Multiset ℤ} (h1 : S1 ⊆ S2) (h2 : T1 ⊆ T2) :
      (S1.product T1) ⊆ S2.product T2 :=
    Multiset.subset_iff.mpr (fun x => by simpa using fun h1' h2' => ⟨h1 h1', h2 h2'⟩)
  rw [subset_def] at h
  cases T
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldKinds]
    repeat'
      apply Multiset.map_subset_map <| Multiset.subset_iff.mpr <|
        h1 _ (Finset.subset_def.mp (ofFieldKind_subset_of_subset h _))
    simp

def IsPresent  (x : Charges) (T : PotentialTerm) : Prop :=
    0 ∈ ofPotentialTerm x T

lemma isPresent_of_subset {T : PotentialTerm} {y x : Charges}
    (h : y ⊆ x) (hy : y.IsPresent T) :
    x.IsPresent T := ofPotentialTerm_subset_of_subset h T hy

def isPresentForm (a b c : ℤ) : (T : PotentialTerm) → Charges
  | .μ =>  (some a, some a, ∅ , ∅)
  | .β =>  (none, some a, {a} , ∅)
  | .Λ =>  (none, none, {a, b}, {- a - b})
  | .W1 => (none, none, {- a - b - c}, {a, b, c})
  | .W2 => (some (- a - b - c), none, ∅, {a, b, c})
  | .W3 => (none, some (- a), {b, - b - 2 * a}, ∅)
  | .W4 => (some (- c - 2 * b), some (- b), {c}, ∅)
  | .K1 => (none, none, {-a}, {b, - a - b})
  | .K2 => (some a, some b, ∅, {- a - b})
  | .topYukawa => (none, some (-a), ∅, {b, - a - b})
  | .bottomYukawa => (some a, none, {b}, {- a - b})

lemma isPresentForm_isPresent {a b c : ℤ} {T : PotentialTerm} :
    (isPresentForm a b c T).IsPresent T := by
  simp [IsPresent, ofPotentialTerm, isPresentForm]
  cases T
  all_goals
    simp [PotentialTerm.toFieldKinds, ofFieldKind, ofPotentialTerm]
  any_goals omega
  case' Λ =>
    use a + b
    simp
    use a, b
    simp
    use 0, a
    simp
  case' W3 =>
    use - 2 * a
    apply And.intro ?_ (by omega)
    use b, -b - 2 * a
    apply And.intro ?_ (by omega)
    simp
    use 0, b
    simp
  case' K1 =>
    use - a
    apply And.intro ?_ (by omega)
    use b, - a - b
    apply And.intro ?_ (by omega)
    simp
    use 0, b
    simp
  case' topYukawa =>
    use - a
    apply And.intro ?_ (by omega)
    use b, - a - b
    apply And.intro ?_ (by omega)
    simp
    use 0, b
    simp
  case' W1 =>
    use a + b + c
    apply And.intro ?_ (by omega)
    use a + b, c
    apply And.intro ?_ (by omega)
    simp
    use a, b
    simp
    use 0, a
    simp
  case' W2 =>
    use a + b + c
    apply And.intro ?_ (by omega)
    use a + b, c
    apply And.intro ?_ (by omega)
    simp
    use a, b
    simp
    use 0, a
    simp

lemma isPresent_of_eq_isPresentForm {T : PotentialTerm}
    (x : Charges) (h : ∃ a b c, x = isPresentForm a b c T) :
    x.IsPresent T := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact isPresentForm_isPresent
open PotentialTerm in

lemma isPresentForm_eq_of_subset {a b c a' b' c' : ℤ} {T : PotentialTerm}
    (h : isPresentForm a b c T ⊆ isPresentForm a' b' c' T) (hT : T ≠ W1 ∧ T ≠ W2):
    isPresentForm a b c T = isPresentForm a' b' c' T := by
  cases T
  case' W1 | W2 => simp at hT
  all_goals
    rw [subset_def] at h
    simp [isPresentForm] at h ⊢
  case' μ =>
    subst h
    rfl
  case' β =>
    subst h
    rfl
  case' K2 =>
    obtain ⟨rfl, rfl, h2⟩ := h
    rfl
  case' W4 =>
    obtain ⟨h2, rfl, rfl⟩ := h
    rfl
  case' bottomYukawa =>
    obtain ⟨rfl, rfl, h2⟩ := h
    rfl
  case' Λ => obtain ⟨h2, h1⟩ := h
  case' K1 =>  obtain ⟨rfl, h2⟩ := h
  case' topYukawa => obtain ⟨rfl, h2⟩ := h
  case' W3 => obtain ⟨rfl, h2⟩ := h
  case' topYukawa | W3 | K1 | Λ  =>
    rw [Finset.insert_subset_iff] at h2
    simp at h2
    obtain ⟨rfl | rfl , h1 | h2 ⟩ := h2
    all_goals simp_all [Finset.pair_comm]


lemma isPresentForm_card_le_degree {a b c : ℤ} {T : PotentialTerm} :
    (isPresentForm a b c T).card ≤ T.degree := by
  cases T
  all_goals
    simp [isPresentForm, PotentialTerm.toFieldKinds, ofFieldKind, ofPotentialTerm, card,
      PotentialTerm.degree]
  case' Λ =>
    have h1 : Finset.card {a, b} ≤ 2 := Finset.card_le_two
    omega
  case' W3  =>
    have h1 : Finset.card {b, -b - 2 * a} ≤ 2 := Finset.card_le_two
    omega
  case' K1  =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  case' topYukawa  =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  all_goals
    have h1 : Finset.card {a, b, c} ≤ 3 := Finset.card_le_three
    omega

lemma isPresentForm_subset_isPresent_of_isPresent {T : PotentialTerm} {x : Charges}
    (h : x.IsPresent T) :
    ∃ a b c, isPresentForm a b c T ⊆ x ∧ (isPresentForm a b c T).IsPresent T := by
  simp [IsPresent, ofPotentialTerm] at h
  cases T
  all_goals
    simp [PotentialTerm.toFieldKinds] at h
    obtain ⟨f1, f2, ⟨⟨f3, f4, ⟨h3, f4_mem⟩ , rfl⟩, f2_mem⟩, f1_add_f2_eq_zero⟩ := h
  case' μ | β =>  obtain ⟨rfl⟩ := h3
  case' Λ | W1 | W2 | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨f5, f6, ⟨h4, f6_mem⟩, rfl⟩ := h3
  case' Λ | K1 | K2 | topYukawa | bottomYukawa => obtain ⟨rfl⟩ := h4
  case' W1 | W2 | W3 | W4 => obtain ⟨f7, f8, ⟨rfl, f8_mem⟩, rfl⟩ := h4
  -- The cases which are present
  case' μ => use f4, (f2), 0
  case' β => use (- f4), f2, 0
  case' Λ => use  f4, f6, f2
  case' W1 => use  f4, f6, f8
  case' W2 => use f4, f6, f8
  case' W3 => use (f2), f6, f8
  case' W4 => use f6, (f2), f8
  case' K1 => use f2, f4, f6
  case' K2 => use  f4, f6, f2
  case' topYukawa => use (f2), f4, f6
  case' bottomYukawa => use f2, f4, f6
  all_goals
    rw [subset_def]
    simp_all [ofFieldKind, ofPotentialTerm, Finset.insert_subset_iff, isPresentForm]
  all_goals
    simp [IsPresent, ofPotentialTerm, PotentialTerm.toFieldKinds, ofFieldKind]
  -- Replacements of equalities
  case' W1 | W2 =>
    have hf2 : f2 =  -f4 - f6 - f8 := by omega
    subst hf2
    simp_all
  case' β =>
    have hf2 : f4 = - f2 := by omega
    subst hf2
    simp_all
  case' K2 =>
    have hf2 : f2 = - f4 - f6 := by omega
    subst hf2
    simp_all
  case' Λ =>
    have hf2 : f2 = -f4 - f6 := by omega
    subst hf2
    simp_all
  case' W3 =>
    subst f4_mem
    have hf8 : f8 = - f6 -2 * f4 := by omega
    subst hf8
    simp_all
  case' bottomYukawa =>
    have hf6 : f6 = - f2 - f4 := by omega
    subst hf6
    simp_all
  -- IsPresent
  any_goals omega
  case' W3 =>
    use (- f6 -2 * f4 ) + f6
    apply And.intro ?_ (by omega)
    try simp
    use (- f6 -2 * f4 ), f6
    simp
    use 0, (- f6 -2 * f4 )
    simp
  case' W1 | W2   =>
    use f8 + f6 + f4
    apply And.intro ?_ (by omega)
    use f8 + f6, f4
  case' W1 | W2   =>
    apply And.intro ?_ (by omega)
    try simp
    use f8, f6
    simp
    use 0, f8
    simp
  case' K1  =>
    have hf6 : f6 = - f2 - f4 := by omega
    subst hf6
    simp_all
    use (-f2 - f4) + f4
    apply And.intro ?_ (by omega)
    use (-f2 - f4), f4
    apply And.intro ?_ (by omega)
    simp
    use 0, (-f2 - f4)
    simp
  case' topYukawa   =>
    have hf2 : f2 = - f4 - f6 := by omega
    subst hf2
    simp_all
  case' topYukawa | Λ  =>
    use f6 + f4
    apply And.intro ?_ (by omega)
    use f6, f4
    apply And.intro ?_ (by omega)
    simp
    use 0, f6
    simp

lemma subset_card_le_degree_isPresent_of_isPresent {T : PotentialTerm} {x : Charges}
    (h : x.IsPresent T) : ∃ y ∈ x.powerset, y.card ≤ T.degree ∧ y.IsPresent T := by
  obtain ⟨a, b, c, h1, h2⟩ := isPresentForm_subset_isPresent_of_isPresent h
  use isPresentForm a b c T
  simp_all
  exact isPresentForm_card_le_degree

/-!

## Is Present decidable

-/

open PotentialTerm
def IsPresentFast (y : Charges) (T : PotentialTerm)  : Prop :=
  let qHd := y.1
  let qHu := y.2.1
  let Q5 := y.2.2.1
  let Q10 := y.2.2.2
  match T with
  | μ => 0 ∈ (qHd.toFinset.product <| qHu.toFinset).val.map (fun x => x.1 - x.2)
  | β => 0 ∈  (qHu.toFinset.product <| Q5).val.map (fun x => - x.1 + x.2)
  | Λ => 0 ∈ (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => 0 ∈ (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 => 0 ∈ (qHd.toFinset.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W3 => 0 ∈ (qHu.toFinset.product <| Q5.product <| Q5).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2)
  | W4 => 0 ∈ (qHd.toFinset.product <| qHu.toFinset.product <| Q5).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2)
  | K1 => 0 ∈ (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2 => 0 ∈  (qHd.toFinset.product <| qHu.toFinset.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)
  | topYukawa => 0 ∈ (qHu.toFinset.product <| Q10.product <| Q10).val.map
    (fun x => -x.1 + x.2.1 + x.2.2)
  | bottomYukawa => 0 ∈ (qHd.toFinset.product <| Q5.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)

lemma isPresentFast_of_isPresent {x : Charges} (T : PotentialTerm) (h : x.IsPresent T) :
    x.IsPresentFast T := by
  simp [IsPresent, ofPotentialTerm] at h
  cases T
  all_goals
    simp [PotentialTerm.toFieldKinds] at h
    obtain ⟨f1, f2, ⟨⟨f3, f4, ⟨h3, f4_mem⟩ , rfl⟩, f2_mem⟩, f1_add_f2_eq_zero⟩ := h
  case' μ | β =>  obtain ⟨rfl⟩ := h3
  case' Λ | W1 | W2 | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨f5, f6, ⟨h4, f6_mem⟩, rfl⟩ := h3
  case' Λ | K1 | K2 | topYukawa | bottomYukawa => obtain ⟨rfl⟩ := h4
  case' W1 | W2 | W3 | W4 => obtain ⟨f7, f8, ⟨rfl, f8_mem⟩, rfl⟩ := h4
  all_goals
    simp [IsPresentFast]
    simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
    simp_all [ofFieldKind]
  case' W1 => use f2, f4, f6, f8
  case' W2 =>  use f2, f4, f6, f8
  case' W3 =>  use (-f2), f6, f8
  case' W4 => use f6, (-f4), f8
  case' K1 => use (-f2), f4, f6
  case' K2 => use f4, f6, f2
  case' Λ => use f4, f6, f2
  case' topYukawa => use (-f2), f4, f6
  case' bottomYukawa => use f2, f4, f6
  case' β => use (-f4), f2
  all_goals simp_all
  all_goals omega

lemma isPresent_of_isPresentFast {x : Charges} (T : PotentialTerm) (h : x.IsPresentFast T) :
    x.IsPresent T := by
  cases T
  all_goals
    simp [IsPresentFast] at h
    simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product] at h
  case' μ | β =>
    obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
  case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
  case' W1 | W2 =>
    obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
  case' μ => refine isPresent_of_subset (y := (q1, q2, ∅, ∅)) ?μSub ?μP
  case' β => refine isPresent_of_subset (y := (none, q1, {q2}, ∅)) ?βSub ?βP
  case' Λ => refine isPresent_of_subset (y := (none, none, {q1, q2}, {q3})) ?ΛSub ?ΛP
  case' W1 => refine isPresent_of_subset (y := (none, none, {q1}, {q2, q3, q4})) ?W1Sub ?W1P
  case' W2 => refine isPresent_of_subset (y := (q1, none, ∅, {q2, q3, q4})) ?W2Sub ?W2P
  case' W3 => refine isPresent_of_subset (y := (none, q1, {q2, q3}, ∅)) ?W3Sub ?W3P
  case' W4 => refine isPresent_of_subset (y := (q1, q2, {q3}, ∅)) ?W4Sub ?W4P
  case' K1 => refine isPresent_of_subset (y := (none, none, {q1}, {q2, q3})) ?K1Sub ?K1P
  case' K2 => refine isPresent_of_subset (y := (q1, q2, ∅, {q3})) ?K2Sub ?K2P
  case' topYukawa => refine isPresent_of_subset (y := (none, q1, ∅, {q2, q3})) ?topYukawaSub ?topYukawaP
  case' bottomYukawa => refine isPresent_of_subset (y := (q1, none, {q2}, {q3})) ?bottomYukawaSub ?bottomYukawaP
  case' μSub | βSub | ΛSub | W1Sub | W2Sub | W3Sub | W4Sub | K1Sub | K2Sub |
      topYukawaSub | bottomYukawaSub =>
    rw [subset_def]
    simp_all [Finset.insert_subset]
  all_goals
    simp [IsPresent, ofPotentialTerm, PotentialTerm.toFieldKinds, ofFieldKind]
  any_goals omega
  case' ΛP =>
    use - q3
    simp
    use - q1 - q3, q1
    apply And.intro ?_ (by omega)
    simp
    use 0
    simp
    omega
  case' W3P =>
    use  2 * q1
    apply And.intro ?_ (by omega)
    use - q2 + 2 * q1, q2
    apply And.intro ?_ (by omega)
    simp
    use 0, q3
    simp
    omega
  case' K1P =>
    use q1
    apply And.intro ?_ (by omega)
    use q1 - q2, q2
    apply And.intro ?_ (by omega)
    simp
    use 0, q3
    simp
    omega
  case' topYukawaP =>
    use q1
    apply And.intro ?_ (by omega)
    use q1 - q2, q2
    apply And.intro ?_ (by omega)
    simp
    use 0, q3
    simp
    omega
  case' W1P | W2P =>
    use - q1
    apply And.intro ?_ (by omega)
    use - q1 - q2, q2
    apply And.intro ?_ (by omega)
    simp
    use -q1 - q2 - q3, q3
    simp
    use 0, q4
    simp
    omega

lemma isPresent_iff_isPresentFast {x : Charges} {T : PotentialTerm} :
    x.IsPresent T ↔ x.IsPresentFast T := by
  constructor
  · exact fun a => isPresentFast_of_isPresent T a
  · exact fun a => isPresent_of_isPresentFast T a


instance (x : Charges) (T : PotentialTerm) : Decidable (x.IsPresentFast T) :=
  match T with
  | μ => inferInstanceAs (Decidable (0 ∈ (x.1.toFinset.product <| x.2.1.toFinset).val.map (fun x => x.1 - x.2)))
  | β => inferInstanceAs (Decidable (0 ∈ (x.2.1.toFinset.product <| x.2.2.1).val.map (fun x => - x.1 + x.2)))
  | Λ => inferInstanceAs (Decidable (0 ∈ (x.2.2.1.product <| x.2.2.1.product <| x.2.2.2).val.map (fun x => x.1 + x.2.1 + x.2.2)))
  | W1 => inferInstanceAs (Decidable (0 ∈ (x.2.2.1.product <| x.2.2.2.product <| x.2.2.2.product <| x.2.2.2).val.map
      (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)))
  | W2 => inferInstanceAs (Decidable (0 ∈ (x.1.toFinset.product <| x.2.2.2.product <| x.2.2.2.product <| x.2.2.2).val.map
      (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)))
  | W3 => inferInstanceAs (Decidable (0 ∈ (x.2.1.toFinset.product <| x.2.2.1.product <| x.2.2.1).val.map
      (fun x => -x.1 - x.1 + x.2.1 + x.2.2)))
  | W4 => inferInstanceAs (Decidable (0 ∈ (x.1.toFinset.product <| x.2.1.toFinset.product <| x.2.2.1).val.map
      (fun x => x.1 - x.2.1 - x.2.1 + x.2.2)))
  | K1 => inferInstanceAs (Decidable (0 ∈ (x.2.2.1.product <| x.2.2.2.product <| x.2.2.2).val.map
      (fun x => - x.1 + x.2.1 + x.2.2)))
  | K2 => inferInstanceAs (Decidable (0 ∈ (x.1.toFinset.product <| x.2.1.toFinset.product <| x.2.2.2).val.map
      (fun x => x.1 + x.2.1 + x.2.2)))
  | topYukawa => inferInstanceAs (Decidable (0 ∈ (x.2.1.toFinset.product <| x.2.2.2.product <| x.2.2.2).val.map
      (fun x => -x.1 + x.2.1 + x.2.2)))
  | bottomYukawa => inferInstanceAs (Decidable (0 ∈ (x.1.toFinset.product <| x.2.2.1.product <| x.2.2.2).val.map
      (fun x => x.1 + x.2.1 + x.2.2)))



instance (x : Charges) (T : PotentialTerm) : Decidable (x.IsPresent T) :=
  decidable_of_iff (x.IsPresentFast T) isPresent_iff_isPresentFast.symm


end Charges

end SU5U1
end FTheory
