/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfPotentialTerm
import PhysLean.StringTheory.FTheory.SU5U1.Potential.Basic
/-!

# Charges associated with a potential term

-/

namespace FTheory
namespace SU5U1

namespace Charges

def IsPresent (x : Charges) (T : PotentialTerm) : Prop := 0 ∈ ofPotentialTerm x T

lemma isPresent_iff_zero_mem_ofPotentialTerm' {x : Charges} {T : PotentialTerm} :
    x.IsPresent T ↔ 0 ∈ x.ofPotentialTerm' T := by
  rw [IsPresent]
  exact mem_ofPotentialTerm_iff_mem_ofPotentialTerm

lemma isPresent_of_subset {T : PotentialTerm} {y x : Charges}
    (h : y ⊆ x) (hy : y.IsPresent T) : x.IsPresent T := ofPotentialTerm_subset_of_subset h T hy

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
    simp [PotentialTerm.toFieldLabel, ofFieldLabel, ofPotentialTerm]
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
    simp [isPresentForm, PotentialTerm.toFieldLabel, ofFieldLabel, ofPotentialTerm, card,
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
    simp [PotentialTerm.toFieldLabel] at h
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
    simp_all [ofFieldLabel, ofPotentialTerm, Finset.insert_subset_iff, isPresentForm]
  all_goals
    simp [IsPresent, ofPotentialTerm, PotentialTerm.toFieldLabel, ofFieldLabel]
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

instance (x : Charges) (T : PotentialTerm) : Decidable (x.IsPresent T) :=
  decidable_of_iff (0 ∈ x.ofPotentialTerm' T) isPresent_iff_zero_mem_ofPotentialTerm'.symm

end Charges

end SU5U1
end FTheory
