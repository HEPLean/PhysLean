/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.AllowsTerm


namespace FTheory
namespace SU5U1

namespace Charges

def IsIrreducible (x : Charges) (T : PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ y.AllowsTerm T

instance (x : Charges) (T : PotentialTerm) : Decidable (x.IsIrreducible T) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ y.AllowsTerm T))

variable {T : PotentialTerm} {x : Charges}

lemma allowsTerm_of_isIrreducible (h : x.IsIrreducible T) : x.AllowsTerm T := by
  simp only [IsIrreducible] at h
  simpa using h x (self_mem_powerset x)

lemma allowsTerm_of_has_isIrreducible_subset (hx : ∃ y ∈ powerset x, y.IsIrreducible T) :
    x.AllowsTerm T := by
  obtain ⟨y, hy⟩ := hx
  simp only [mem_powerset_iff_subset] at hy
  apply allowsTerm_of_subset hy.1
  exact allowsTerm_of_isIrreducible hy.2

lemma isIrreducible_iff_powerset_filter_eq :
    x.IsIrreducible T ↔ x.powerset.filter (fun y => y.AllowsTerm T) = {x} := by
  constructor
  · intro h
    ext y
    simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_singleton]
    simp [IsIrreducible] at h
    constructor
    · exact fun ⟨h1, h2⟩ => (h y h1).mpr h2
    · intro h1
      subst h1
      simp
      exact (h y (by simp)).mp rfl
  · intro h
    simp [IsIrreducible]
    intro y hy
    rw [Finset.eq_singleton_iff_unique_mem] at h
    simp at h
    constructor
    · intro h1
      subst h1
      exact h.1
    · intro h1
      apply h.2
      · exact hy
      · exact h1

lemma isIrreducible_iff_powerset_countP_eq_one  :
    x.IsIrreducible T ↔ x.powerset.val.countP (fun y => y.AllowsTerm T) = 1 := by
  rw [isIrreducible_iff_powerset_filter_eq]
  constructor
  · intro h
    trans (Finset.filter (fun y => y.AllowsTerm T) x.powerset).card
    · change _ = (Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val).card
      exact Multiset.countP_eq_card_filter (fun y => y.AllowsTerm T) x.powerset.val
    · rw [h]
      simp
  · intro h
    have h1 : (Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val).card = 1 := by
      rw [← h]
      exact Eq.symm (Multiset.countP_eq_card_filter (fun y => y.AllowsTerm T) x.powerset.val)
    rw [Multiset.card_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have haMem : a ∈ Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val := by
      simp [ha]
    simp at haMem
    have hxMem : x ∈ Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val := by
      simpa using allowsTerm_of_subset haMem.1 haMem.2
    rw [ha] at hxMem
    simp at hxMem
    subst hxMem
    exact Finset.val_inj.mp ha

lemma subset_isIrreducible_of_allowsTerm
    (hx : x.AllowsTerm T) : ∃ y ∈ powerset x, y.IsIrreducible T := by
  have hPresent : (x.powerset.filter (fun y => y.AllowsTerm T)) ≠ ∅ := by
    rw [← @Finset.nonempty_iff_ne_empty]
    use x
    simp [hx]
  obtain ⟨y, h1, h2⟩ := min_exists (x.powerset.filter (fun y => y.AllowsTerm T)) hPresent
  use y
  simp at h1
  simp_all
  rw [isIrreducible_iff_powerset_filter_eq]
  rw [← h2]
  ext z
  simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_inter, and_congr_right_iff,
    iff_and_self]
  intro hzy hzpres
  exact subset_trans hzy h1.1

lemma allowsTerm_iff_subset_isIrreducible :
    x.AllowsTerm T ↔ ∃ y ∈ powerset x, y.IsIrreducible T :=
  ⟨fun h => subset_isIrreducible_of_allowsTerm h, fun h => allowsTerm_of_has_isIrreducible_subset h⟩

lemma card_le_degree_of_isIrreducible (h : x.IsIrreducible T) :
    x.card ≤ T.degree := by
  obtain ⟨y, y_mem_power, y_card,y_present⟩ :=
    subset_card_le_degree_allowsTerm_of_allowsTerm (allowsTerm_of_isIrreducible h)
  have hy : y ∈ x.powerset.filter (fun y => y.AllowsTerm T)  := by
    simp_all
  rw [isIrreducible_iff_powerset_filter_eq] at h
  rw [h] at hy
  simp at hy
  subst hy
  exact y_card

lemma eq_allowsTermForm_of_isIrreducible (h1 : x.IsIrreducible T) :
    ∃ a b c, x = allowsTermForm a b c T := by
  obtain ⟨a, b, c,  h2, h3⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm
    (allowsTerm_of_isIrreducible h1)
  use a, b, c
  have hy : allowsTermForm a b c T ∈ x.powerset.filter (fun y => y.AllowsTerm T)  := by
    simp_all
  rw [isIrreducible_iff_powerset_filter_eq] at h1
  rw [h1] at hy
  simp at hy
  exact hy.symm

open PotentialTerm in
lemma allowsTermForm_isIrreducible  {a b c  : ℤ} {T : PotentialTerm}
    (hT : T ≠ W1 ∧ T ≠ W2) :
    IsIrreducible (allowsTermForm a b c T) T := by
  simp [IsIrreducible]
  intro y hy
  constructor
  · intro h
    subst h
    exact allowsTermForm_allowsTerm
  · intro h
    obtain ⟨a', b', c', hsub, hAllowsTerm⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
    have hEq : allowsTermForm a' b' c' T  = allowsTermForm a b c T :=
      allowsTermForm_eq_of_subset (subset_trans hsub hy) hT
    apply subset_antisymm hy
    rw [← hEq]
    exact hsub

end Charges

end SU5U1
end FTheory
