/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.AllowsTerm
/-!

# Minimally allows terms

Given a set of charges `x : Charges` corresponding to charges of the representations
present in the theory, and a potential term `T : PotentialTerm`, we say that `x`
minimally allows `T` if it allows the term `T` and no proper subset of `x` allows `T`.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]
open SuperSymmetry.SU5

/-- A collection of charges `x : Charges` is said to minimally allow
  the potential term `T` if it allows `T` and no strict subset of it allows `T`. -/
def MinimallyAllowsTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ y.AllowsTerm T

instance (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Decidable (x.MinimallyAllowsTerm T) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ y.AllowsTerm T))

variable {T : PotentialTerm} {x : ChargeSpectrum 𝓩}

lemma allowsTerm_of_minimallyAllowsTerm (h : x.MinimallyAllowsTerm T) : x.AllowsTerm T := by
  simp only [MinimallyAllowsTerm] at h
  simpa using h x (self_mem_powerset x)

lemma allowsTerm_of_has_minimallyAllowsTerm_subset
    (hx : ∃ y ∈ powerset x, y.MinimallyAllowsTerm T) : x.AllowsTerm T := by
  obtain ⟨y, hy⟩ := hx
  simp only [mem_powerset_iff_subset] at hy
  apply allowsTerm_mono hy.1
  exact allowsTerm_of_minimallyAllowsTerm hy.2

lemma minimallyAllowsTerm_iff_powerset_filter_eq :
    x.MinimallyAllowsTerm T ↔ x.powerset.filter (fun y => y.AllowsTerm T) = {x} := by
  constructor
  · intro h
    ext y
    simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_singleton]
    simp [MinimallyAllowsTerm] at h
    constructor
    · exact fun ⟨h1, h2⟩ => (h y h1).mpr h2
    · intro h1
      subst h1
      simp
      exact (h y (by simp)).mp rfl
  · intro h
    simp [MinimallyAllowsTerm]
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

lemma minimallyAllowsTerm_iff_powerset_countP_eq_one :
    x.MinimallyAllowsTerm T ↔ x.powerset.val.countP (fun y => y.AllowsTerm T) = 1 := by
  rw [minimallyAllowsTerm_iff_powerset_filter_eq]
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
      simpa using allowsTerm_mono haMem.1 haMem.2
    rw [ha] at hxMem
    simp at hxMem
    subst hxMem
    exact Finset.val_inj.mp ha

lemma subset_minimallyAllowsTerm_of_allowsTerm
    (hx : x.AllowsTerm T) : ∃ y ∈ powerset x, y.MinimallyAllowsTerm T := by
  have hPresent : (x.powerset.filter (fun y => y.AllowsTerm T)) ≠ ∅ := by
    rw [← @Finset.nonempty_iff_ne_empty]
    use x
    simp [hx]
  obtain ⟨y, h1, h2⟩ := min_exists (x.powerset.filter (fun y => y.AllowsTerm T)) hPresent
  use y
  simp at h1
  simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq]
  rw [← h2]
  ext z
  simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_inter, and_congr_right_iff,
    iff_and_self]
  intro hzy hzpres
  exact subset_trans hzy h1.1

lemma allowsTerm_iff_subset_minimallyAllowsTerm :
    x.AllowsTerm T ↔ ∃ y ∈ powerset x, y.MinimallyAllowsTerm T :=
  ⟨fun h => subset_minimallyAllowsTerm_of_allowsTerm h, fun h =>
    allowsTerm_of_has_minimallyAllowsTerm_subset h⟩

lemma card_le_degree_of_minimallyAllowsTerm (h : x.MinimallyAllowsTerm T) :
    x.card ≤ T.degree := by
  obtain ⟨y, y_mem_power, y_card,y_present⟩ :=
    subset_card_le_degree_allowsTerm_of_allowsTerm (allowsTerm_of_minimallyAllowsTerm h)
  have hy : y ∈ x.powerset.filter (fun y => y.AllowsTerm T) := by
    simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq] at h
  rw [h] at hy
  simp at hy
  subst hy
  exact y_card

lemma eq_allowsTermForm_of_minimallyAllowsTerm (h1 : x.MinimallyAllowsTerm T) :
    ∃ a b c, x = allowsTermForm a b c T := by
  obtain ⟨a, b, c, h2, h3⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm
    (allowsTerm_of_minimallyAllowsTerm h1)
  use a, b, c
  have hy : allowsTermForm a b c T ∈ x.powerset.filter (fun y => y.AllowsTerm T) := by
    simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq] at h1
  rw [h1] at hy
  simp at hy
  exact hy.symm

open PotentialTerm in
lemma allowsTermForm_minimallyAllowsTerm {a b c : 𝓩} {T : PotentialTerm}
    (hT : T ≠ W1 ∧ T ≠ W2) :
    MinimallyAllowsTerm (allowsTermForm a b c T) T := by
  simp [MinimallyAllowsTerm]
  intro y hy
  constructor
  · intro h
    subst h
    exact allowsTermForm_allowsTerm
  · intro h
    obtain ⟨a', b', c', hsub, hAllowsTerm⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
    have hEq : allowsTermForm a' b' c' T = allowsTermForm a b c T :=
      allowsTermForm_eq_of_subset (subset_trans hsub hy) hT
    apply subset_antisymm hy
    rw [← hEq]
    exact hsub

end ChargeSpectrum

end SU5
end SuperSymmetry
