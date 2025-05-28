/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Basic
/-!

# Irreducible Charge Profiles

An irreducible charge profile is a charge profile that allows it's potential term,
but for which no other member of its powerset allows the potential term.

## Related PRs

- See #562 for a first version of code related to charge profiles.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace PotentialTerm

namespace ChargeProfile

/-- For a potential term `T`, an `x : T.ChargeProfile` is said to be irreducible if
  it allows the term `T`, and no other member of it's powerset allows `T`. -/
def IsIrreducible {T : PotentialTerm} (x : T.ChargeProfile) : Prop :=
  ∀ y ∈ powerset x, y = x ↔ IsPresent T y

instance {T : PotentialTerm} (x : T.ChargeProfile) : Decidable x.IsIrreducible :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ IsPresent T y))

lemma isPresent_of_isIrreducible {T : PotentialTerm} {x : T.ChargeProfile} (h : IsIrreducible x) :
    IsPresent T x := by
  simp only [IsIrreducible] at h
  simpa using h x (self_mem_powerset x)

lemma isPresent_of_has_isIrreducible_subset {T : PotentialTerm} {x : T.ChargeProfile}
    (hx : ∃ y ∈ powerset x, IsIrreducible y) : IsPresent T x := by
  obtain ⟨y, hy⟩ := hx
  simp only [mem_powerset_iff_subset] at hy
  apply isPresent_of_subset hy.1
  exact isPresent_of_isIrreducible hy.2

lemma isIrreducible_iff_powerset_filter_eq {T : PotentialTerm} {x : T.ChargeProfile} :
    x.IsIrreducible ↔ x.powerset.filter (IsPresent T) = {x} := by
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

lemma isIrreducible_iff_powerset_countP_eq_one {T : PotentialTerm} {x : T.ChargeProfile} :
    x.IsIrreducible ↔ x.powerset.val.countP (IsPresent T) = 1 := by
  rw [isIrreducible_iff_powerset_filter_eq]
  constructor
  · intro h
    trans (Finset.filter (IsPresent T) x.powerset).card
    · change _ = (Multiset.filter (IsPresent T) x.powerset.val).card
      exact Multiset.countP_eq_card_filter (IsPresent T) x.powerset.val
    · rw [h]
      simp
  · intro h
    have h1 : (Multiset.filter (IsPresent T) x.powerset.val).card = 1 := by
      rw [← h]
      exact Eq.symm (Multiset.countP_eq_card_filter (IsPresent T) x.powerset.val)
    rw [Multiset.card_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have haMem : a ∈ Multiset.filter (IsPresent T) x.powerset.val := by
      simp [ha]
    simp at haMem
    have hxMem : x ∈ Multiset.filter (IsPresent T) x.powerset.val := by
      simpa using isPresent_of_subset haMem.1 haMem.2
    rw [ha] at hxMem
    simp at hxMem
    subst hxMem
    exact Eq.symm ((fun {α} {s t} => Finset.val_inj.mp) (id (Eq.symm ha)))

lemma subset_isIrreducible_of_isPresent {T : PotentialTerm} {x : T.ChargeProfile}
    (hx : IsPresent T x) : ∃ y ∈ powerset x, IsIrreducible y := by
  have hPresent : (x.powerset.filter (IsPresent T)) ≠ ∅ := by
    rw [← @Finset.nonempty_iff_ne_empty]
    use x
    simp [hx]
  obtain ⟨y, h1, h2⟩ := min_exists (x.powerset.filter (IsPresent T)) hPresent
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

lemma isPresent_iff_subest_isIrreducible {T : PotentialTerm} {x : T.ChargeProfile} :
    IsPresent T x ↔ ∃ y ∈ powerset x, IsIrreducible y :=
  ⟨fun h => subset_isIrreducible_of_isPresent h, fun h => isPresent_of_has_isIrreducible_subset h⟩

end ChargeProfile

end PotentialTerm

end SU5U1

end FTheory
