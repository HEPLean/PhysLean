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
  simp [IsIrreducible] at h
  simpa using h x (self_mem_powerset x)

lemma isPresent_of_has_isIrreducible_subset {T : PotentialTerm} {x : T.ChargeProfile}
    (hx : ∃ y ∈ powerset x, IsIrreducible y) : IsPresent T x := by
  obtain ⟨y, hy⟩ := hx
  rw [← subset_of_iff_mem_powerset] at hy
  apply isPresent_of_subset hy.1
  exact isPresent_of_isIrreducible hy.2

end ChargeProfile

end PotentialTerm

end SU5U1

end FTheory
