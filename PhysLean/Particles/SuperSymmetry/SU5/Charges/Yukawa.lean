/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.PhenoConstrained
/-!

# Yukawa charges

This module includes the charges associated with the Yukawa terms in the superpotential.
It also asks the following question:
Do the singlets needed to regenerate the Yukawa terms regenerate a dangerous coupling
in the superpotential with up to `n` insertions of the Yukawa singlets?
This questions is manifested in the `YukawaGeneratesDangerousAtLevel` predicate.

-/

namespace SuperSymmetry
namespace SU5

namespace Charges
open PotentialTerm

/-- The collection of charges associated with Yukawa terms.
  Correspondingly, the (negative) of the charges of the singlets needed to regenerate all
  Yukawa terms in the potential. -/
def ofYukawaTerms (x : Charges) : Multiset ℤ :=
   x.ofPotentialTerm topYukawa + x.ofPotentialTerm bottomYukawa

lemma ofYukawaTerms_subset_of_subset {x y : Charges} (h : x ⊆ y) :
    x.ofYukawaTerms ⊆ y.ofYukawaTerms := by
  simp only [ofYukawaTerms]
  refine Multiset.subset_iff.mpr ?_
  intro z
  simp only [Multiset.mem_add]
  intro hr
  rcases hr with hr | hr
  · left
    apply ofPotentialTerm_subset_of_subset h
    exact hr
  · right
    apply ofPotentialTerm_subset_of_subset h
    exact hr

/-- The charges of those terms which can be regenerated with up-to `n`
  insertions of singlets needed to regenerate the Yukawa terms.
  Equivalently, the sum of up-to `n` integers each corresponding to a charge of the
  Yukawa terms.  -/
def ofYukawaTermsNSum (x : Charges) : ℕ → Multiset ℤ
  | 0 => {0}
  | n + 1 => x.ofYukawaTermsNSum n + (x.ofYukawaTermsNSum n).bind fun sSum =>
    (x.ofYukawaTerms.map fun s => sSum + s)

lemma ofYukawaTermsNSum_subset_of_subset {x y : Charges} (h : x ⊆ y) (n : ℕ) :
    x.ofYukawaTermsNSum n ⊆ y.ofYukawaTermsNSum n := by
  induction n with
  | zero => simp [ofYukawaTermsNSum]
  | succ n ih =>
    simp [ofYukawaTermsNSum]
    refine Multiset.subset_iff.mpr ?_
    intro z
    simp only [Multiset.mem_add, Multiset.mem_bind, Multiset.mem_map]
    intro hr
    rcases hr with hr | ⟨z1, hz1, z2, hz2, hsum⟩
    · left
      exact ih hr
    right
    use z1
    constructor
    · exact ih hz1
    use z2
    simp_all only [and_true]
    apply ofYukawaTerms_subset_of_subset h
    exact hz2

/-- For charges `x : Charges`, the proposition which states that the singlets
  needed to regenerate the Yukawa couplings regnerate a dangerous coupling
  (in the superpotential) with up-to `n` insertions of the scalars. -/
def YukawaGeneratesDangerousAtLevel (x : Charges) (n : ℕ) : Prop :=
  (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset ≠ ∅

@[simp]
lemma not_yukawaGeneratesDangerousAtLevel_of_empty (n : ℕ) :
    ¬ YukawaGeneratesDangerousAtLevel ∅ n := by
  simp [YukawaGeneratesDangerousAtLevel]

instance (x : Charges) (n : ℕ) : Decidable (YukawaGeneratesDangerousAtLevel x n) :=
  inferInstanceAs (Decidable ((x.ofYukawaTermsNSum n).toFinset
    ∩ x.phenoConstrainingChargesSP.toFinset ≠ ∅))

lemma yukawaGeneratesDangerousAtLevel_of_subset {x y : Charges} {n : ℕ} (h : x ⊆ y)
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    y.YukawaGeneratesDangerousAtLevel n := by
  simp [YukawaGeneratesDangerousAtLevel] at *
  have h1 : (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset
      ⊆ (y.ofYukawaTermsNSum n).toFinset ∩ y.phenoConstrainingChargesSP.toFinset := by
    trans (x.ofYukawaTermsNSum n).toFinset ∩ y.phenoConstrainingChargesSP.toFinset
    · apply Finset.inter_subset_inter_left
      simp only [Multiset.toFinset_subset]
      exact phenoConstrainingChargesSP_of_subset h
    · apply Finset.inter_subset_inter_right
      simp only [Multiset.toFinset_subset]
      exact ofYukawaTermsNSum_subset_of_subset h n
  by_contra hn
  rw [hn] at h1
  simp at h1
  rw [h1] at hx
  simp at hx

lemma yukawaGeneratesDangerousAtLevel_succ {x : Charges} {n : ℕ}
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel (n + 1) := by
  simp [YukawaGeneratesDangerousAtLevel] at *
  simp [ofYukawaTermsNSum]
  rw [Finset.union_inter_distrib_right]
  rw [Finset.union_eq_empty]
  rw [not_and_or]
  left
  exact hx

lemma yukawaGeneratesDangerousAtLevel_add_of_left {x : Charges} {n k : ℕ}
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel (n + k) := by
  induction k with
  | zero => exact hx
  | succ k ih => exact yukawaGeneratesDangerousAtLevel_succ ih

lemma yukawaGeneratesDangerousAtLevel_of_le {x : Charges} {n m : ℕ}
    (h : n ≤ m) (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel m := by
  let k := m - n
  have h1 : n + k = m := by omega
  generalize k = k' at *
  subst h1
  exact yukawaGeneratesDangerousAtLevel_add_of_left hx

end Charges

end SU5
end SuperSymmetry
