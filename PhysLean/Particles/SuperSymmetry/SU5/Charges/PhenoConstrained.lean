/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.AllowsTerm
import Mathlib.Tactic.Polyrith
/-!

# Pheno constrained charges

We say a charge is pheno-constrained if it leads to allows proton decay or
R-parity violating terms.

We are actually intrested in the charges which are not pheno-constrained.

-/
namespace SuperSymmetry

namespace SU5

namespace Charges
open SuperSymmetry.SU5
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-- A charge is pheno-constrained if it leads to the presence of any term causing proton decay
  ` {W1, Λ, W2, K1}` or R-parity violation `{β, Λ, W2, W4, K1, K2}`. -/
def IsPhenoConstrained (x : Charges 𝓩) : Prop :=
  x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2 ∨ x.AllowsTerm W4 ∨
  x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1

instance decidableIsPhenoConstrained [DecidableEq 𝓩] (x : Charges 𝓩) :
    Decidable x.IsPhenoConstrained :=
  inferInstanceAs (Decidable (x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2
    ∨ x.AllowsTerm W4 ∨ x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1))

@[simp]
lemma not_isPhenoConstrained_empty :
    ¬ IsPhenoConstrained (∅ : Charges 𝓩) := by
  simp [IsPhenoConstrained, AllowsTerm, ofPotentialTerm_empty]

lemma isPhenoConstrained_mono {x y : Charges 𝓩} (h : x ⊆ y)
    (hx : x.IsPhenoConstrained) : y.IsPhenoConstrained := by
  simp [IsPhenoConstrained] at *
  rcases hx with hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    have h' := allowsTerm_mono h hr
    simp_all

/-- The collection of charges of super-potential terms leading to a pheno-constrained model. -/
def phenoConstrainingChargesSP (x : Charges 𝓩) : Multiset 𝓩 :=
  x.ofPotentialTerm' μ + x.ofPotentialTerm' β + x.ofPotentialTerm' Λ +
  x.ofPotentialTerm' W2 + x.ofPotentialTerm' W4 + x.ofPotentialTerm' W1

@[simp]
lemma phenoConstrainingChargesSP_empty :
    phenoConstrainingChargesSP (∅ : Charges 𝓩) = ∅ := by
  simp [phenoConstrainingChargesSP]

lemma phenoConstrainingChargesSP_mono [DecidableEq 𝓩] {x y : Charges 𝓩} (h : x ⊆ y) :
    x.phenoConstrainingChargesSP ⊆ y.phenoConstrainingChargesSP := by
  simp only [phenoConstrainingChargesSP]
  refine Multiset.subset_iff.mpr ?_
  intro z
  simp [or_assoc]
  intro hr
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals
    have h' := ofPotentialTerm'_mono h _ hr
    simp_all

/-!

## Is Pheno constrained Q5 addition

-/

/-- The proposition which is true if the addition of a charge `q5` to a set of charegs `x` leads
  `x` to being phenomenologically constrained. -/
def IsPhenoConstrainedQ5 [DecidableEq 𝓩] (x : Charges 𝓩) (q5 : 𝓩) : Prop :=
  x.AllowsTermQ5 q5 μ ∨ x.AllowsTermQ5 q5 β ∨ x.AllowsTermQ5 q5 Λ ∨ x.AllowsTermQ5 q5 W2 ∨
  x.AllowsTermQ5 q5 W4 ∨
  x.AllowsTermQ5 q5 K1 ∨ x.AllowsTermQ5 q5 K2 ∨ x.AllowsTermQ5 q5 W1

lemma isPhenoConstrainedQ5_iff [DecidableEq 𝓩] (x : Charges 𝓩) (q5 : 𝓩) :
    x.IsPhenoConstrainedQ5 q5 ↔
    x.AllowsTermQ5 q5 β ∨ x.AllowsTermQ5 q5 Λ ∨ x.AllowsTermQ5 q5 W4 ∨
    x.AllowsTermQ5 q5 K1 ∨ x.AllowsTermQ5 q5 W1 := by
  simp [IsPhenoConstrainedQ5, AllowsTermQ5]

instance decidableIsPhenoConstrainedQ5 [DecidableEq 𝓩] (x : Charges 𝓩) (q5 : 𝓩) :
    Decidable (x.IsPhenoConstrainedQ5 q5) :=
  decidable_of_iff _ (isPhenoConstrainedQ5_iff x q5).symm

lemma isPhenoConstrained_insertQ5_iff_isPhenoConstrainedQ5 [DecidableEq 𝓩] {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} :
    IsPhenoConstrained (qHd, qHu, insert q5 Q5, Q10) ↔
    IsPhenoConstrainedQ5 (qHd, qHu, Q5, Q10) q5 ∨
    IsPhenoConstrained (qHd, qHu, Q5, Q10) := by
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
    all_goals
      rw [allowsTerm_insertQ5_iff_allowsTermQ5] at hr
      rcases hr with hr | hr
      all_goals
        simp_all [IsPhenoConstrainedQ5, IsPhenoConstrained]
  · intro hr
    rcases hr with hr | hr
    · simp [IsPhenoConstrainedQ5] at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals
        have hr' := allowsTerm_insertQ5_of_allowsTermQ5 _ hr
        simp_all [IsPhenoConstrained]
    · apply isPhenoConstrained_mono _ hr
      simp [subset_def]

/-- The proposition which is true if the addition of a charge `q10` to a set of charegs `x` leads
  `x` to being phenomenologically constrained. -/
def IsPhenoConstrainedQ10 [DecidableEq 𝓩] (x : Charges 𝓩) (q10 : 𝓩) : Prop :=
  x.AllowsTermQ10 q10 μ ∨ x.AllowsTermQ10 q10 β ∨ x.AllowsTermQ10 q10 Λ ∨ x.AllowsTermQ10 q10 W2 ∨
  x.AllowsTermQ10 q10 W4 ∨
  x.AllowsTermQ10 q10 K1 ∨ x.AllowsTermQ10 q10 K2 ∨ x.AllowsTermQ10 q10 W1

lemma isPhenoConstrainedQ10_iff [DecidableEq 𝓩] (x : Charges 𝓩) (q10 : 𝓩) :
    x.IsPhenoConstrainedQ10 q10 ↔ x.AllowsTermQ10 q10 Λ ∨ x.AllowsTermQ10 q10 W2 ∨
    x.AllowsTermQ10 q10 K1 ∨ x.AllowsTermQ10 q10 K2 ∨ x.AllowsTermQ10 q10 W1 := by
  simp [IsPhenoConstrainedQ10, AllowsTermQ10]

instance decidableIsPhenoConstrainedQ10 [DecidableEq 𝓩] (x : Charges 𝓩) (q10 : 𝓩) :
    Decidable (x.IsPhenoConstrainedQ10 q10) :=
  decidable_of_iff _ (isPhenoConstrainedQ10_iff x q10).symm

lemma isPhenoConstrained_insertQ10_iff_isPhenoConstrainedQ10 [DecidableEq 𝓩] {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} :
    IsPhenoConstrained (qHd, qHu, Q5, insert q10 Q10) ↔
    IsPhenoConstrainedQ10 (qHd, qHu, Q5, Q10) q10 ∨
    IsPhenoConstrained (qHd, qHu, Q5, Q10) := by
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
    all_goals
      rw [allowsTerm_insertQ10_iff_allowsTermQ10] at hr
      rcases hr with hr | hr
      all_goals
        simp_all [IsPhenoConstrainedQ10, IsPhenoConstrained]
  · intro hr
    rcases hr with hr | hr
    · simp [IsPhenoConstrainedQ10] at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals
        have hr' := allowsTerm_insertQ10_of_allowsTermQ10 _ hr
        simp_all [IsPhenoConstrained]
    · apply isPhenoConstrained_mono _ hr
      simp [subset_def]

end Charges

end SU5

end SuperSymmetry
