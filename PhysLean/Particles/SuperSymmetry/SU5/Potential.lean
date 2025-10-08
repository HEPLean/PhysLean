/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.FieldLabels
/-!

# Potential of the SU(5) + U(1) GUT

## i. Overview

In this module we will write down some of the potential terms appearing in
an `SU(5)` SUSY GUT model, with matter in the 5-bar and 10d representations.

A future iteration of this file will include all terms,
and derive them from symmetry properties.

The terms of the super-potential we will consider are:
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

The terms of the Kahler potential are:
`K ⊃ K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

## ii. Key results

- `PotentialTerm` : The inductive type indexing the potential terms.
- `violateRParity` : The finite set of terms which violate R-parity.
  `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
- `causeProtonDecay` : The finite set of terms which contribute to proton decay.
  `W¹`, `W²`, `K¹`, `λ`

## iii. Table of contents

- A. The definition of `PotentialTerm`
- B. Relation to field labels
- C. Presence in the super-potential
  - C.1. In super potential implies no conjugate fields
- D. Degree of the potential term
- E. R-parity of the potential terms
- F. Terms which violate proton decay

## iv. References

- The main reference for the terms, and notation used in this module is: arXiv:0912.0853
A previous version of this code was replaced in PR#569.

-/

namespace SuperSymmetry

namespace SU5

/-!

## A. The definition of `PotentialTerm`

We define an inductive type with a term for each of the potential terms we are interested in,
present in both the super-potential and Kahler potential.

-/

/-- Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT. -/
inductive PotentialTerm
  /-- The term `μ 5Hu 5̄Hd` appearing in the super-potential. -/
  | μ : PotentialTerm
  /-- The term `𝛽ᵢ 5̄Mⁱ5Hu` appearing in the super-potential. -/
  | β : PotentialTerm
  /-- The term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` appearing in the super-potential. -/
  | Λ : PotentialTerm
  /-- The term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` appearing in the super-potential. -/
  | W1 : PotentialTerm
  /-- The term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd` appearing in the super-potential. -/
  | W2 : PotentialTerm
  /-- The term `W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu` appearing in the super-potential. -/
  | W3 : PotentialTerm
  /-- The term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu` appearing in the super-potential. -/
  | W4 : PotentialTerm
  /-- The term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ` appearing in the Kahler potential. -/
  | K1 : PotentialTerm
  /-- The term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` appearing in the Kahler potential. -/
  | K2 : PotentialTerm
  /-- The term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu` appearing in the super-potential. -/
  | topYukawa : PotentialTerm
  /-- The term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd` appearing in the super-potential. -/
  | bottomYukawa : PotentialTerm
deriving DecidableEq, Fintype

namespace PotentialTerm

/-!

## B. Relation to field labels

We map each term in the potential to the list of `FieldLabel`s which it contains.
This allows us to define various properties of the potential term in a safe way, based
solely on the field content.

-/

/-- The fields contained within a given term of the potential. -/
def toFieldLabel : PotentialTerm → List FieldLabel
  | μ => [.fiveBarHd, .fiveHu]
  | β => [.fiveHu, .fiveBarMatter]
  | Λ => [.fiveBarMatter, .fiveBarMatter, .tenMatter]
  | W1 => [.tenMatter, .tenMatter, .tenMatter, .fiveBarMatter]
  | W2 => [.tenMatter, .tenMatter, .tenMatter, .fiveBarHd]
  | W3 => [.fiveBarMatter, .fiveBarMatter, .fiveHu, .fiveHu]
  | W4 => [.fiveBarMatter, .fiveBarHd, .fiveHu, .fiveHu]
  | K1 => [.tenMatter, .tenMatter, .fiveMatter]
  | K2 => [.fiveBarHu, .fiveBarHd, .tenMatter]
  | topYukawa => [.tenMatter, .tenMatter, .fiveHu]
  | bottomYukawa => [.tenMatter, .fiveBarMatter, .fiveBarHd]

/-!

## C. Presence in the super-potential

We define a predicate which is true on those terms which are members of the super-potential.
We will also prove that this predicate is decidable.

-/

/-- The proposition which is true on those terms which are members of the
  super potential. -/
def InSuperPotential : PotentialTerm → Prop
  | μ => True
  | β => True
  | Λ => True
  | W1 => True
  | W2 => True
  | W3 => True
  | W4 => True
  | K1 => False
  | K2 => False
  | topYukawa => True
  | bottomYukawa => True

instance : (T : PotentialTerm) → Decidable (InSuperPotential T)
  | μ => inferInstanceAs (Decidable True)
  | β => inferInstanceAs (Decidable True)
  | Λ => inferInstanceAs (Decidable True)
  | W1 => inferInstanceAs (Decidable True)
  | W2 => inferInstanceAs (Decidable True)
  | W3 => inferInstanceAs (Decidable True)
  | W4 => inferInstanceAs (Decidable True)
  | K1 => inferInstanceAs (Decidable False)
  | K2 => inferInstanceAs (Decidable False)
  | topYukawa => inferInstanceAs (Decidable True)
  | bottomYukawa => inferInstanceAs (Decidable True)

/-!

### C.1. In super potential implies no conjugate fields

Been in the super potential implies that the term contains no conjugate fields.

-/

/-- The terms within the super-potential contain no conjugate fields. -/
lemma no_conjugate_in_toFieldLabel_of_inSuperPotential {T : PotentialTerm}
    (h : T.InSuperPotential) : FieldLabel.fiveMatter ∉ T.toFieldLabel ∧
    FieldLabel.fiveHd ∉ T.toFieldLabel ∧ FieldLabel.fiveBarHu ∉ T.toFieldLabel:= by
  revert T
  decide

/-!

## D. Degree of the potential term

We define the degree of a term in the potential to be the number of fields it contains.
The degree of all terms present is less than or equal to four.

-/

/-- The degree of a term in the potential. -/
def degree (T : PotentialTerm) : ℕ := T.toFieldLabel.length

lemma degree_le_four (T : PotentialTerm) : T.degree ≤ 4 := by
  cases T
  all_goals simp [toFieldLabel, degree]

/-!

## E. R-parity of the potential terms

Based on the R-parity of the underlying fields, we define the R-parity of each term
in the potential. We show that those terms which violate R-parity are exactly those
which are `β`, `Λ`, `W2`, `W4`, `K1`, or `K2`.

-/
/-- The R-parity of a term in the potential. -/
def RParity (T : PotentialTerm) : Fin 2 :=
  (T.toFieldLabel.map FieldLabel.RParity).foldl (· + ·) 0

/- The terms which violate R-parity are those with an odd-number of matter fields. -/
lemma violates_RParity_iff_mem {T : PotentialTerm} :
    T.RParity = 1 ↔ T ∈ ({β, Λ, W2, W4, K1, K2} : Finset PotentialTerm) := by
  revert T
  decide

/-!

## F. Terms which violate proton decay

We write down the finite set of terms which contribute to proton decay.
We do not at this point prove this result.

-/

/-- The finite set of terms in the superpotential and Kahler potential which are involved in
  proton decay.
- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
-/
def causeProtonDecay : Finset PotentialTerm :=
  {W1, Λ, W2, K1}

end PotentialTerm

end SU5

end SuperSymmetry
