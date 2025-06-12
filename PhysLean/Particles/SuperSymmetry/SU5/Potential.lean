/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.DeriveFintype
/-!

# Potential of the SU(5) + U(1) GUT

This file contains properties of the potential terms of the `SU(5)` SUSY.

The terms from the superpotential considered are (arXiv:0912.0853) :
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

The terms of the Kahler potential are (arXiv:0912.0853) :
`K ⊃ K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

## Important results

- `PotentialTerm` : The inductive type indexing the potential terms.
- `violateRParity` : The finite set of terms which violate R-parity.
  `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
- `causeProtonDecay` : The finite set of terms which contribute to proton decay.
  `W¹`, `W²`, `K¹`, `λ`

## Previous versions

A previous version of this code was replaced in PR #569.

-/

namespace SuperSymmetry

namespace SU5

/-- Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT. -/
inductive PotentialTerm
  /-- The term `μ 5Hu 5̄Hd`. -/
  | μ : PotentialTerm
  /-- The term `𝛽ᵢ 5̄Mⁱ5Hu`. -/
  | β : PotentialTerm
  /-- The term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`. -/
  | Λ : PotentialTerm
  /-- The term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` -/
  | W1 : PotentialTerm
  /-- The term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`. -/
  | W2 : PotentialTerm
  /-- The term `W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu`. -/
  | W3 : PotentialTerm
  /-- The term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`. -/
  | W4 : PotentialTerm
  /-- The term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`. -/
  | K1 : PotentialTerm
  /-- The term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` -/
  | K2 : PotentialTerm
  /-- The term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`. -/
  | topYukawa : PotentialTerm
  /-- The term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd`. -/
  | bottomYukawa : PotentialTerm
deriving DecidableEq, Fintype

/-- The types of field present in SU(5). -/
inductive FieldLabel
  | fiveBarHu
  | fiveHu
  | fiveBarHd
  | fiveHd
  | fiveBarMatter
  | fiveMatter
  | tenMatter

deriving DecidableEq, Fintype

/-- The R-Parity of a field, landding on `1` if it is in the non-trivial representation
  and `0` otherwise. -/
def FieldLabel.RParity : FieldLabel → Fin 2
  | fiveBarHu => 0
  | fiveHu => 0
  | fiveBarHd => 0
  | fiveHd => 0
  | fiveBarMatter => 1
  | fiveMatter => 1
  | tenMatter => 1

namespace PotentialTerm

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

instance :  (T : PotentialTerm) → Decidable (InSuperPotential T)
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

/-- The terms within the super-potential contain no conjugate fields. -/
lemma no_conjugate_in_toFieldLabel_of_inSuperPotential {T : PotentialTerm}
    (h : T.InSuperPotential) : FieldLabel.fiveMatter ∉ T.toFieldLabel ∧
    FieldLabel.fiveHd ∉ T.toFieldLabel ∧ FieldLabel.fiveBarHu ∉ T.toFieldLabel:= by
  revert T
  decide

/-- The degree of a term in the potential. -/
def degree (T : PotentialTerm) : ℕ := T.toFieldLabel.length

lemma degree_le_four (T : PotentialTerm) : T.degree ≤ 4 := by
  cases T
  all_goals simp [toFieldLabel, degree]

/-- The R-parity of a term in the potential. -/
def RParity (T : PotentialTerm) : Fin 2 :=
  (T.toFieldLabel.map FieldLabel.RParity).foldl (· + ·) 0

/- The terms which violate R-parity are those with an odd-number of matter fields. -/
lemma violates_RParity_iff_mem {T : PotentialTerm} :
    T.RParity = 1 ↔ T ∈ ({β, Λ, W2, W4, K1, K2} : Finset PotentialTerm) := by
  revert T
  decide

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
