/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickAlgebra.WickTerm
/-!

# Wick's theorem

This file contrains the time-dependent version of Wick's theorem
for lists of fields containing both fermions and bosons.

Wick's theorem is related to Isserlis' theorem in mathematics.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra
open WickAlgebra
open PhysLean.List
open WickContraction
open FieldStatistic

/-!

## Wick terms

-/

/-!

## Wick's theorem

-/

lemma wicks_theorem_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') :
    ∑ (φsΛ : WickContraction φs.length), φsΛ.wickTerm
    = ∑ (φs'Λ : WickContraction φs'.length), φs'Λ.wickTerm := by
  subst h
  rfl

/--
For a list `φs` of `𝓕.FieldOp`, Wick's theorem states that

`𝓣(φs) = ∑ φsΛ, φsΛ.wickTerm`

where the sum is over all Wick contraction `φsΛ`.

The proof is via induction on `φs`.
- The base case `φs = []` is handled by `wickTerm_empty_nil`.

The inductive step works as follows:

For the LHS:
1. `timeOrder_eq_maxTimeField_mul_finset` is used to write
  `𝓣(φ₀…φₙ)` as `𝓢(φᵢ,φ₀…φᵢ₋₁) • φᵢ * 𝓣(φ₀…φᵢ₋₁φᵢ₊₁φₙ)` where `φᵢ` is
  the maximal time field in `φ₀…φₙ`
2. The induction hypothesis is then used on `𝓣(φ₀…φᵢ₋₁φᵢ₊₁φₙ)` to expand it as a sum over
  Wick contractions of `φ₀…φᵢ₋₁φᵢ₊₁φₙ`.
3. This gives terms of the form `φᵢ * φsΛ.wickTerm` on which
  `mul_wickTerm_eq_sum` is used where `φsΛ` is a Wick contraction of `φ₀…φᵢ₋₁φᵢ₊₁φ`,
  to rewrite terms as a sum over optional uncontracted elements of `φsΛ`

On the LHS we now have a sum over Wick contractions `φsΛ` of `φ₀…φᵢ₋₁φᵢ₊₁φ` (from 2) and optional
uncontracted elements of `φsΛ` (from 3)

For the RHS:
1. The sum over Wick contractions of `φ₀…φₙ` on the RHS
  is split via `insertLift_sum` into a sum over Wick contractions `φsΛ` of `φ₀…φᵢ₋₁φᵢ₊₁φ` and
  sum over optional uncontracted elements of `φsΛ`.

Both sides are now sums over the same thing and their terms equate by the nature of the
lemmas used.
-/
theorem wicks_theorem : (φs : List 𝓕.FieldOp) → 𝓣(ofFieldOpList φs) =
    ∑ (φsΛ : WickContraction φs.length), φsΛ.wickTerm
  | [] => by
    rw [timeOrder_ofFieldOpList_nil]
    simp only [List.length_nil]
    rw [sum_WickContraction_nil]
    simp only [wickTerm_empty_nil]
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    conv_lhs => rw [timeOrder_eq_maxTimeField_mul_finset, ih, Finset.mul_sum]
    have h1 : φ :: φs =
        (eraseMaxTimeField φ φs).insertIdx (maxTimeFieldPosFin φ φs) (maxTimeField φ φs) := by
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeField, insertionSortMin, List.get_eq_getElem]
      erw [insertIdx_eraseIdx_fin]
    conv_rhs => rw [wicks_theorem_congr h1]
    conv_rhs => rw [insertLift_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_mul_assoc, mul_wickTerm_eq_sum
      (maxTimeField φ φs) (eraseMaxTimeField φ φs) (maxTimeFieldPosFin φ φs) c]
    trans (1 : ℂ) • ∑ k : Option { x // x ∈ c.uncontracted },
      (c ↩Λ (maxTimeField φ φs) (maxTimeFieldPosFin φ φs) k).wickTerm
    swap
    · simp
    rw [smul_smul]
    simp only [instCommGroup.eq_1, exchangeSign_mul_self, Nat.succ_eq_add_one, Fintype.sum_option,
      Finset.univ_eq_attach, smul_add, one_smul]
    · exact fun k => timeOrder_maxTimeField _ _ k
    · exact fun k => lt_maxTimeFieldPosFin_not_timeOrder _ _ k
termination_by φs => φs.length

end FieldSpecification
