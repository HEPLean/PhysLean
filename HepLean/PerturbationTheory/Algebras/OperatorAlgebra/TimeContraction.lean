/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.NormalOrder
import HepLean.PerturbationTheory.Algebras.StateAlgebra.TimeOrder
/-!

# Time contractions

We define the state algebra of a field structure to be the free algebra
generated by the states.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}
open CrAnAlgebra
noncomputable section

namespace OperatorAlgebra

variable (𝓞 : 𝓕.OperatorAlgebra)
open FieldStatistic

def timeContract (φ ψ : 𝓕.States) : 𝓞.A :=
  𝓞.crAnF (ofStateAlgebra (StateAlgebra.timeOrder (StateAlgebra.ofState φ * StateAlgebra.ofState ψ))
  - normalOrder (ofState φ * ofState ψ))

lemma timeContract_eq_smul (φ ψ : 𝓕.States) : 𝓞.timeContract φ ψ =
    𝓞.crAnF (ofStateAlgebra (StateAlgebra.timeOrder
    (StateAlgebra.ofState φ * StateAlgebra.ofState ψ))
    + (-1 : ℂ) • normalOrder (ofState φ * ofState ψ)) := by rfl

lemma timeContract_of_timeOrderProp (φ ψ : 𝓕.States) (h : timeOrderProp φ ψ) :
    𝓞.timeContract φ ψ = 𝓞.crAnF (⟨anPart (StateAlgebra.ofState φ), ofState ψ⟩ₛca) := by
  conv_rhs =>
    rw [ofState_eq_crPart_add_anPart]
    rw [map_add, map_add, crAnF_superCommute_anPart_anPart, superCommute_anPart_crPart]
  simp only [timeContract, instCommGroup.eq_1, Algebra.smul_mul_assoc, add_zero]
  rw [StateAlgebra.timeOrder_ofState_ofState_ordered h]
  rw [normalOrder_ofState_mul_ofState]
  rw [map_mul]
  simp only [ofStateAlgebra_ofState, instCommGroup.eq_1]
  rw [ofState_eq_crPart_add_anPart, ofState_eq_crPart_add_anPart]
  simp only [mul_add, add_mul]
  abel_nf

lemma timeContract_of_not_timeOrderProp (φ ψ : 𝓕.States) (h : ¬ timeOrderProp φ ψ) :
    𝓞.timeContract φ ψ = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • 𝓞.timeContract ψ φ := by
  rw [timeContract_eq_smul]
  simp only [Int.reduceNeg, one_smul, map_add]
  rw [map_smul]
  rw [crAnF_normalOrder_ofState_ofState_swap]
  rw [StateAlgebra.timeOrder_ofState_ofState_not_ordered_eq_timeOrder h]
  rw [timeContract_eq_smul]
  simp only [FieldStatistic.instCommGroup.eq_1, map_smul, one_smul, map_add, smul_add]
  rw [smul_smul, smul_smul, mul_comm]

lemma timeContract_mem_center (φ ψ : 𝓕.States) : 𝓞.timeContract φ ψ ∈ Subalgebra.center ℂ 𝓞.A := by
  by_cases h : timeOrderProp φ ψ
  · rw [timeContract_of_timeOrderProp _ _ _ h]
    exact 𝓞.crAnF_superCommute_anPart_ofState_mem_center _ _
  · rw [timeContract_of_not_timeOrderProp _ _ _ h]
    refine Subalgebra.smul_mem (Subalgebra.center ℂ 𝓞.A) ?_ 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ)
    rw [timeContract_of_timeOrderProp]
    exact 𝓞.crAnF_superCommute_anPart_ofState_mem_center _ _
    have h1 := IsTotal.total (r := 𝓕.timeOrderProp) φ ψ
    simp_all

lemma timeContract_zero_of_diff_grade (φ ψ : 𝓕.States) (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) :
    𝓞.timeContract φ ψ = 0 := by
  by_cases h1 : timeOrderProp φ ψ
  · rw [timeContract_of_timeOrderProp _ _ _ h1]
    rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
    exact h
  · rw [timeContract_of_not_timeOrderProp _ _ _ h1]
    rw [timeContract_of_timeOrderProp _ _ _]
    rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
    simp only [instCommGroup.eq_1, smul_zero]
    exact h.symm
    have ht := IsTotal.total (r := 𝓕.timeOrderProp) φ ψ
    simp_all

end OperatorAlgebra

end
end FieldStruct
