/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
/-!

# The potential of the two Higgs doublet model

## i. Overview

In this file we give the potential of the two Higgs doublet model (2HDM) in Lean, and derive
properties thereof.

-/
namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

/-- The parameters of the Two Higgs doublet model potential.
  Following the convention of https://arxiv.org/pdf/1605.03237. -/
structure PotentialParameters where
  /-- The parameter corresponding to `m₁₁²` in the 2HDM potential. -/
  m₁₁2 : ℝ
  /-- The parameter corresponding to `m₂₂²` in the 2HDM potential. -/
  m₂₂2 : ℝ
  /-- The parameter corresponding to `m₁₂²` in the 2HDM potential. -/
  m₁₂2 : ℂ
  /-- The parameter corresponding to `λ₁` in the 2HDM potential. -/
  𝓵₁ : ℝ
  /-- The parameter corresponding to `λ₂` in the 2HDM potential. -/
  𝓵₂ : ℝ
  /-- The parameter corresponding to `λ₃` in the 2HDM potential. -/
  𝓵₃ : ℝ
  /-- The parameter corresponding to `λ₄` in the 2HDM potential. -/
  𝓵₄ : ℝ
  /-- The parameter corresponding to `λ₅` in the 2HDM potential. -/
  𝓵₅ : ℂ
  /-- The parameter corresponding to `λ₆` in the 2HDM potential. -/
  𝓵₆ : ℂ
  /-- The parameter corresponding to `λ₇` in the 2HDM potential. -/
  𝓵₇ : ℂ

namespace PotentialParameters

/-- A reparameterization of the parameters of the quadratic terms of the
  potential for use with the gramVector. -/
noncomputable def ξ (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
  match μ with
  | Sum.inl 0 => (P.m₁₁2 + P.m₂₂2) / 2
  | Sum.inr 0 => -Complex.re P.m₁₂2
  | Sum.inr 1 => Complex.im P.m₁₂2
  | Sum.inr 2 => (P.m₁₁2 - P.m₂₂2) / 2

/-- A reparameterization of the parameters of the quartic terms of the
  potential for use with the gramVector. -/
noncomputable def η (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl 0, Sum.inl 0 => (P.𝓵₁ + P.𝓵₂ + 2 * P.𝓵₃) / 8
  | Sum.inl 0, Sum.inr 0 => (P.𝓵₆.re + P.𝓵₇.re) * (1 / 4)
  | Sum.inl 0, Sum.inr 1 => (P.𝓵₆.im + P.𝓵₇.im) * (-1 / 4)
  | Sum.inl 0, Sum.inr 2 => (P.𝓵₁ - P.𝓵₂) * (1 / 8)
  | Sum.inr 0, Sum.inl 0 => (P.𝓵₆.re + P.𝓵₇.re) * (1 / 4)
  | Sum.inr 1, Sum.inl 0 => (P.𝓵₆.im + P.𝓵₇.im) * (-1 / 4)
  | Sum.inr 2, Sum.inl 0 => (P.𝓵₁ - P.𝓵₂) * (1 / 8)
  /-η_a_a-/
  | Sum.inr 0, Sum.inr 0 => (P.𝓵₅.re + P.𝓵₄) * (1 / 4)
  | Sum.inr 1, Sum.inr 1 => (-P.𝓵₅.re + P.𝓵₄) * (1 / 4)
  | Sum.inr 2, Sum.inr 2 => (P.𝓵₁ + P.𝓵₂ - 2 * P.𝓵₃) * (1 / 8)
  | Sum.inr 0, Sum.inr 1 => P.𝓵₅.im * (-1 / 4)
  | Sum.inr 2, Sum.inr 0 => (P.𝓵₆.re - P.𝓵₇.re) * (1 / 4)
  | Sum.inr 2, Sum.inr 1 => (P.𝓵₇.im - P.𝓵₆.im) * (1 / 4)
  | Sum.inr 1, Sum.inr 0 => P.𝓵₅.im * (-1 / 4)
  | Sum.inr 0, Sum.inr 2 => (P.𝓵₆.re - P.𝓵₇.re) * (1 / 4)
  | Sum.inr 1, Sum.inr 2 => (P.𝓵₇.im - P.𝓵₆.im) * (1 / 4)

lemma η_symm (P : PotentialParameters) (μ ν : Fin 1 ⊕ Fin 3) :
    P.η μ ν = P.η ν μ := by
  fin_cases μ <;> fin_cases ν <;> simp [η]

end PotentialParameters

open ComplexConjugate

/-- The mass term of the two Higgs doublet model potential. -/
noncomputable def massTerm (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  P.m₁₁2 * ‖H.Φ1‖ ^ 2 + P.m₂₂2 * ‖H.Φ2‖ ^ 2 -
  (P.m₁₂2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.m₁₂2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re

lemma massTerm_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    massTerm P H = ∑ μ, P.ξ μ * H.gramVector μ := by
  simp [massTerm, Fin.sum_univ_three, PotentialParameters.ξ, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  ring

@[simp]
lemma gaugeGroupI_smul_massTerm (g : StandardModel.GaugeGroupI) (P : PotentialParameters)
    (H : TwoHiggsDoublet) :
    massTerm P (g • H) = massTerm P H := by
  rw [massTerm_eq_gramVector, massTerm_eq_gramVector]
  simp

/-- The quartic term of the two Higgs doublet model potential. -/
noncomputable def quarticTerm (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  1/2 * P.𝓵₁ * ‖H.Φ1‖ ^ 2 * ‖H.Φ1‖ ^ 2 + 1/2 * P.𝓵₂ * ‖H.Φ2‖ ^ 2 * ‖H.Φ2‖ ^ 2
  + P.𝓵₃ * ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2
  + P.𝓵₄ * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
  + (1/2 * P.𝓵₅ * ⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + 1/2 * conj P.𝓵₅ * ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
  + (P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re
  + (P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re

lemma quarticTerm_𝓵₄_expand (P : PotentialParameters) (H : TwoHiggsDoublet) :
    H.quarticTerm P =
    1/2 * P.𝓵₁ * ‖H.Φ1‖ ^ 2 * ‖H.Φ1‖ ^ 2 + 1/2 * P.𝓵₂ * ‖H.Φ2‖ ^ 2 * ‖H.Φ2‖ ^ 2
    + P.𝓵₃ * ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2
    + P.𝓵₄ * (⟪H.Φ1, H.Φ2⟫_ℂ * ⟪H.Φ2, H.Φ1⟫_ℂ).re
    + (1/2 * P.𝓵₅ * ⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + 1/2 * conj P.𝓵₅ * ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
    + (P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re
    + (P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re := by
  simp [quarticTerm]
  left
  rw [Complex.sq_norm]
  rw [← Complex.mul_re]
  rw [← inner_conj_symm, ← Complex.normSq_eq_conj_mul_self]
  simp only [inner_conj_symm, Complex.ofReal_re]
  rw [← inner_conj_symm]
  exact Complex.normSq_conj ⟪H.Φ2, H.Φ1⟫_ℂ

lemma quarticTerm_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    quarticTerm P H = ∑ a, ∑ b, H.gramVector a * H.gramVector b * P.η a b := by
  simp [quarticTerm_𝓵₄_expand, Fin.sum_univ_three, PotentialParameters.η, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  ring_nf
  simp [← Complex.ofReal_pow, Complex.ofReal_re, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector]
  ring

@[simp]
lemma gaugeGroupI_smul_quarticTerm (g : StandardModel.GaugeGroupI) (P : PotentialParameters)
    (H : TwoHiggsDoublet) :
    quarticTerm P (g • H) = quarticTerm P H := by
  rw [quarticTerm_eq_gramVector, quarticTerm_eq_gramVector]
  simp

/-- The potential of the two Higgs doublet model. -/
noncomputable def potential (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  massTerm P H + quarticTerm P H

@[simp]
lemma gaugeGroupI_smul_potential (g : StandardModel.GaugeGroupI)
    (P : PotentialParameters) (H : TwoHiggsDoublet) :
    potential P (g • H) = potential P H := by
  rw [potential, potential]
  simp
/-!

## Boundedness of the potential

-/

/-- The condition that the potential is bounded from below. -/
def PotentialIsBounded (P : PotentialParameters) : Prop :=
  ∃ c : ℝ, ∀ H : TwoHiggsDoublet, c ≤ potential P H

lemma potentialIsBounded_iff_forall_gramVector (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∃ c : ℝ, ∀ K : Fin 1 ⊕ Fin 3 → ℝ, 0 ≤ K (Sum.inl 0) →
      ∑ μ : Fin 3, K (Sum.inr μ) ^ 2 ≤ K (Sum.inl 0) ^ 2 →
      c ≤ ∑ μ, P.ξ μ * K μ + ∑ a, ∑ b, K a * K b * P.η a b := by
  apply Iff.intro
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    intro v hv₀ hv_sum
    obtain ⟨H, hH⟩ := gramVector_surjective v hv₀ hv_sum
    apply (hc H).trans
    apply le_of_eq
    rw [potential, massTerm_eq_gramVector, quarticTerm_eq_gramVector]
    simp [hH]
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    intro H
    apply (hc H.gramVector (gramVector_inl_nonneg H) (gramVector_inr_sum_sq_le_inl H)).trans
    apply le_of_eq
    rw [potential, massTerm_eq_gramVector, quarticTerm_eq_gramVector]

lemma temp (a b : ℝ) : (∃ c ≤ 0, ∀ x, 0 < x → c ≤ a * x + b * x ^ 2) ↔
      0 ≤ b ∧ (b = 0 → 0 ≤ a) := by
  by_cases hb : b = 0
  /- The case of b = 0. -/
  · subst hb
    by_cases ha : a = 0
    · subst ha
      simp only [zero_mul, add_zero, le_refl, imp_self, and_self, iff_true]
      use 0
      simp
    · simp
      apply Iff.intro
      · rintro ⟨c, hc, hx⟩
        by_contra h2
        simp_all
        refine not_lt_of_ge (hx (c/a + 1) ?_) ?_
        · refine add_pos_of_nonneg_of_pos ?_ Real.zero_lt_one
          refine div_nonneg_of_nonpos hc (Std.le_of_lt h2)
        · field_simp
          linarith
      · rintro ha
        use 0
        simp
        intro x hx
        positivity
  /- The case of b ≠ 0. -/
  have h1 (x : ℝ) : a * x + b * x ^ 2 = b * (x + a / (2 * b)) ^ 2 - a ^ 2 / (4 * b) := by
    field_simp
    ring
  simp [hb]
  generalize a ^ 2 / (4 * b) = c1 at h1
  generalize a / (2 * b) = d at h1
  have hlt (c : ℝ) (x : ℝ) : (c ≤ a * x + b * x ^ 2) ↔ c + c1 ≤ b * (x + d) ^ 2 := by
    rw [h1]
    grind
  conv_lhs =>
    enter [1, c, 2, x]
    rw [hlt c]
  trans ∃ c, ∀ x, 0 < x → c ≤ b * (x + d) ^ 2
  · apply Iff.intro
    · rintro ⟨c, hc, hx⟩
      use c + c1
    · rintro ⟨c, hc⟩
      use min (c - c1) 0
      apply And.intro
      · exact min_le_right (c - c1) 0
      · exact fun x hx => le_trans (le_sub_iff_add_le.mp (min_le_left (c - c1) 0)) (hc x hx)
  refine Iff.symm <| (Ne.ge_iff_gt hb).trans <|
    Iff.intro (fun hb => ⟨0, fun x hx => by positivity⟩) <| fun ⟨c, h⟩ => ?_
  by_contra hn
  simp at hn
  suffices hs : ∀ x, x ^ 2 ≤ c/b by
    apply not_lt_of_ge (hs √(|c/b| + 1))
    rw [Real.sq_sqrt (by grind)]
    grind
  suffices hs : ∀ x, 0 < x → (x + d) ^ 2 ≤ c/b by
    refine fun x => le_trans ((Real.sqrt_le_left ?_).mp ?_) (hs (|x| + |d| + 1) (by positivity))
    · ring_nf
      rw [add_assoc, abs_add_eq_two_nsmul_posPart]
      positivity
    · rw [Real.sqrt_sq_eq_abs, add_assoc, add_assoc]
      simp only [le_add_iff_nonneg_right]
      ring_nf
      rw [add_assoc, abs_add_eq_two_nsmul_posPart]
      positivity
  intro x hx
  specialize h x hx
  refine (le_div_iff_of_neg (by grind)).mpr ?_
  ring_nf at h ⊢
  exact h




end TwoHiggsDoublet
