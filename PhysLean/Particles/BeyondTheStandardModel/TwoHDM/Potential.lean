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

lemma potentialIsBounded_iff_forall_euclid (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∃ c, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 ≤ K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsBounded_iff_forall_gramVector]
  refine exists_congr (fun c => ?_)
  rw [Equiv.forall_congr_left (Equiv.sumArrowEquivProdArrow (Fin 1) (Fin 3) ℝ)]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Prod.forall, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  rw [Equiv.forall_congr_left <| Equiv.funUnique (Fin 1) ℝ]
  apply forall_congr'
  intro K0
  rw [Equiv.forall_congr_left <| (WithLp.equiv 2 ((i : Fin 3) → (fun x => ℝ) i)).symm]
  apply forall_congr'
  intro K
  simp only [Fin.isValue, Equiv.funUnique_symm_apply, uniqueElim_const, Equiv.symm_symm,
    WithLp.equiv_apply]
  refine imp_congr_right ?_
  intro hle
  simp only [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.isValue, Real.norm_eq_abs, sq_abs]
  refine imp_congr_right ?_
  intro hle'
  apply le_iff_le_of_cmp_eq_cmp
  congr 1
  simp [add_assoc, sq, Finset.sum_add_distrib]
  ring_nf
  simp [mul_assoc, ← Finset.mul_sum]
  conv_lhs =>
    enter [2, 2, 2, i]
    rw [PotentialParameters.η_symm]
  ring

lemma potentialIsBounded_iff_forall_euclid_lt (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsBounded_iff_forall_euclid]
  apply Iff.intro
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    apply And.intro
    · simpa using hc 0 0 (by simp) (by simp)
    · intro K0 K hk0 hle
      exact hc K0 K hk0.le hle
  · intro h
    obtain ⟨c, hc₀, hc⟩ := h
    use c
    intro K0 K hK0 hle
    by_cases hK0' : K0 = 0
    · subst hK0'
      simp_all
    · refine hc K0 K ?_ hle
      grind

/-!

## Mass term reduced

-/

/-- A function related to the mass term of the potential, used in the boundedness
  condition and equivalent to the term `J2` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def massTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.ξ (Sum.inl 0) + ∑ μ, P.ξ (Sum.inr μ) * k μ

lemma massTermReduced_lower_bound (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : P.ξ (Sum.inl 0) - √(∑ a, |P.ξ (Sum.inr a)| ^ 2) ≤ massTermReduced P k := by
  simp only [Fin.isValue, massTermReduced]
  have h1 (a b c : ℝ) (h :  - b ≤ c) : a - b ≤ a + c:= by grind
  apply h1
  let ξEuclid : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun a => P.ξ (Sum.inr a))
  trans - ‖ξEuclid‖
  · simp [@PiLp.norm_eq_of_L2, ξEuclid]
  trans - (‖k‖ * ‖ξEuclid‖)
  · simp
    simp at hk
    have ha (a b : ℝ) (h : a ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ b := by nlinarith
    apply ha
    · exact hk
    · exact norm_nonneg k
    · exact norm_nonneg ξEuclid
  trans - ‖⟪k, ξEuclid⟫_ℝ‖
  · simp
    exact abs_real_inner_le_norm k ξEuclid
  trans ⟪k, ξEuclid⟫_ℝ
  · simp
    grind
  simp [PiLp.inner_apply, ξEuclid]


/-!

## Quartic term reduced

-/

/-- A function related to the quartic term of the potential, used in the boundedness
  condition and equivalent to the term `J4` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def quarticTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.η (Sum.inl 0) (Sum.inl 0) + 2 * ∑ b, k b * P.η (Sum.inl 0) (Sum.inr b) +
  ∑ a, ∑ b, k a * k b * P.η (Sum.inr a) (Sum.inr b)

lemma potentialIsBounded_iff_exists_forall_forall_reduced (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ k : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖k‖ ^ 2 ≤ 1 → c ≤ K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k := by
  rw [potentialIsBounded_iff_forall_euclid_lt]
  refine exists_congr <| fun c => and_congr_right <| fun hc => forall_congr' <| fun K0 => ?_
  apply Iff.intro
  · refine fun h k hK0 k_le_one => (h (K0 • k) hK0 ?_).trans (le_of_eq ?_)
    · simp [norm_smul]
      rw [abs_of_nonneg (by positivity), mul_pow]
      nlinarith
    · simp [add_assoc, massTermReduced, quarticTermReduced]
      ring_nf
      simp [add_assoc, mul_assoc, ← Finset.mul_sum, sq]
      ring
  · intro h K hK0 hle
    refine (h ((1 / K0) • K) hK0 ?_).trans (le_of_eq ?_)
    · simp [norm_smul]
      field_simp
      rw [sq_le_sq] at hle
      simpa using hle
    · simp [add_assoc, massTermReduced, quarticTermReduced]
      ring_nf
      simp [add_assoc, mul_assoc, ← Finset.mul_sum, sq]
      field_simp
      ring_nf
      simp only [← Finset.sum_mul, Fin.isValue]
      field_simp
      ring

lemma quarticTermReduced_nonneg_of_potentialIsBounded (P : PotentialParameters)
    (hP : PotentialIsBounded P) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : 0 ≤ quarticTermReduced P k := by
  rw [potentialIsBounded_iff_exists_forall_forall_reduced] at hP
  suffices hp : ∀ (a b : ℝ), (∃ c ≤ 0, ∀ x, 0 < x → c ≤ a * x + b * x ^ 2) →
      0 ≤ b ∧ (b = 0 → 0 ≤ a) by
    obtain ⟨c, hc, h⟩ := hP
    refine (hp (massTermReduced P k) (quarticTermReduced P k) ⟨c, hc, ?_⟩).1
    grind
  intro a b
  by_cases hb : b = 0
  /- The case of b = 0. -/
  · subst hb
    by_cases ha : a = 0
    · subst ha
      simp
    · simp only [zero_mul, add_zero, le_refl, forall_const, true_and]
      rintro ⟨c, hc, hx⟩
      by_contra h2
      simp_all
      refine not_lt_of_ge (hx (c/a + 1) ?_) ?_
      · exact add_pos_of_nonneg_of_pos (div_nonneg_of_nonpos hc (Std.le_of_lt h2))
          Real.zero_lt_one
      · field_simp
        grind
  /- The case of b ≠ 0. -/
  have h1 (x : ℝ) : a * x + b * x ^ 2 = b * (x + a / (2 * b)) ^ 2 - a ^ 2 / (4 * b) := by grind
  generalize a ^ 2 / (4 * b) = c1 at h1
  generalize a / (2 * b) = d at h1
  simp only [hb, IsEmpty.forall_iff, and_true]
  have hlt (c : ℝ) (x : ℝ) : (c ≤ a * x + b * x ^ 2) ↔ c + c1 ≤ b * (x + d) ^ 2 := by grind
  conv_lhs => enter [1, c, 2, x]; rw [hlt c]
  trans ∃ c, ∀ x, 0 < x → c ≤ b * (x + d) ^ 2
  · rintro ⟨c, hc, hx⟩
    use c + c1
  rintro ⟨c, hc⟩
  by_contra hn
  suffices hs : ∀ x, x ^ 2 ≤ c/b from not_lt_of_ge (hs √(|c/b| + 1)) (by grind)
  suffices hs : ∀ x, 0 < x → (x + d) ^ 2 ≤ c/b from
    fun x => le_trans ((Real.sqrt_le_left (by grind)).mp
      (by grind [Real.sqrt_sq_eq_abs])) (hs (|x| + |d| + 1) (by positivity))
  exact fun x hx => (le_div_iff_of_neg (by grind)).mpr (by grind)

lemma potentialIsBounded_iff_exists_forall_reduced (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∃ c, 0 ≤ c ∧ ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
      0 ≤ quarticTermReduced P k ∧
      (massTermReduced P k < 0 →
      massTermReduced P k ^ 2 ≤ 4 * quarticTermReduced P k * c)  := by
  rw [potentialIsBounded_iff_exists_forall_forall_reduced]
  refine Iff.intro (fun ⟨c, hc, h⟩ => ⟨-c, by grind,  fun k hk => ?_⟩)
    (fun ⟨c, hc, h⟩ => ⟨-c, by grind,  fun K0 k hk0 hk => ?_⟩)
  · have hJ4_nonneg : 0 ≤ quarticTermReduced P k := by
      refine quarticTermReduced_nonneg_of_potentialIsBounded P ?_ k hk
      rw [potentialIsBounded_iff_exists_forall_forall_reduced]
      exact ⟨c, hc, h⟩
    have h0 : ∀ K0, 0 < K0 →  c ≤ K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k :=  fun K0 a =>  h K0 k a hk
    clear h
    generalize massTermReduced P k = j2 at *
    generalize quarticTermReduced P k = j4 at *
    by_cases j4_zero : j4 = 0
    · subst j4_zero
      simp_all
      intro hj2
      by_contra hn
      specialize h0 ((c - 1) / j2) <| by
        refine div_pos_iff.mpr (Or.inr ?_)
        grind
      field_simp at h0
      linarith
    · have hsq (K0 : ℝ) : K0 * j2 + K0 ^ 2 * j4 =
            j4 * (K0 + j2 / (2 * j4)) ^ 2 - j2 ^ 2 / (4 * j4) := by
        grind
      have hj_pos : 0 < j4 := by grind
      apply And.intro
      · grind
      · intro j2_neg
        conv at h0 => enter [2]; rw [hsq]
        specialize h0 ( - j2 / (2 * j4)) <| by
          field_simp
          grind
        ring_nf at h0
        field_simp at h0
        grind
  · specialize h k hk
    generalize massTermReduced P k = j2 at *
    generalize quarticTermReduced P k = j4 at *
    by_cases hJ4 : j4 = 0
    · subst j4
      simp_all
      trans 0
      · grind
      · by_cases hJ2 : j2 = 0
        · simp_all
        · simp_all
    · have hJ4_pos : 0 < j4 := by grind
      have h0 : K0 * j2 + K0 ^ 2 * j4 = j4 * (K0 + j2 / (2 * j4)) ^ 2 - j2 ^ 2 / (4 * j4) := by
          grind
      rw [h0]
      by_cases hJ2_neg : j2 < 0
      · trans j4 * (K0 + j2 / (2 * j4)) ^ 2 - c
        · nlinarith
        · field_simp
          grind
      · refine neg_le_sub_iff_le_add.mpr ?_
        trans j4 * (K0 + j2 / (2 * j4)) ^ 2
        · nlinarith
        · grind

@[sorryful]
lemma potentialIsBounded_iff_forall_reduced (P : PotentialParameters) :
    PotentialIsBounded P ↔ ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
      0 ≤ quarticTermReduced P k ∧ (quarticTermReduced P k = 0 → 0 ≤ massTermReduced P k)  := by
  sorry

end TwoHiggsDoublet
