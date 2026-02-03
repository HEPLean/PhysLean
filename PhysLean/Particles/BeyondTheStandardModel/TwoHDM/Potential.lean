/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
/-!

# The potential of the Two Higgs doublet model

## i. Overview

In this module we give the define the parameters of the 2HDM potential.


-/
namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

/-!

## A. The parameters of the potential

We define a type for the parameters of the Higgs potential in the 2HDM.

We follow the convetion of `1605.03237`, which is highlighted in the explicit construction
of the potential itself.

We relate these parameters to the `ξ` and `η` parameters used in the gram vector formalism
given in arXiv:hep-ph/0605184.

-/

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

/-!

### A.1. The potential parameters corresponding to zero

We define an instance of `Zero` for the potential parameters, corresponding to all
parameters being zero, and therefore the potential itself being zero.

-/

instance : Zero PotentialParameters where
  zero :=
    { m₁₁2 := 0
      m₂₂2 := 0
      m₁₂2 := 0
      𝓵₁ := 0
      𝓵₂ := 0
      𝓵₃ := 0
      𝓵₄ := 0
      𝓵₅ := 0
      𝓵₆ := 0
      𝓵₇ := 0 }

@[simp] lemma zero_m₁₁2 : (0 : PotentialParameters).m₁₁2 = 0 := rfl

@[simp] lemma zero_m₂₂2 : (0 : PotentialParameters).m₂₂2 = 0 := rfl

@[simp] lemma zero_m₁₂2 : (0 : PotentialParameters).m₁₂2 = 0 := rfl

@[simp] lemma zero_𝓵₁ : (0 : PotentialParameters).𝓵₁ = 0 := rfl

@[simp] lemma zero_𝓵₂ : (0 : PotentialParameters).𝓵₂ = 0 := rfl

@[simp] lemma zero_𝓵₃ : (0 : PotentialParameters).𝓵₃ = 0 := rfl

@[simp] lemma zero_𝓵₄ : (0 : PotentialParameters).𝓵₄ = 0 := rfl

@[simp] lemma zero_𝓵₅ : (0 : PotentialParameters).𝓵₅ = 0 := rfl

@[simp] lemma zero_𝓵₆ : (0 : PotentialParameters).𝓵₆ = 0 := rfl

@[simp] lemma zero_𝓵₇ : (0 : PotentialParameters).𝓵₇ = 0 := rfl


/-!

### A.2. Gram parameters

A reparameterization of the potential parameters corresponding to `ξ` and `η` in
arXiv:hep-ph/0605184.

-/

/-- A reparameterization of the parameters of the quadratic terms of the
  potential for use with the gramVector. -/
noncomputable def ξ (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
  match μ with
  | Sum.inl 0 => (P.m₁₁2 + P.m₂₂2) / 2
  | Sum.inr 0 => -Complex.re P.m₁₂2
  | Sum.inr 1 => Complex.im P.m₁₂2
  | Sum.inr 2 => (P.m₁₁2 - P.m₂₂2) / 2

@[simp]
lemma ξ_zero : (0 : PotentialParameters).ξ = 0 := by
  ext μ
  fin_cases μ <;> simp [ξ]

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

@[simp]
lemma η_zero : (0 : PotentialParameters).η = 0 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [η]

/-!

### A.3. Specific cases


-/

/-- An example of potential parameters that serve as a counterexample to the stability
  condition given in arXiv:hep-ph/0605184. -/
def stabilityCounterExample : PotentialParameters := {(0 : PotentialParameters) with
    m₁₂2 := Complex.I
    𝓵₁ := 2
    𝓵₂ := 2
    𝓵₃ := 2
    𝓵₄ := 2
    𝓵₅ := 2
    𝓵₆ := -2
    𝓵₇ := -2}

end PotentialParameters

open ComplexConjugate

/-!

## B. The mass term

We define the mass term of the potential, write it in terms of the gram vector,
and prove that it is gauge invariant.

-/

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

@[simp]
lemma massTerm_zero : massTerm 0 = 0 := by
  ext H
  simp [massTerm]

lemma massTerm_stabilityCounterExample (H : TwoHiggsDoublet) :
    massTerm PotentialParameters.stabilityCounterExample H =
    2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im := by
  simp [massTerm, PotentialParameters.stabilityCounterExample]
  rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
  rw [Complex.conj_im]
  ring_nf

/-!

## C. The quartic term

We define the quartic term of the potential, write it in terms of the gram vector,
and prove that it is gauge invariant.

-/

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

@[simp]
lemma quarticTerm_zero : quarticTerm 0 = 0 := by
  ext H
  simp [quarticTerm]

lemma quarticTerm_stabilityCounterExample (H : TwoHiggsDoublet) :
    quarticTerm .stabilityCounterExample H = ‖H.Φ1 - H.Φ2‖ ^ 4 := by
  /- Proof by calculation. -/
  calc _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) ^ 2
    + 2 * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
    + (⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
     - 2 * (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) * ((⟪H.Φ1, H.Φ2⟫_ℂ).re + (⟪H.Φ2, H.Φ1⟫_ℂ).re) := by
        simp [quarticTerm, PotentialParameters.stabilityCounterExample, Complex.add_re,
          ← Complex.ofReal_pow]
        ring
      _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) ^ 2
      + 4 * (⟪H.Φ1, H.Φ2⟫_ℂ).re ^ 2
      - 2 * (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) * ((⟪H.Φ1, H.Φ2⟫_ℂ).re + (⟪H.Φ2, H.Φ1⟫_ℂ).re):= by
        have h1 : 2 * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
            + (⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re = 4 * (⟪H.Φ1, H.Φ2⟫_ℂ).re ^ 2 := by
          rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
          generalize ⟪H.Φ1, H.Φ2⟫_ℂ = z
          have hz : z = z.re + z.im  * Complex.I := by exact Eq.symm (Complex.re_add_im z)
          generalize z.re = x at hz
          generalize z.im = y at hz
          subst hz
          have h0 : ‖↑x + ↑y * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
            rw [Complex.norm_add_mul_I, Real.sq_sqrt]
            positivity
          rw [h0]
          simp [Complex.add_re, sq]
          ring
        rw [← h1]
        ring
      _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 - 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re) ^ 2 := by
        rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
        rw [Complex.conj_re]
        ring
      _ = (‖H.Φ1 - H.Φ2‖ ^ 2) ^ 2 := by
        congr
        have h1 (v : HiggsVec): ‖v‖ ^ 2 =  (⟪v, v⟫_ℂ).re := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [← Complex.ofReal_pow]
        rw [h1, h1, h1]
        simp only [inner_sub_right, inner_sub_left, Complex.sub_re]
        rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
        rw [Complex.conj_re]
        ring
      _ = ‖H.Φ1 - H.Φ2‖ ^ 4 := by ring



lemma massTerm_zero_of_quarticTerm_zero_stabilityCounterExample (H : TwoHiggsDoublet)
    (h : quarticTerm .stabilityCounterExample H = 0) :
    massTerm .stabilityCounterExample H = 0 := by
  rw [quarticTerm_stabilityCounterExample] at h
  rw [massTerm_stabilityCounterExample]
  simp at h
  have h1 : H.Φ1 = H.Φ2 := by grind
  simp [← Complex.ofReal_pow, h1]


/-!

## D. The full potential

We define the full potential as the sum of the mass and quartic terms,
and prove that it is gauge invariant.

-/

/-- The potential of the two Higgs doublet model. -/
noncomputable def potential (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  massTerm P H + quarticTerm P H

@[simp]
lemma gaugeGroupI_smul_potential (g : StandardModel.GaugeGroupI)
    (P : PotentialParameters) (H : TwoHiggsDoublet) :
    potential P (g • H) = potential P H := by
  rw [potential, potential]
  simp

@[simp]
lemma potential_zero : potential 0 = 0 := by
  ext H
  simp [potential]

lemma potential_stabilityCounterExample (H : TwoHiggsDoublet) :
    potential .stabilityCounterExample H = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im + ‖H.Φ1 - H.Φ2‖ ^ 4 := by
  simp [potential, massTerm_stabilityCounterExample, quarticTerm_stabilityCounterExample]

/-!

## E. Stability of the potential

-/

/-!

## E.1. The stability condition

We define the condition that the potential is stable, that is, bounded from below.

-/

/-- The condition that the potential is stable. -/
def PotentialIsStable (P : PotentialParameters) : Prop :=
  ∃ c : ℝ, ∀ H : TwoHiggsDoublet, c ≤ potential P H

/-!

## E.2. The reduced mass term

The reduced mass term is a function that helps express the stability condition.
It is the function `J2` in https://arxiv.org/abs/hep-ph/0605184.

-/

/-- A function related to the mass term of the potential, used in the stableness
  condition and equivalent to the term `J2` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def massTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.ξ (Sum.inl 0) + ∑ μ, P.ξ (Sum.inr μ) * k μ

lemma massTermReduced_lower_bound (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : P.ξ (Sum.inl 0) - √(∑ a, |P.ξ (Sum.inr a)| ^ 2) ≤ massTermReduced P k := by
  simp only [Fin.isValue, massTermReduced]
  have h1 (a b c : ℝ) (h : - b ≤ c) : a - b ≤ a + c:= by grind
  apply h1
  let ξEuclid : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun a => P.ξ (Sum.inr a))
  trans - ‖ξEuclid‖
  · simp [PiLp.norm_eq_of_L2, ξEuclid]
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

@[simp]
lemma massTermReduced_zero : massTermReduced 0 = 0 := by
  ext k
  simp [massTermReduced]

lemma massTermReduced_stabilityCounterExample (k : EuclideanSpace ℝ (Fin 3)) :
    massTermReduced .stabilityCounterExample k = k 1 := by
 simp [massTermReduced, PotentialParameters.ξ, Fin.isValue,
  PotentialParameters.stabilityCounterExample, Fin.sum_univ_three]

/-!

## E.2. The reduced quartic term

The reduced quartic term is a function that helps express the stability condition.
It is the function `J4` in https://arxiv.org/abs/hep-ph/0605184.

-/

/-- A function related to the quartic term of the potential, used in the stableness
  condition and equivalent to the term `J4` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def quarticTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.η (Sum.inl 0) (Sum.inl 0) + 2 * ∑ b, k b * P.η (Sum.inl 0) (Sum.inr b) +
  ∑ a, ∑ b, k a * k b * P.η (Sum.inr a) (Sum.inr b)

@[simp]
lemma quarticTermReduced_zero : quarticTermReduced 0 = 0 := by
  ext k
  simp [quarticTermReduced]

lemma quarticTermReduced_stabilityCounterExample (k : EuclideanSpace ℝ (Fin 3)) :
    quarticTermReduced .stabilityCounterExample k = (1 - k 0) ^ 2 := by
  simp [quarticTermReduced, PotentialParameters.η, Fin.isValue,
    PotentialParameters.stabilityCounterExample, Fin.sum_univ_three]
  ring

lemma quarticTermReduced_stabilityCounterExample_nonneg (k : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ quarticTermReduced .stabilityCounterExample k := by
  rw [quarticTermReduced_stabilityCounterExample]
  apply sq_nonneg

/-!

## E.3. Stability in terms of the gram vectors

We give some necessary and sufficent conditions for the potential to be stable
in terms of the gram vectors.

This follows the analysis in https://arxiv.org/abs/hep-ph/0605184.

We also give some necessary conditions.

-/

lemma potentialIsStable_iff_forall_gramVector (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c : ℝ, ∀ K : Fin 1 ⊕ Fin 3 → ℝ, 0 ≤ K (Sum.inl 0) →
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

lemma potentialIsStable_iff_forall_euclid (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 ≤ K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsStable_iff_forall_gramVector]
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

lemma potentialIsStable_iff_forall_euclid_lt (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsStable_iff_forall_euclid]
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

lemma potentialIsStable_iff_exists_forall_forall_reduced (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ k : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖k‖ ^ 2 ≤ 1 → c ≤ K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k := by
  rw [potentialIsStable_iff_forall_euclid_lt]
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

lemma quarticTermReduced_nonneg_of_potentialIsStable (P : PotentialParameters)
    (hP : PotentialIsStable P) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : 0 ≤ quarticTermReduced P k := by
  rw [potentialIsStable_iff_exists_forall_forall_reduced] at hP
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

lemma potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c, 0 ≤ c ∧ ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
      0 ≤ quarticTermReduced P k ∧
      (massTermReduced P k < 0 →
      massTermReduced P k ^ 2 ≤ 4 * quarticTermReduced P k * c) := by
  rw [potentialIsStable_iff_exists_forall_forall_reduced]
  refine Iff.intro (fun ⟨c, hc, h⟩ => ⟨-c, by grind, fun k hk => ?_⟩)
    (fun ⟨c, hc, h⟩ => ⟨-c, by grind, fun K0 k hk0 hk => ?_⟩)
  · have hJ4_nonneg : 0 ≤ quarticTermReduced P k := by
      refine quarticTermReduced_nonneg_of_potentialIsStable P ?_ k hk
      rw [potentialIsStable_iff_exists_forall_forall_reduced]
      exact ⟨c, hc, h⟩
    have h0 : ∀ K0, 0 < K0 → c ≤ K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k :=
      fun K0 a => h K0 k a hk
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
        specialize h0 (- j2 / (2 * j4)) <| by
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

lemma massTermReduced_pos_of_quarticTermReduced_zero_potentialIsStable (P : PotentialParameters)
    (hP : PotentialIsStable P) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) (hq : quarticTermReduced P k = 0) : 0 ≤ massTermReduced P k := by
  rw [potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced] at hP
  obtain ⟨c, hc₀, hc⟩ := hP
  specialize hc k hk
  rw [hq] at hc
  simp only [le_refl, mul_zero, zero_mul, sq_nonpos_iff, true_and] at hc
  generalize massTermReduced P k = j2 at *
  grind

/-!

### E.4. Strong stability implies stability

Stability in terms of the positivity of the quartic term, implies that the whole
potential is stable.

-/

/-- The potential is stable if it is strongly stable, i.e. its quartic term is always positive.
    The proof of this result relies on the compactness of the closed unit ball in
    `EuclideanSpace ℝ (Fin 3)`, and the `extreme value theorem`. -/
lemma potentialIsStable_of_strong (P : PotentialParameters)
    (h : ∀ k, ‖k‖ ^ 2 ≤ 1 → 0 < quarticTermReduced P k) :
    PotentialIsStable P := by
  rw [potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced]
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
  have S_isCompact : IsCompact S :=  isCompact_closedBall 0 1
  have S_nonEmpty : S.Nonempty := ⟨0, by simp [S]⟩
  obtain ⟨kmax, kmax_S, kmax_isMax⟩ := IsCompact.exists_isMaxOn
    (isCompact_closedBall 0 1) S_nonEmpty
    (f := fun k => (massTermReduced P k ^ 2) / (4 * quarticTermReduced P k)) <| by
    apply ContinuousOn.div₀
    · apply Continuous.continuousOn
      simp only [massTermReduced, Fin.isValue]
      fun_prop
    · apply Continuous.continuousOn
      simp only [quarticTermReduced, Fin.isValue]
      fun_prop
    · intro x hx
      specialize h x (by simpa using hx)
      linarith
  use (massTermReduced P kmax) ^ 2 / (4 * quarticTermReduced P kmax)
  apply And.intro
  · refine (le_div_iff₀ ?_).mpr ?_
    · specialize h kmax (by simpa using kmax_S)
      linarith
    · simp only [zero_mul]
      exact sq_nonneg (massTermReduced P kmax)
  · intro k hk
    apply And.intro
    · specialize h k hk
      linarith
    · intro hq
      rw [isMaxOn_iff] at kmax_isMax
      refine (div_le_iff₀' ?_).mp (kmax_isMax k (by simpa using hk))
      grind

/-!

### E.5. Properties of `stabilityCounterExample`

-/

/-- The potential `stabilityCounterExample` is not stable.-/
lemma stabilityCounterExample_not_potentialIsStable :
    ¬ PotentialIsStable .stabilityCounterExample := by
  /- Changing the goal to an existence. -/
    rw [potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced]
    by_contra ⟨c, c_pos, hc⟩
    suffices h_exists : ∃ k, ‖k‖ ^ 2 ≤ 1 ∧
        0 ≤ quarticTermReduced .stabilityCounterExample k ∧
        massTermReduced .stabilityCounterExample k < 0 ∧
        4 * c * quarticTermReduced .stabilityCounterExample k <
        (massTermReduced .stabilityCounterExample k) ^ 2 by
      obtain ⟨k, hk_norm, hk_quartic, hk_mass_neg, hk_mass⟩ := h_exists
      specialize hc k hk_norm
      have := hc.2 hk_mass_neg
      linarith
    /- A general sequence of points. -/
    let kt (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
      !₂[(1 : ℝ), 0, 0] - t • !₂[Real.sin t, Real.cos t, 0]
    have kt_normSq (t : ℝ) : ‖kt t‖ ^ 2 = 1 + t ^ 2 - 2 * t * Real.sin t := by
      simp [kt, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
      trans 1 - t * Real.sin t * 2 + t ^ 2 * (Real.sin t ^ 2 +Real.cos t ^ 2)
      · ring
      rw [Real.sin_sq_add_cos_sq]
      ring
    have kt_normSq_le_one (t : ℝ) (ht : 0 ≤ t) (htu : t ≤ Real.pi / 2) : ‖kt t‖ ^ 2 ≤ 1 := by
      rw [kt_normSq, tsub_le_iff_right, add_le_add_iff_left]
      trans 2 * t * (2 / Real.pi * t)
      · ring_nf
        rw [mul_assoc]
        apply le_mul_of_one_le_right
        · positivity
        · field_simp
          exact Real.pi_le_four
      · nlinarith [Real.mul_le_sin ht htu]
    have kt_quarticTermReduced (t : ℝ) :
        quarticTermReduced .stabilityCounterExample (kt t) = t ^ 2 * Real.sin t ^ 2 := by
      simp only [quarticTermReduced_stabilityCounterExample, Fin.isValue, PiLp.sub_apply, Matrix.cons_val_zero,
        PiLp.smul_apply, smul_eq_mul, sub_sub_cancel, kt]
      ring
    have kt_massTermReduced (t : ℝ) : massTermReduced .stabilityCounterExample (kt t) = - t * Real.cos t := by
      simp [massTermReduced_stabilityCounterExample, kt]
    have kt_massTermReduced_neg (t : ℝ) (ht : 0 < t) (htu : t < Real.pi / 2) :
        massTermReduced .stabilityCounterExample (kt t) < 0 := by
      rw [kt_massTermReduced, neg_mul, Left.neg_neg_iff]
      refine (mul_pos_iff_of_pos_right (Real.cos_pos_of_mem_Ioo <| Set.mem_Ioo.mp ⟨?_, htu⟩)).mpr ht
      linarith
    /- A specific point invalidating the boundedness. -/
    use kt (Real.arctan (2 * Real.sqrt (c + 1))⁻¹)
    refine ⟨?_, ?_, ?_, ?_⟩
    · /- Norm le 1. -/
      apply kt_normSq_le_one
      · simp
      · exact le_of_lt <| Real.arctan_lt_pi_div_two _
    · /- Quadratic term non negative. -/
      exact quarticTermReduced_stabilityCounterExample_nonneg (kt (Real.arctan (2 * √(c + 1))⁻¹))
    · /- Mass term negative. -/
      apply kt_massTermReduced_neg
      · simp only [mul_inv_rev, Real.arctan_pos, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right,
        Real.sqrt_pos]
        linarith
      · apply Real.arctan_lt_pi_div_two
    · /- The inequality -/
      rw [kt_quarticTermReduced, kt_massTermReduced]
      simp [mul_pow]
      refine (mul_inv_lt_iff₀ ?_).mp ?_
      · refine pow_two_pos_of_ne_zero (ne_of_gt ?_)
        exact Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo ((√(c + 1))⁻¹ * 2⁻¹))
      apply lt_of_eq_of_lt (b :=  4 * c * (Real.arctan ((√(c + 1))⁻¹ * 2⁻¹) ^ 2 *
          Real.tan (Real.arctan ((√(c + 1))⁻¹ * 2⁻¹)) ^ 2))
      · rw [Real.tan_eq_sin_div_cos]
        field_simp
      · rw [Real.tan_arctan]
        simp [mul_pow]
        rw [Real.sq_sqrt (by positivity)]
        field_simp
        grind

/-!

### E.6. Showing step in hep-ph/0605184 is invalid

-/

/-- A lemma invalidating the step in https://arxiv.org/pdf/hep-ph/0605184 leading to
  equation (4.4). -/
lemma forall_reduced_exists_not_potentialIsStable :
    ∃ P, ¬ PotentialIsStable P ∧ (∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
    0 ≤ quarticTermReduced P k ∧ (quarticTermReduced P k = 0 → 0 ≤ massTermReduced P k)) := by
  /- Construction of the explicit counter example.
    The reason that this counter example works is that:
    - There is a zero of the quartic term `z` on the boundary.
    - The quartic term is equal to `((k - z) · z)²`, as `k - z` approaches orthogonal to `z`,
      this becomes small on two accounts: the abs of `k - z` has to become small as `z` is on
      the boundary, and the angle between `k - z` and `z` also becomes small.
    - The mass term is of the form `-(k - z) · w` for some `w` orthogonal to `z`, so as `k - z`
      approaches orthogonal to `z`, the mass term becomes small only on the account that the abs of
      `k - z` becomes small. -/
  use .stabilityCounterExample
  apply And.intro
  /- The condition that P is not stable. -/
  · exact stabilityCounterExample_not_potentialIsStable
  /- The condition on the reduced terms. -/
  · refine fun k hk =>  And.intro (quarticTermReduced_stabilityCounterExample_nonneg k) (fun hq => ?_)
    simp [quarticTermReduced_stabilityCounterExample] at hq
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three,
      Fin.isValue] at hk
    have hk1 : k 1 = 0 := by nlinarith
    rw [massTermReduced_stabilityCounterExample, hk1]

end TwoHiggsDoublet
