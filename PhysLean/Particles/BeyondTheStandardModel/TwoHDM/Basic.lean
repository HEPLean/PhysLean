/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import PhysLean.Relativity.PauliMatrices.SelfAdjoint
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

-/

open StandardModel

/-!

## A. The configuration space

-/

/-- The configuration space of the two Higgs doublet model.
  In otherwords, the underlying vector space associated with the model. -/
structure TwoHiggsDoublet where
  /-- The first Higgs doublet. -/
  Φ1 : HiggsVec
  /-- The second Higgs doublet. -/
  Φ2 : HiggsVec

namespace TwoHiggsDoublet

open InnerProductSpace

@[ext]
lemma ext_of_fst_snd {H1 H2 : TwoHiggsDoublet}
    (h1 : H1.Φ1 = H2.Φ1) (h2 : H1.Φ2 = H2.Φ2) : H1 = H2 := by
  cases H1
  cases H2
  congr
/-!

## B. Gauge group actions

-/

noncomputable instance : SMul StandardModel.GaugeGroupI TwoHiggsDoublet where
  smul g H :=
    { Φ1 := g • H.Φ1
      Φ2 := g • H.Φ2 }

@[simp]
lemma gaugeGroupI_smul_fst (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ1 = g • H.Φ1 := rfl

@[simp]
lemma gaugeGroupI_smul_snd (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ2 = g • H.Φ2 := rfl

noncomputable instance : MulAction StandardModel.GaugeGroupI TwoHiggsDoublet where
  one_smul H := by
    ext <;> simp
  mul_smul g1 g2 H := by
    ext <;> simp [mul_smul]

/-!

## C. The Gram matrix

-/

/-- The Gram matrix of the two Higgs doublet.
  This matrix is used in https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def gramMatrix (H : TwoHiggsDoublet) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪H.Φ1, H.Φ1⟫_ℂ, ⟪H.Φ2, H.Φ1⟫_ℂ; ⟪H.Φ1, H.Φ2⟫_ℂ, ⟪H.Φ2, H.Φ2⟫_ℂ]

lemma gramMatrix_selfAdjoint (H : TwoHiggsDoublet) :
    IsSelfAdjoint (gramMatrix H) := by
  rw [gramMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inner_conj_symm]

lemma eq_fst_norm_of_eq_gramMatrix {H1 H2 : TwoHiggsDoublet}
    (h : H1.gramMatrix = H2.gramMatrix) : ‖H1.Φ1‖ = ‖H2.Φ1‖ := by
  rw [gramMatrix, gramMatrix] at h
  have h1 := congrArg (fun x => x 0 0) h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Fin.isValue] at h1
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · rw [← RCLike.ofReal_neg] at h1
    have hnorm1 : 0 ≤ ‖H1.Φ1‖ := norm_nonneg H1.Φ1
    have hnorm2 : 0 ≤ ‖H2.Φ1‖ := norm_nonneg H2.Φ1
    have hl : ‖H1.Φ1‖ = (-‖H2.Φ1‖) :=  Eq.symm ((fun {z w} => Complex.ofReal_inj.mp) (id (Eq.symm h1)))
    grind

lemma eq_snd_norm_of_eq_gramMatrix {H1 H2 : TwoHiggsDoublet}
    (h : H1.gramMatrix = H2.gramMatrix) : ‖H1.Φ2‖ = ‖H2.Φ2‖ := by
  rw [gramMatrix, gramMatrix] at h
  have h1 := congrArg (fun x => x 1 1) h
  simp  [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Fin.isValue] at h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · erw [← RCLike.ofReal_neg] at h1
    have hnorm1 : 0 ≤ ‖H1.Φ2‖ := norm_nonneg H1.Φ2
    have hnorm2 : 0 ≤ ‖H2.Φ2‖ := norm_nonneg H2.Φ2
    have hl : ‖H1.Φ2‖ = (-‖H2.Φ2‖) :=  Eq.symm ((fun {z w} => Complex.ofReal_inj.mp) (id (Eq.symm h1)))
    grind

@[simp]
lemma gaugeGroupI_smul_gramMatrix (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).gramMatrix = H.gramMatrix := by
  rw [gramMatrix, gramMatrix, gaugeGroupI_smul_fst, gaugeGroupI_smul_snd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma gramMatrix_det_eq (H : TwoHiggsDoublet) :
    H.gramMatrix.det = ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
  rw [gramMatrix, Matrix.det_fin_two]
  simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    sub_right_inj]
  rw [← Complex.conj_mul']
  simp only [inner_conj_symm]

lemma gramMatrix_det_eq_real (H : TwoHiggsDoublet) :
    H.gramMatrix.det.re = ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
  rw [gramMatrix_det_eq]
  simp [← Complex.ofReal_pow, Complex.ofReal_im]

lemma gramMatrix_det_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramMatrix.det.re := by
  rw [gramMatrix_det_eq_real]
  simp only [sub_nonneg]
  convert inner_mul_inner_self_le (𝕜 := ℂ) H.Φ1 H.Φ2
  · simp [sq, norm_inner_symm]
  · exact norm_sq_eq_re_inner H.Φ1
  · exact norm_sq_eq_re_inner H.Φ2

lemma gramMatrix_tr_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramMatrix.trace.re := by
  rw [gramMatrix, Matrix.trace_fin_two]
  simp
  apply add_nonneg
  · rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg ‖H.Φ1‖
  · rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg ‖H.Φ2‖

lemma gaugeGroupI_exists_fst_eq {H : TwoHiggsDoublet} (h1 : H.Φ1 ≠ 0) :
    ∃ g : StandardModel.GaugeGroupI,
      g • H.Φ1 = (!₂[‖H.Φ1‖, 0] : HiggsVec) ∧
      (g • H.Φ2) 0 = ⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖ ∧
      ‖(g • H.Φ2) 1‖ = Real.sqrt (H.gramMatrix.det.re) / ‖H.Φ1‖
      := by
  rw [gramMatrix_det_eq_real]
  obtain ⟨g, h⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H.Φ1) (!₂[‖H.Φ1‖, 0] : HiggsVec)).mpr
    (by simp [@PiLp.norm_eq_of_L2])
  use g
  simp at h
  simp [h]
  have h_fst : (g • H.Φ2).ofLp 0 = ⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖ := by
    have h2 : ⟪H.Φ1, H.Φ2⟫_ℂ = ⟪g • H.Φ1, g • H.Φ2⟫_ℂ := by
      simp
    rw [h] at h2
    conv_rhs at h2 =>
      simp [PiLp.inner_apply]
    rw [h2]
    have hx : (‖H.Φ1‖ : ℂ) ≠ 0 := by
      simp_all
    field_simp
  apply And.intro h_fst
  have hx : ‖g • H.Φ2‖ ^ 2 = ‖H.Φ2‖ ^ 2 := by
    simp
  rw [PiLp.norm_sq_eq_of_L2] at hx
  simp at hx
  have hx0 : ‖(g • H.Φ2).ofLp 1‖ ^ 2 = ‖H.Φ2‖ ^ 2 - ‖(g • H.Φ2).ofLp 0‖ ^ 2 := by
    rw [← hx]
    simp
  have h0 : ‖(g • H.Φ2) 1‖ ^ 2 = (‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2) / ‖H.Φ1‖ ^ 2 := by
    field_simp
    rw [hx0, h_fst]
    simp
    ring_nf
    field_simp
  have habc (a b c : ℝ) (ha : 0 ≤ a) (hx : a ^ 2 = b / c ^2) (hc : c ≠ 0) (hc : 0 < c) : a = Real.sqrt b / c := by
    field_simp
    symm
    have hb : b = a ^ 2 * c ^ 2 := by
      rw [hx]
      field_simp
    subst hb
    rw [Real.sqrt_eq_iff_eq_sq ]
    · ring
    · positivity
    · positivity
  apply habc
  rw [h0]
  ring_nf
  · exact norm_ne_zero_iff.mpr h1
  · simpa using h1
  · exact norm_nonneg ((g • H.Φ2).ofLp 1)

lemma gaugeGroupI_exists_fst_eq_snd_eq {H : TwoHiggsDoublet} (h1 : H.Φ1 ≠ 0) :
    ∃ g : StandardModel.GaugeGroupI,
      g • H.Φ1 = (!₂[‖H.Φ1‖, 0] : HiggsVec) ∧
      g • H.Φ2 = (!₂[⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖, √(H.gramMatrix.det.re) / ‖H.Φ1‖] : HiggsVec) := by
  obtain ⟨g, h_fst, h_snd_0, h_snd_1⟩ := gaugeGroupI_exists_fst_eq h1
  obtain ⟨k, h1, h2, h3⟩ := HiggsVec.gaugeGroupI_smul_phase_snd (g • H.Φ2)
  use k * g
  apply And.intro
  · rw [mul_smul, h_fst, h3]
  · rw [mul_smul]
    ext i
    fin_cases i
    · simp
      rw [h2, h_snd_0]
    · simp
      rw [h1, h_snd_1]
      simp

lemma mem_orbit_gaugeGroupI_iff_gramMatrix (H1 H2 : TwoHiggsDoublet) :
    H1 ∈ MulAction.orbit GaugeGroupI H2 ↔ H1.gramMatrix = H2.gramMatrix := by
  apply Iff.intro
  · intro h
    obtain ⟨g, hg⟩ := h
    simp at hg
    simp [← hg]
  by_cases Φ1_zero : H1.Φ1 = 0
  · intro h
    obtain ⟨g1, hg1⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H1.Φ2) (!₂[‖H1.Φ2‖, 0] : HiggsVec)).mpr
      (by simp [@PiLp.norm_eq_of_L2])
    obtain ⟨g2, hg2⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H2.Φ2) (!₂[‖H2.Φ2‖, 0] : HiggsVec)).mpr
      (by simp [@PiLp.norm_eq_of_L2])
    use g1⁻¹ * g2
    simp
    ext:1
    · simp [Φ1_zero]
      have hnorm : ‖H2.Φ1‖ = ‖H1.Φ1‖ := by
        symm
        rw [← eq_fst_norm_of_eq_gramMatrix h]
      simp [Φ1_zero] at hnorm
      simp [hnorm]
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp at hg1 hg2
      simp [hg1, hg2]
      exact eq_snd_norm_of_eq_gramMatrix (id (Eq.symm h))
  · intro h
    obtain ⟨g1, H1_Φ1, H1_Φ2⟩ := gaugeGroupI_exists_fst_eq_snd_eq (H := H1) Φ1_zero
    have Φ2_nezero : H2.Φ1 ≠ 0 := by
      intro hzero
      have hnorm : ‖H1.Φ1‖ = ‖H2.Φ1‖ := by
        rw [← eq_fst_norm_of_eq_gramMatrix h]
      simp [hzero] at hnorm
      simp [hnorm] at Φ1_zero
    obtain ⟨g2, H2_Φ1, H2_Φ2⟩ := gaugeGroupI_exists_fst_eq_snd_eq (H := H2) Φ2_nezero
    use g1⁻¹ * g2
    simp
    ext:1
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp [H1_Φ1, H2_Φ1]
      apply eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp [H1_Φ2, H2_Φ2]
      apply And.intro
      · congr 1
        · symm
          exact congrArg (fun x => x 1 0) h
        · simp only [Complex.ofReal_inj]
          exact eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))
      · congr 2
        · simp [h]
        · exact eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))

/-!

### C.2. The Gram vector

-/
noncomputable def gramVector (H : TwoHiggsDoublet) : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
 2 * PauliMatrix.pauliBasis.repr ⟨gramMatrix H, gramMatrix_selfAdjoint H⟩ μ

lemma gramMatrix_eq_gramVector_sum_pauliMatrix (H : TwoHiggsDoublet) :
    gramMatrix H = (1 / 2 : ℝ) • ∑ μ, H.gramVector μ • PauliMatrix.pauliMatrix μ := by
  have h1 := congrArg (fun x => x.1) <|
    PauliMatrix.pauliBasis.sum_repr ⟨gramMatrix H, gramMatrix_selfAdjoint H⟩
  simp [-Module.Basis.sum_repr] at h1
  rw [← h1]
  simp [gramVector, smul_smul, Finset.smul_sum]
  congr 1
  · simp [PauliMatrix.pauliBasis, PauliMatrix.pauliSelfAdjoint]
  · simp [PauliMatrix.pauliBasis, PauliMatrix.pauliSelfAdjoint]

lemma gramMatrix_eq_component_gramVector (H : TwoHiggsDoublet) :
    gramMatrix H  =
    !![(1 / 2 : ℂ) * (H.gramVector (Sum.inl 0) + H.gramVector (Sum.inr 2)),
      (1 / 2 : ℂ) * (H.gramVector (Sum.inr 0) - Complex.I * H.gramVector (Sum.inr 1));
      (1 / 2 : ℂ) * (H.gramVector (Sum.inr 0) + Complex.I * H.gramVector (Sum.inr 1)),
      (1 / 2 : ℂ) * (H.gramVector (Sum.inl 0) - H.gramVector (Sum.inr 2))] := by
  rw [gramMatrix_eq_gramVector_sum_pauliMatrix]
  simp only [one_div, PauliMatrix.pauliMatrix, Matrix.one_fin_two, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Matrix.smul_of,
    Matrix.smul_cons, Complex.real_smul, mul_one, smul_zero, Matrix.smul_empty, Fin.sum_univ_three,
    smul_neg, Matrix.of_add_of, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons,
    Matrix.empty_add_empty, zero_add, smul_add, Complex.ofReal_inv, Complex.ofReal_ofNat,
    EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  ring_nf
  simp

lemma gramVector_inl_eq_trace_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inl 0) = H.gramMatrix.trace := by
  rw [gramMatrix_eq_component_gramVector, Matrix.trace_fin_two]
  simp only [Fin.isValue, one_div, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  ring

lemma normSq_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ1‖ ^ 2 = (1/2 : ℝ) * (H.gramVector (Sum.inl 0) + H.gramVector (Sum.inr 2)) := by
  trans (gramMatrix H 0 0).re
  · simp [gramMatrix]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · rw [gramMatrix_eq_component_gramVector]
    simp

lemma normSq_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ2‖ ^ 2 = (1/2 : ℝ) * (H.gramVector (Sum.inl 0) - H.gramVector (Sum.inr 2)) := by
  trans (gramMatrix H 1 1).re
  · simp [gramMatrix]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · rw [gramMatrix_eq_component_gramVector]
    simp

lemma Φ1_inner_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ1, H.Φ2⟫_ℂ) = (1/2 : ℝ) * (H.gramVector (Sum.inr 0) + Complex.I * H.gramVector (Sum.inr 1)) := by
  trans (gramMatrix H 1 0)
  · simp [gramMatrix]
  · simp [gramMatrix_eq_component_gramVector]

lemma Φ2_inner_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ2, H.Φ1⟫_ℂ) = (1/2 : ℝ) * (H.gramVector (Sum.inr 0) - Complex.I * H.gramVector (Sum.inr 1)) := by
  trans (gramMatrix H 0 1)
  · simp [gramMatrix]
  · simp [gramMatrix_eq_component_gramVector]
/-!

## D. The potential

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

noncomputable def ξ (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
  match μ with
  | Sum.inl 0 => (P.m₁₁2 + P.m₂₂2) / 2
  | Sum.inr 0 => -Complex.re P.m₁₂2
  | Sum.inr 1 => Complex.im P.m₁₂2
  | Sum.inr 2 => (P.m₁₁2 - P.m₂₂2) / 2

noncomputable def η (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl 0, Sum.inl 0 => (P.𝓵₁ + P.𝓵₂ + 2 * P.𝓵₃) / 8
  | Sum.inl 0, Sum.inr 0 => (P.𝓵₆.re + P.𝓵₇.re) * (1 / 4)
  | Sum.inl 0, Sum.inr 1 => (P.𝓵₆.im + P.𝓵₇.im)  * (-1 / 4)
  | Sum.inl 0, Sum.inr 2 => (P.𝓵₁ - P.𝓵₂) * (1 / 8)
  | Sum.inr 0, Sum.inl 0 => (P.𝓵₆.re + P.𝓵₇.re) * (1 / 4)
  | Sum.inr 1, Sum.inl 0 => (P.𝓵₆.im + P.𝓵₇.im)  * (-1 / 4)
  | Sum.inr 2, Sum.inl 0 => (P.𝓵₁ - P.𝓵₂) * (1 / 8)
  /-η_a_a-/
  | Sum.inr 0, Sum.inr 0 => (P.𝓵₅.re + P.𝓵₄) * (1 / 4)
  | Sum.inr 1, Sum.inr 1 => (-P.𝓵₅.re + P.𝓵₄) * (1 / 4)
  | Sum.inr 2, Sum.inr 2 => (P.𝓵₁ + P.𝓵₂ - 2 * P.𝓵₃) * (1 / 8)
  | Sum.inr 0, Sum.inr 1 => P.𝓵₅.im * (-1 / 4)
  | Sum.inr 2, Sum.inr 0 => (P.𝓵₆.re - P.𝓵₇.re) * (1 / 4)
  | Sum.inr 2, Sum.inr 1 => ( P.𝓵₇.im  - P.𝓵₆.im) * (1 / 4)
  | Sum.inr 1, Sum.inr 0 => P.𝓵₅.im * (-1 / 4)
  | Sum.inr 0, Sum.inr 2 => (P.𝓵₆.re - P.𝓵₇.re) * (1 / 4)
  | Sum.inr 1, Sum.inr 2 => ( P.𝓵₇.im  - P.𝓵₆.im) * (1 / 4)


lemma η_symm (P : PotentialParameters) (μ ν : Fin 1 ⊕ Fin 3) :
    P.η μ ν = P.η ν μ := by
  fin_cases μ <;> fin_cases ν <;> simp [η]

end PotentialParameters

open ComplexConjugate


noncomputable def massTerm (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  P.m₁₁2 * ‖H.Φ1‖ ^ 2 + P.m₂₂2 * ‖H.Φ2‖ ^ 2 -
  (P.m₁₂2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.m₁₂2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re

lemma massTerm_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    massTerm P H = ∑ μ, P.ξ μ * H.gramVector μ := by
  simp [massTerm, Fin.sum_univ_three, PotentialParameters.ξ, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  ring

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
  simp
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

noncomputable def potential (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  massTerm P H + quarticTerm P H

end TwoHiggsDoublet
