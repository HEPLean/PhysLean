/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhysHermite
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import PhysLean.Mathematics.SpecialFunctions.PhysHermite
import Mathlib.Analysis.Convolution
import Mathlib.Algebra.Star.Basic
/-!

# Hilbert space for one dimension quantum mechanics

-/

namespace QuantumMechanics

namespace OneDimension

noncomputable section

/-- The Hilbert space for a one dimensional quantum system is defined as
  the space of almost-everywhere equal equivalence classes of square integrable functions
  from `ℝ` to `ℂ`. -/
abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2

namespace HilbertSpace
open MeasureTheory

/-- The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : ℝ → ℂ) : Prop := MemLp f 2 MeasureTheory.volume

lemma aeStronglyMeasurable_of_memHS {f : ℝ → ℂ} (h : MemHS f) : AEStronglyMeasurable f := h.1

/-- A function `f` satisfies `MemHS f` if and only if it is almost everywhere
  strongly measurable, and square integrable. -/
lemma memHS_iff {f : ℝ → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [MemHS, MemLp, and_congr_right_iff]
  intro h1
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (Ne.symm (NeZero.ne' 2)) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable (fun x => norm (f x) ^ 2) MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.pow (continuous_norm.comp_aestronglyMeasurable h1) ..
  simp [h0, HasFiniteIntegral]

lemma aeEqFun_mk_mem_iff (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ HilbertSpace ↔ MemHS f := by
  simp only [Lp.mem_Lp_iff_memLp]
  exact MeasureTheory.memLp_congr_ae (AEEqFun.coeFn_mk f hf)

/-- Given a function `f : ℝ → ℂ` such that `MemHS f` is true via `hf`, then `HilbertSpace.mk hf`
  is the element of the `HilbertSpace` defined by `f`. -/
def mk {f : ℝ → ℂ} (hf : MemHS f) : HilbertSpace :=
  ⟨AEEqFun.mk f hf.1, (aeEqFun_mk_mem_iff f hf.1).mpr hf⟩

lemma coe_hilbertSpace_memHS (f : HilbertSpace) : MemHS (f : ℝ → ℂ) := by
  rw [← aeEqFun_mk_mem_iff f.1 (Lp.aestronglyMeasurable f)]
  have hf : f = AEEqFun.mk f.1 (Lp.aestronglyMeasurable f) := (AEEqFun.mk_coeFn _).symm
  exact hf ▸ f.2

lemma mk_surjective (f : HilbertSpace) : ∃ (g : ℝ → ℂ), ∃ (hg : MemHS g), mk hg = f := by
  use f, coe_hilbertSpace_memHS f
  simp [mk]

lemma coe_mk_ae {f : ℝ → ℂ} (hf : MemHS f) : (mk hf : ℝ → ℂ) =ᵐ[MeasureTheory.volume] f :=
  AEEqFun.coeFn_mk f hf.1

lemma inner_mk_mk {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    inner (mk hf) (mk hg) = ∫ x : ℝ, starRingEnd ℂ (f x) * g x := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coe_mk_ae hf, coe_mk_ae hg] with _ hf hg
  simp [hf, hg, mul_comm]

@[simp]
lemma eLpNorm_mk {f : ℝ → ℂ} {hf : MemHS f} : eLpNorm (mk hf) 2 volume = eLpNorm f 2 volume :=
  MeasureTheory.eLpNorm_congr_ae (coe_mk_ae hf)

lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  simp only [Lp.mem_Lp_iff_memLp, MemLp, eLpNorm_aeeqFun]
  have h1 : MeasureTheory.AEStronglyMeasurable
      (MeasureTheory.AEEqFun.mk f hf) MeasureTheory.volume :=
    MeasureTheory.AEEqFun.aestronglyMeasurable ..
  simp only [h1,
    MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (Ne.symm (NeZero.ne' 2))
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, true_and, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable (fun x => norm (f x) ^ 2) MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.pow (continuous_norm.comp_aestronglyMeasurable hf) ..
  simp [h0, HasFiniteIntegral]

/-!

## Gaussians

-/
open MeasureTheory

lemma gaussian_integrable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => (Real.exp (- b * (x - c)^ 2) : ℂ)) :=
  MeasureTheory.Integrable.ofReal (Integrable.comp_sub_right
    (f := (fun x => Real.exp (- b * x ^ 2))) (integrable_exp_neg_mul_sq hb) ..)

lemma gaussian_aestronglyMeasurable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) volume :=
  MeasureTheory.Integrable.aestronglyMeasurable (gaussian_integrable c hb)

lemma gaussian_memHS {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MemHS (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) := by
  rw [memHS_iff]
  refine ⟨gaussian_aestronglyMeasurable c hb, ?_⟩
  simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h1 : (fun (x : ℝ) => Real.exp (-(b * ((x - c : ℂ) ^ 2).re)) ^ 2) =
    fun y => (fun x => Real.exp (- (2 * b) * x ^ 2)) (y - c) := by
    ext x
    simp only [neg_mul]
    trans Real.exp (-(b * ((x - c: ℂ) ^ 2).re)) ^ (2 : ℝ)
    · simp
    rw [← Real.exp_mul]
    simp only [neg_mul, Real.exp_eq_exp, neg_inj]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [h1]
  apply Integrable.comp_sub_right (f := fun x => Real.exp (- (2 * b) * x ^ 2))
  apply integrable_exp_neg_mul_sq
  simp_all

lemma exp_mul_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (c * x) * Real.exp (- b * x ^ 2)) := by
  have h1 : (fun x => Real.exp (c * x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) * Real.exp (- b * (x - c/(2 * b)) ^ 2)) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  apply MeasureTheory.Integrable.const_mul
  apply Integrable.comp_sub_right (f := (fun x => Real.exp (- b * x ^ 2)))
  exact integrable_exp_neg_mul_sq hb

lemma exp_abs_mul_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (|c * x|) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0 := (Set.Iic_union_Ici).symm
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (- |c|) hb
    · intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul, abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (|c|) hb
    · intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul, abs_of_nonneg hx]

lemma mul_gaussian_mem_Lp_one (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.MemLp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 1 volume := by
  refine memLp_one_iff_integrable.mpr ?_
  let g : HilbertSpace := mk (gaussian_memHS c hb)
  refine (integrable_congr ?_).mp (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) g (mk hf))
  simp only [RCLike.inner_apply, neg_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub]
  refine Filter.EventuallyEq.mul (coe_mk_ae hf) ?_
  trans (fun x => (starRingEnd ℂ) (Real.exp (- b * (x - c) ^2)))
  · apply Filter.EventuallyEq.fun_comp
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, g]
    exact AEEqFun.coeFn_mk ..
  · apply Filter.EventuallyEq.of_eq
    funext x
    rw [Complex.conj_ofReal]
    simp

lemma mul_gaussian_mem_Lp_two (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.MemLp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 2 volume := by
  refine MeasureTheory.MemLp.mul ?_ hf (q := ⊤)
  · apply MeasureTheory.memLp_top_of_bound (C := Real.exp (0))
    · exact gaussian_aestronglyMeasurable c hb
    · apply Filter.Eventually.of_forall
      intro x
      simp only [neg_mul, zero_sub, even_two, Even.neg_pow]
      rw [Complex.norm_real]
      simp only [Real.norm_eq_abs, Real.abs_exp, Real.exp_zero, Real.exp_le_one_iff,
        Left.neg_nonpos_iff]
      apply mul_nonneg
      · exact le_of_lt hb
      · exact sq_nonneg (x - c)

lemma abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => norm (f x) * Real.exp (- b * (x - c)^2)) := by
  have h1 : (fun x => norm (f x) * Real.exp (- b * (x - c)^2)) =
      (fun x => norm (f x * Real.exp (- b *(x - c)^2))) := by
    funext x
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.norm_mul, Complex.norm_exp, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_eq_mul_left_iff,
      Real.exp_eq_exp, neg_inj, norm_eq_zero]
    left
    left
    simp [← Complex.ofReal_sub, ← Complex.ofReal_pow]
  rw [h1]
  simpa using MeasureTheory.MemLp.integrable_norm_rpow (mul_gaussian_mem_Lp_one f hf b c hb)
    one_ne_zero ENNReal.one_ne_top

lemma exp_mul_abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f)
    (b c : ℝ) (hb : 0 < b) : MeasureTheory.Integrable
    (fun x => Real.exp (c * x) * norm (f x) * Real.exp (- b * x ^ 2)) := by
  have h1 : (fun x => Real.exp (c * x) *
    norm (f x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) *
      (norm (f x) * Real.exp (- b * (x - c/(2 * b)) ^ 2))) := by
    funext x
    rw [mul_comm,← mul_assoc]
    trans (Real.exp (c ^ 2 / (4 * b)) * Real.exp (-b * (x - c / (2 * b)) ^ 2)) * norm (f x)
    swap
    · ring
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  exact MeasureTheory.Integrable.const_mul (abs_mul_gaussian_integrable f hf b (c / (2 * b)) hb) ..

lemma exp_abs_mul_abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable
    (fun x => Real.exp (|c * x|) * norm (f x) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0 := Set.Iic_union_Ici.symm
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * norm (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf b (-|c|) hb
    · intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, map_eq_zero, Real.exp_ne_zero,
        or_false, g]
      left
      rw [abs_mul, abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * norm (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf b |c| hb
    · intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, map_eq_zero, Real.exp_ne_zero,
        or_false, g]
      left
      rw [abs_mul, abs_of_nonneg hx]

end HilbertSpace
