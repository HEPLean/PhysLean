/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import PhysLean.ClassicalMechanics.VectorFields
/-!
# Wave equation

The general wave equation.

-/

namespace ClassicalMechanics

open Space
open Time

/-- The general form of the wave equation where `c` is the propagation speed. -/
def WaveEquation (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) (c : ℝ) : Prop :=
    c^2 • Δ (f t) x - ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t = 0

/-- A vector-valued plane wave travelling in the direction of `s` with propagation speed `c`. -/
noncomputable def planeWave (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (s : Direction d) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
    fun t x => f₀ (inner ℝ x s.unit - c * t)

lemma wave_dt {s : Direction d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    ∂ₜ (fun t => f₀ (inner ℝ x s.unit - c * t)) =
    fun t : Time => -c • (f₀' (inner ℝ x s.unit - c * t)) 1 := by
  unfold Time.deriv
  ext t i
  change fderiv ℝ (f₀ ∘ fun t : Time => (inner ℝ x s.unit - c * t)) t 1 i = _
  rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    neg_mul, neg_inj, mul_eq_mul_left_iff]
  rw [HasFDerivAt.fderiv (h' (inner ℝ x s.unit - c * t))]
  left
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ContinuousLinearMap.coe_comp',
    Function.comp_apply, fderiv_val]
  repeat fun_prop

lemma wave_dt2 {s : Direction d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    ∂ₜ (fun t => -c • (f₀' (inner ℝ x s.unit - c * t)) 1) t
    =
    c^2 • (f₀'' (inner ℝ x s.unit - c * t)) 1 := by
  rw [Time.deriv_smul]
  unfold Time.deriv
  ext i
  change -c • fderiv ℝ ((fun x' => f₀' x' 1) ∘ (fun t : Time => inner ℝ x s.unit - c * t)) t 1 i = _
  rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    mul_neg, neg_mul, neg_neg]
  rw [← mul_assoc, ← pow_two]
  rw [HasFDerivAt.fderiv (h'' (inner ℝ x s.unit - c * t))]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ContinuousLinearMap.coe_comp',
    Function.comp_apply, fderiv_val]
  repeat fun_prop
  · change Differentiable ℝ ((fun t' => f₀' t' 1) ∘ (fun t : Time => (inner ℝ x s.unit - c * t)))
    apply Differentiable.comp
    · intro x
      exact HasFDerivAt.differentiableAt (h'' x)
    · fun_prop

lemma wave_differentiable {s : Direction d} {c : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    DifferentiableAt ℝ (fun x => inner ℝ x s.unit - c * t) x := by
  apply DifferentiableAt.sub
  apply DifferentiableAt.inner
  repeat fun_prop

lemma wave_dx {u v : Fin d} {s : Direction d}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    (fun x' => fderiv ℝ (fun x => (inner ℝ (f₀ (inner ℝ x s.unit - c * t))
    (EuclideanSpace.single u 1))) x' (EuclideanSpace.single v 1))
    =
    fun x' => (inner ℝ (f₀' (inner ℝ x' s.unit - c * t) (s.unit v))
    (EuclideanSpace.single u 1)) := by
  ext x'
  rw [fderiv_inner_apply]
  conv_lhs =>
    enter [2, 2, 1, 2]
    change (f₀ ∘ fun x => (inner ℝ x s.unit - c * t))
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [HasFDerivAt.fderiv (h' (inner ℝ x' s.unit - c * t))]
  have hdi : (fderiv ℝ (fun x => inner ℝ x s.unit - c * t) x') (EuclideanSpace.single v 1)
      =
      s.unit v := by
    rw [fderiv_fun_sub]
    simp only [fderiv_fun_const, Pi.ofNat_apply, sub_zero]
    rw [fderiv_inner_apply]
    simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
    rw [real_inner_comm]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_left,
      PiLp.inner_apply, EuclideanSpace.single_apply, RCLike.inner_apply,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, zero_add]
    repeat fun_prop
    apply DifferentiableAt.inner
    repeat fun_prop
  rw [hdi]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, inner_zero_right, EuclideanSpace.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, zero_add]
  · fun_prop
  · exact wave_differentiable
  · apply DifferentiableAt.comp
    · fun_prop
    · exact wave_differentiable
  · fun_prop

lemma wave_dx2 {u v : Fin d} {s : Direction d}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)} {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    (fderiv ℝ (fun x' => (inner ℝ ((f₀' (inner ℝ x' s.unit - c * t)) (s.unit u))
    (EuclideanSpace.single v 1))) x) (EuclideanSpace.single u 1)
    =
    inner ℝ ((s.unit u) ^ 2 • f₀'' (inner ℝ x s.unit - c * t) 1) (EuclideanSpace.single v 1) := by
  rw [fderiv_inner_apply]
  have hdi' : (fderiv ℝ (fun x' => (f₀' (inner ℝ x' s.unit - c * t))
      (s.unit u)) x) (EuclideanSpace.single u 1)
      =
      (s.unit u) ^ 2 • (f₀'' (inner ℝ x s.unit - c * t) 1) := by
    change (fderiv ℝ ((fun x' => f₀' x' (s.unit u)) ∘
        fun x' => (inner ℝ x' s.unit - c * t)) x) (EuclideanSpace.single u 1) = _
    rw [fderiv_comp, fderiv_fun_sub]
    simp only [fderiv_fun_const, Pi.ofNat_apply, sub_zero, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [fderiv_inner_apply]
    simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
    trans (fderiv ℝ (fun x' => (f₀' x') (s.unit u • 1)) (inner ℝ x s.unit - c * t)) (s.unit u • 1)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, fderiv_fun_const, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, inner_zero_right, EuclideanSpace.single_apply,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, zero_add, fderiv_eq_smul_deriv, smul_eq_mul]
    conv_lhs =>
      enter [1, 2, x']
      rw [ContinuousLinearMap.map_smul]
    rw [ContinuousLinearMap.map_smul, fderiv_fun_const_smul, pow_two]
    rw [HasFDerivAt.fderiv (h'' (inner ℝ x s.unit - c * t))]
    change s.unit u • s.unit u • (f₀'' (inner ℝ x s.unit - c * t) 1) = _
    rw [← smul_assoc, smul_eq_mul]
    repeat fun_prop
    apply DifferentiableAt.inner
    repeat fun_prop
    · conv_lhs =>
        enter [x]
        rw [← mul_one (s.unit u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
      fun_prop
    · exact wave_differentiable
  rw [hdi']
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, inner_zero_right, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, zero_add]
  change DifferentiableAt ℝ ((fun x' => f₀' x' (s.unit u)) ∘
      (fun x => (inner ℝ x s.unit - c * t))) x
  apply DifferentiableAt.comp
  · conv_lhs =>
      enter [x]
      rw [← mul_one (s.unit u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
    fun_prop
  · exact wave_differentiable
  · fun_prop

/-- The plane wave satisfies the wave equation. -/
theorem planeWave_isWave (c : ℝ) (s : Direction d)
    (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    ∀ t x, WaveEquation (planeWave f₀ c s) t x c := by
  intro t x
  unfold WaveEquation planeWave
  conv_lhs =>
    enter [2, 1, t]
    rw [wave_dt h']
  conv_lhs =>
    enter [2]
    rw [wave_dt2 h'']
  unfold laplacianVec laplacian coord basis Space.deriv
  rw [← smul_sub]
  simp only [EuclideanSpace.basisFun_apply, smul_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  right
  ext i
  conv_lhs =>
    enter [1, u, 2, v]
    rw [wave_dx h']
  simp only [PiLp.sub_apply, PiLp.zero_apply]
  conv_lhs =>
    enter [1, 2, j]
    rw [wave_dx2 h'']
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [← Finset.sum_mul]
  have hsj : ∑ j, s.unit j ^ 2 = 1 := by
    have h := s.norm
    rw [norm, PiLp.instNorm] at h
    norm_num at h
    rw [← Real.sqrt_eq_rpow, Real.sqrt_eq_one] at h
    exact h
  rw [hsj]
  simp

/-!
## Helper lemmas for further derivation
-/

/-- If `f₀` is a function of `(inner ℝ x s - c * t)`, the fderiv of its components
with respect to spatial coordinates is equal to the corresponding component of
the propagation direction `s` times time derivative. -/
lemma space_fderiv_of_inner_product_wave_eq_space_fderiv
    {t : Time} {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {u v : Fin d} (h' : Differentiable ℝ f₀) :
    c * ((fun x' => (fderiv ℝ (fun x => inner ℝ (f₀ (inner ℝ x s.unit - c * t))
    (EuclideanSpace.single v 1)) x') (EuclideanSpace.single u 1)) x)
    =
    - s.unit u * ∂ₜ (fun t => f₀ (inner ℝ x s.unit - c * t)) t v := by
  rw [wave_dx, wave_dt]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, EuclideanSpace.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, PiLp.smul_apply,
    smul_eq_mul, neg_mul, mul_neg]
  rw [← mul_one (s.unit u), ← smul_eq_mul (s.unit u), ContinuousLinearMap.map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_one]
  ring
  repeat
    intro x
    apply DifferentiableAt.hasFDerivAt
    fun_prop

lemma time_differentiable_of_eq_planewave {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)} {f : Time → Space d → EuclideanSpace ℝ (Fin d)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    Differentiable ℝ fun t => f t x := by
  rw [hf]
  unfold planeWave
  fun_prop

open Matrix

lemma crossProduct_time_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {f : Time → Space → EuclideanSpace ℝ (Fin 3)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    DifferentiableAt ℝ (fun t => s.unit ⨯ₑ₃ (f t x)) t := by
  rw [hf, crossProduct]
  unfold planeWave
  apply differentiable_pi''
  intro i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, LinearMap.mk₂_apply, PiLp.ofLp_apply,
    Fin.reduceFinMk, WithLp.equiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val]
    fun_prop

lemma crossProduct_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} (h' : Differentiable ℝ f₀) :
    DifferentiableAt ℝ (fun u => s.unit ⨯ₑ₃ (f₀ u)) u := by
  rw [crossProduct]
  apply differentiable_pi''
  intro i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
    LinearMap.mk₂_apply, PiLp.ofLp_apply, Fin.reduceFinMk, WithLp.equiv_symm_apply, PiLp.toLp_apply,
    Matrix.cons_val]
    fun_prop

lemma wave_fderiv_inner_eq_inner_fderiv_proj {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {i : Fin d} (h' : Differentiable ℝ f₀) :
    ∀ x y, s.unit i * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t)) x) y i
    =
    inner ℝ y s.unit * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t) i) x)
    (EuclideanSpace.single i 1) := by
  intro x y
  rw [fderiv_pi]
  change s.unit i * fderiv ℝ ((EuclideanSpace.proj i) ∘
      fun x => f₀ (inner ℝ x s.unit - c * t)) x y =
      inner ℝ y s.unit * (fderiv ℝ ((EuclideanSpace.proj i) ∘
      fun x => f₀ (inner ℝ x s.unit - c * t)) x) (EuclideanSpace.single i 1)
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    PiLp.proj_apply]
  change s.unit i * (fderiv ℝ (f₀ ∘ fun x => (inner ℝ x s.unit - c * t)) x) y i =
      inner ℝ y s.unit * (fderiv ℝ (f₀ ∘ fun x => (inner ℝ x s.unit - c * t)) x)
      (EuclideanSpace.single i 1) i
  rw [fderiv_comp, fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, sub_zero, ContinuousLinearMap.coe_comp',
    Function.comp_apply, differentiableAt_fun_id, differentiableAt_const, fderiv_inner_apply,
    ContinuousLinearMap.zero_apply, inner_zero_right, fderiv_id', ContinuousLinearMap.coe_id',
    id_eq, zero_add]
  nth_rw 5 [PiLp.inner_apply]
  simp only [EuclideanSpace.single_apply, RCLike.inner_apply, MonoidWithZeroHom.map_ite_one_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← mul_one (s.unit i), ← smul_eq_mul (s.unit i), ContinuousLinearMap.map_smul]
  rw [← mul_one (inner ℝ y s.unit), ← smul_eq_mul (inner ℝ y s.unit), ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul, PiLp.smul_apply, ← mul_assoc, mul_comm, one_mul]
  apply DifferentiableAt.inner
  repeat fun_prop
  · exact wave_differentiable
  · fun_prop
  · apply DifferentiableAt.comp
    · fun_prop
    · exact wave_differentiable
  · intro i
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    fun_prop

lemma differentiable_uncurry_of_eq_planewave {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)} (hf : f = planeWave f₀ c s)
    (h' : Differentiable ℝ f₀) : Differentiable ℝ ↿f := by
  rw [hf]
  unfold planeWave
  change Differentiable ℝ (f₀ ∘ fun ((t : Time), x) => (inner ℝ x s.unit - c * t))
  apply Differentiable.comp
  · fun_prop
  · apply Differentiable.sub
    · apply Differentiable.inner
      repeat fun_prop
    · fun_prop

end ClassicalMechanics
