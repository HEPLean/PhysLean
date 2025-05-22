/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import PhysLean.ClassicalMechanics.Time.Basic
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
@[nolint unusedArguments]
noncomputable def planeWave (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (s : Space d) (hs : inner ℝ s s = 1) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
    fun t x => f₀ (inner ℝ x s - c * t)

lemma wave_dt {s : Space d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    ∂ₜ (fun t => f₀ (inner ℝ x s - c * t)) = fun t => -c • (f₀' (inner ℝ x s - c * t)) 1 := by
  unfold Time.deriv
  ext t i
  change fderiv ℝ (f₀ ∘ fun t => (inner ℝ x s - c * t)) t 1 i = _
  rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
  simp only [fderiv_id', ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, ContinuousLinearMap.comp_id, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    neg_mul, neg_inj, mul_eq_mul_left_iff]
  rw [HasFDerivAt.fderiv (h' (inner ℝ x s - c * t))]
  left
  rfl
  repeat fun_prop

lemma wave_dt2 {s : Space d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    ∂ₜ (fun t => -c • (f₀' (inner ℝ x s - c * t)) 1) t
    =
    c^2 • (f₀'' (inner ℝ x s - c * t)) 1 := by
  rw [Time.deriv_smul]
  unfold Time.deriv
  ext i
  change -c • fderiv ℝ ((fun x' => f₀' x' 1) ∘ (fun t => inner ℝ x s - c * t)) t 1 i = _
  rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
  simp only [fderiv_id', ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, ContinuousLinearMap.comp_id, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    mul_neg, neg_mul, neg_neg]
  rw [← mul_assoc, ← pow_two]
  rw [HasFDerivAt.fderiv (h'' (inner ℝ x s - c * t))]
  repeat fun_prop
  · change Differentiable ℝ ((fun t' => f₀' t' 1) ∘ (fun t => (inner ℝ x s - c * t)))
    apply Differentiable.comp
    · intro x
      exact HasFDerivAt.differentiableAt (h'' x)
    · fun_prop

lemma wave_differentiable {c : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    DifferentiableAt ℝ (fun x => inner ℝ x s - c * t) x := by
  apply DifferentiableAt.sub
  apply DifferentiableAt.inner
  repeat fun_prop

lemma wave_dx {u v : Fin d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    (fun x' => fderiv ℝ (fun x => (inner ℝ (f₀ (inner ℝ x s - c * t))
    (EuclideanSpace.single u 1))) x' (EuclideanSpace.single v 1))
    =
    fun x' => (inner ℝ (f₀' (inner ℝ x' s - c * t) (s v)) (EuclideanSpace.single u 1)) := by
  ext x'
  rw [fderiv_inner_apply]
  simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
    zero_add]
  conv_lhs =>
    enter [2, 1, 2]
    change (f₀ ∘ fun x => (inner ℝ x s - c * t))
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [HasFDerivAt.fderiv (h' (inner ℝ x' s - c * t))]
  have hdi : (fderiv ℝ (fun x => inner ℝ x s - c * t) x') (EuclideanSpace.single v 1)
      =
      s v := by
    rw [fderiv_sub]
    simp only [fderiv_const, Pi.zero_apply, sub_zero]
    rw [fderiv_inner_apply]
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      fderiv_id', ContinuousLinearMap.coe_id', id_eq, zero_add]
    rw [real_inner_comm]
    simp only [PiLp.inner_apply, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    repeat fun_prop
    apply DifferentiableAt.inner
    repeat fun_prop
  rw [hdi]
  · fun_prop
  · exact wave_differentiable
  · apply DifferentiableAt.comp
    · fun_prop
    · exact wave_differentiable
  · fun_prop

lemma wave_dx2 {u v : Fin d} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    (fderiv ℝ (fun x' => (inner ℝ ((f₀' (inner ℝ x' s - c * t)) (s u))
    (EuclideanSpace.single v 1))) x) (EuclideanSpace.single u 1)
    =
    inner ℝ ((s u) ^ 2 • f₀'' (inner ℝ x s - c * t) 1) (EuclideanSpace.single v 1) := by
  rw [fderiv_inner_apply]
  simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
    zero_add]
  have hdi' : (fderiv ℝ (fun x' => (f₀' (inner ℝ x' s - c * t))
      (s u)) x) (EuclideanSpace.single u 1)
      =
      (s u) ^ 2 • (f₀'' (inner ℝ x s - c * t) 1) := by
    change (fderiv ℝ ((fun x' => f₀' x' (s u)) ∘
        fun x' => (inner ℝ x' s - c * t)) x) (EuclideanSpace.single u 1) = _
    rw [fderiv_comp, fderiv_sub]
    simp only [fderiv_const, Pi.zero_apply, sub_zero, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [fderiv_inner_apply]
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      fderiv_id', ContinuousLinearMap.coe_id', id_eq, zero_add]
    trans (fderiv ℝ (fun x' => (f₀' x') (s u • 1)) (inner ℝ x s - c * t)) (s u • 1)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, EuclideanSpace.single_apply,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, fderiv_eq_smul_deriv, smul_eq_mul]
    conv_lhs =>
      enter [1, 2, x']
      rw [ContinuousLinearMap.map_smul]
    rw [ContinuousLinearMap.map_smul, fderiv_const_smul, pow_two]
    rw [HasFDerivAt.fderiv (h'' (inner ℝ x s - c * t))]
    change s u • s u • (f₀'' (inner ℝ x s - c * t) 1) = _
    rw [← smul_assoc, smul_eq_mul]
    repeat fun_prop
    apply DifferentiableAt.inner
    repeat fun_prop
    · conv_lhs =>
        enter [x]
        rw [← mul_one (s u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
      apply DifferentiableAt.const_smul
      exact HasFDerivAt.differentiableAt (h'' (inner ℝ x s - c * t))
    · exact wave_differentiable
  rw [hdi']
  change DifferentiableAt ℝ ((fun x' => f₀' x' (s u)) ∘ (fun x => (inner ℝ x s - c * t))) x
  apply DifferentiableAt.comp
  · conv_lhs =>
      enter [x]
      rw [← mul_one (s u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
    apply DifferentiableAt.const_smul
    exact HasFDerivAt.differentiableAt (h'' (inner ℝ x s - c * t))
  · exact wave_differentiable
  · fun_prop

/-- The plane wave satisfies the wave equation. -/
theorem planeWave_isWave (c : ℝ) (s : Space d) (hs : inner ℝ s s = 1)
    (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    WaveEquation (planeWave f₀ c s hs) t x c := by
  unfold WaveEquation planeWave
  conv_lhs =>
    enter [2, 1, t]
    rw [wave_dt h']
  conv_lhs =>
    enter [2]
    rw [wave_dt2 h'']
  unfold laplacian_vec laplacian coord basis Space.deriv
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
  have hsj : ∑ j, s j ^ 2 = 1 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at hs
    conv_lhs =>
      enter [2, j]
      rw [pow_two]
    rw [hs]
  rw [hsj]
  simp
