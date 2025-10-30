/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
/-!

# Vector identities

## i. Overview

In this module we prove properties of the gradient, divergence, and curl operators.
We show that on differentiable functions they are linear,
show their action on basic functions, and prove vector calculus identities

## ii. Key results

- `grad_inner_space_unit_vector` : The gradient in the direction of the space position.
- `curl_of_curl` : `∇ × (∇ × f) = ∇ (∇ ⬝ f) - Δ f`
- `div_of_curl_eq_zero` : `∇ ⬝ (∇ × f) = 0`

## iii. Table of contents

- A. Basic lemmas about derivatives of space
  - A.1. Derivative distributes over addition
  - A.2. Derivative distributes over scalar multiplication
  - A.3. Two spatial derivatives commute
  - A.4. Derivative of a component
  - A.5. Derivative of a component squared
  - A.6. Derivivatives of components
  - A.7. Derivative of a norm squared
    - A.7.1. Differentiability of the norm squared function
    - A.7.2. Derivative of the norm squared function
  - A.8. Derivative of the inner product
    - A.8.1. Differentiability of the inner product function
    - A.8.2. Derivative of the inner product function
  - A.9. Differentiability of derivatives
- B. Properties of the gradient operator
  - B.1. Gradient of the zero function
  - B.2. Gradient distributes over addition
  - B.3. Gradient of a constant function
  - B.4. Gradient distributes over scalar multiplication
  - B.5. Gradient distributes over negation
  - B.6. Expansion in terms of basis vectors
  - B.7. Components of the gradient
  - B.8. Inner product with a gradient
  - B.9. Gradient is equal to `gradient` from Mathlib
  - B.10. Value of gradient in the direction of the position vector
  - B.11. Gradient of the norm squared function
  - B.12. Gradient of the inner product function
- C. Properties of the curl operator
  - C.1. The curl on the zero function
  - C.2. The curl on a constant function
  - C.3. The curl distributes over addition
  - C.4. The curl distributes over scalar multiplication
  - C.5. The curl of a linear map is a linear map
  - C.6. Preliminary lemmas about second derivatives
  - C.7. The div of a curl is zero
  - C.8. The curl of a curl
- D. Properties of the divergence operator
  - D.1. The divergence on the zero function
  - D.2. The divergence on a constant function
  - D.3. The divergence distributes over addition
  - D.4. The divergence distributes over scalar multiplication
  - D.5. The divergence of a linear map is a linear map
- E. Properties of the Laplacian operator

## iv. References

-/

namespace Space

/-!

## A. Basic lemmas about derivatives of space

-/

/-!

### A.1. Derivative distributes over addition

-/

/-- Derivatives on space distribute over addition. -/
lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f1 f2 : Space d → M) (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∂[u] (f1 + f2) = ∂[u] f1 + ∂[u] f2 := by
  unfold deriv
  simp only
  ext x
  rw [fderiv_add]
  rfl
  repeat fun_prop

/-- Derivatives on space distribute coordinate-wise over addition. -/
lemma deriv_coord_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    (∂[u] (fun x => f1 x i + f2 x i)) =
      (∂[u] (fun x => f1 x i)) + (∂[u] (fun x => f2 x i)) := by
  unfold deriv
  simp only
  ext x
  rw [fderiv_fun_add]
  simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
  repeat fun_prop

/-!

### A.2. Derivative distributes over scalar multiplication

-/

/-- Scalar multiplication on space derivatives. -/
lemma deriv_smul [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Space d → M) (k : ℝ) (hf : Differentiable ℝ f) :
    ∂[u] (k • f) = (k • ∂[u] f) := by
  unfold deriv
  ext x
  rw [fderiv_const_smul]
  rfl
  fun_prop

/-- Coordinate-wise scalar multiplication on space derivatives. -/
lemma deriv_coord_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂[u] (fun x => k * f x i) x= (k • ∂[u] (fun x => f x i)) x:= by
  unfold deriv
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  fun_prop

/-!

### A.3. Two spatial derivatives commute

-/

/-- Derivatives on space commute with one another. -/
lemma deriv_commute [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Space d → M) (hf : ContDiff ℝ 2 f) : ∂[u] (∂[v] f) = ∂[v] (∂[u] f) := by
  unfold deriv
  ext x
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  apply ContDiffAt.isSymmSndFDerivAt
  exact ContDiff.contDiffAt hf
  simp only [minSmoothness_of_isRCLikeNormedField, le_refl]
  repeat fun_prop

/-!

### A.4. Derivative of a component

-/

@[simp]
lemma deriv_component_same (μ : Fin d) (x : Space d) :
    ∂[μ] (fun x => x μ) x = 1 := by
  conv_lhs =>
    enter [2, x]
    rw [← Space.coord_apply μ x]
  change deriv μ (Space.coordCLM μ) x = 1
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simp [Space.coordCLM, Space.coord]

lemma deriv_component_diff (μ ν : Fin d) (x : Space d) (h : μ ≠ ν) :
    (deriv μ (fun x => x ν) x) = 0 := by
  conv_lhs =>
    enter [2, x]
    rw [← Space.coord_apply _ x]
  change deriv μ (Space.coordCLM ν) x = 0
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simpa [Space.coordCLM, Space.coord] using h.symm

lemma deriv_component (μ ν : Fin d) (x : Space d) :
    (deriv ν (fun x => x μ) x) = if ν = μ then 1 else 0 := by
  by_cases h' : ν = μ
  · subst h'
    simp
  · rw [deriv_component_diff ν μ]
    simp only [right_eq_ite_iff, zero_ne_one, imp_false]
    simpa using h'
    simpa using h'

/-!

### A.5. Derivative of a component squared

-/

lemma deriv_component_sq {d : ℕ} {ν μ : Fin d} (x : Space d) :
    (deriv ν (fun x => (x μ) ^ 2) x) = if ν = μ then 2 * x μ else 0:= by
  rw [deriv_eq_fderiv_basis]
  rw [fderiv_pow]
  simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [← deriv_eq_fderiv_basis, deriv_component]
  simp only [mul_ite, mul_one, mul_zero]
  fun_prop

/-!

### A.6. Derivivatives of components

-/

lemma deriv_euclid {d ν μ} {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq_fderiv_basis]
  · fun_prop
  · fun_prop

lemma deriv_lorentz_vector {d ν μ} {f : Space d → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (Lorentz.Vector.coordCLM μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq_fderiv_basis]
    rfl
  · fun_prop
  · fun_prop

/-!

### A.7. Derivative of a norm squared

-/

/-!

#### A.7.1. Differentiability of the norm squared function

-/
@[fun_prop]
lemma norm_sq_differentiable : Differentiable ℝ (fun x : Space d => ‖x‖ ^ 2) := by
  simp [@PiLp.norm_sq_eq_of_L2]
  fun_prop

/-!

#### A.7.2. Derivative of the norm squared function

-/

lemma deriv_norm_sq (x : Space d) (i : Fin d) :
    deriv i (fun x => ‖x‖ ^ 2) x = 2 * x i := by
  simp [@PiLp.norm_sq_eq_of_L2]
  rw [deriv_eq_fderiv_basis]
  rw [fderiv_fun_sum]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  conv_lhs =>
    enter [2, j]
    rw [← deriv_eq_fderiv_basis]
    simp
  simp [deriv_component_sq]
  intro i hi
  fun_prop

/-!

### A.8. Derivative of the inner product

-/

open InnerProductSpace

/-!

#### A.8.1. Differentiability of the inner product function

-/

/-- The inner product is differentiable. -/
lemma inner_differentiable {d : ℕ} :
    Differentiable ℝ (fun y : Space d => ⟪y, y⟫_ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  fun_prop

/-!

#### A.8.2. Derivative of the inner product function

-/

lemma deriv_eq_inner_self (x : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x⟫_ℝ) x = 2 * x i := by
  convert deriv_norm_sq x i
  exact real_inner_self_eq_norm_sq _

/-!

### A.9. Differentiability of derivatives

-/

lemma deriv_differentiable {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} {f : Space d → M}
    (hf : ContDiff ℝ 2 f) (i : Fin d) :
    Differentiable ℝ (deriv i f) := by
  have h1 : Differentiable ℝ (fun x => fderiv ℝ f x (basis i)) := by
    fun_prop
  convert h1 using 1
  funext x
  rw [deriv_eq_fderiv_basis]

/-!

## B. Properties of the gradient operator

-/

/-!

### B.1. Gradient of the zero function

-/

@[simp]
lemma grad_zero : ∇ (0 : Space d → ℝ) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### B.2. Gradient distributes over addition

-/

lemma grad_add (f1 f2 : Space d → ℝ)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ (f1 + f2) = ∇ f1 + ∇ f2 := by
  unfold grad
  ext x i
  simp only [Pi.add_apply]
  rw [deriv_add]
  rfl
  exact hf1
  exact hf2

/-!

### B.3. Gradient of a constant function

-/

@[simp]
lemma grad_const : ∇ (fun _ : Space d => c) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### B.4. Gradient distributes over scalar multiplication

-/

lemma grad_smul (f : Space d → ℝ) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ (k • f) = k • ∇ f := by
  unfold grad
  ext x i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [deriv_smul]
  rfl
  exact hf

/-!

### B.5. Gradient distributes over negation

-/

lemma grad_neg (f : Space d → ℝ) :
    ∇ (- f) = - ∇ f := by
  unfold grad
  ext x i
  simp only [Pi.neg_apply]
  rw [Space.deriv_eq, fderiv_neg]
  rfl

/-!

### B.6. Expansion in terms of basis vectors

-/

lemma grad_eq_sum {d} (f : Space d → ℝ) (x : Space d) :
    ∇ f x = ∑ i, deriv i f x • basis i := by
  funext i
  rw [grad, deriv_eq]
  simp only
  rw [Fintype.sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [basis]
    rfl
  · intro j hj
    simp [basis]
    exact fun a a_1 => False.elim (a (id (Eq.symm a_1)))
  · simp

/-!

### B.7. Components of the gradient

-/

lemma grad_apply {d} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    (∇ f x) i = deriv i f x := by
  rw [grad_eq_sum]
  simp [basis_apply]

/-!

### B.8. Inner product with a gradient

-/

open InnerProductSpace

lemma grad_inner_eq {d} (f : Space d → ℝ) (x : Space d) (y : Space d) :
    ⟪∇ f x, y⟫_ℝ = (fderiv ℝ f x) y:= by
  rw [grad_eq_sum]
  have hy : y = ∑ i, y i • basis i := by
      conv_lhs => rw [← OrthonormalBasis.sum_repr basis y]
      dsimp [basis]
  rw [hy]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_sum, map_smul, smul_eq_mul]
  conv_lhs =>
    enter [2, x]
    rw [Fintype.sum_apply, Fintype.sum_apply]
  simp [basis_apply]
  congr
  funext x
  rw [deriv_eq_fderiv_basis]

lemma inner_grad_eq {d} (f : Space d → ℝ) (x : Space d) (y : Space d) :
    ⟪x, ∇ f y⟫_ℝ = (fderiv ℝ f y) x := by
  rw [← grad_inner_eq]
  exact real_inner_comm (∇ f y) x

/-!

### B.9. Gradient is equal to `gradient` from Mathlib

-/

lemma grad_eq_gradiant {d} (f : Space d → ℝ) :
    ∇ f = gradient f := by
  funext x
  have hx (y : Space d) : ⟪gradient f x, y⟫_ℝ =
      ⟪∇ f x, y⟫_ℝ := by
    rw [gradient, toDual_symm_apply]
    exact Eq.symm (grad_inner_eq f x y)
  have h1 : ∀ y, ⟪gradient f x - ∇ f x, y⟫_ℝ = 0 := by
    intro y
    rw [inner_sub_left, hx y]
    simp
  have h2 := h1 (gradient f x - ∇ f x)
  rw [inner_self_eq_zero, sub_eq_zero] at h2
  rw [h2]

/-!

### B.10. Value of gradient in the direction of the position vector

-/

/-- The gradient in the direction of the space position. -/
lemma grad_inner_space_unit_vector {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, ‖x‖⁻¹ • x⟫_ℝ = _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp
  symm
  calc _
    _ = fderiv ℝ (f ∘ (fun r => r • ‖x‖⁻¹ • x)) ‖x‖ 1 := by rfl
    _ = (fderiv ℝ f (‖x‖ • ‖x‖⁻¹ • x)) (_root_.deriv (fun r => r • ‖x‖⁻¹ • x) ‖x‖) := by
      rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
      simp
    _ = (fderiv ℝ f x) (_root_.deriv (fun r => r • ‖x‖⁻¹ • x) ‖x‖) := by
      have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      rw [smul_smul]
      field_simp
      simp
  rw [grad_inner_eq f x (‖x‖⁻¹ • x)]
  congr
  rw [deriv_smul_const (by fun_prop)]
  simp

lemma grad_inner_space {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, x⟫_ℝ = ‖x‖ * _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  rw [← grad_inner_space_unit_vector _ _ hd, inner_smul_right]
  by_cases hx : x = 0
  · subst hx
    simp
  have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-!

### B.11. Gradient of the norm squared function

-/

lemma grad_norm_sq (x : Space d) :
    ∇ (fun x => ‖x‖ ^ 2) x = (2 : ℝ) • x := by
  funext i
  rw [grad_eq_sum]
  simp [deriv_norm_sq, basis_apply]

/-!

### B.12. Gradient of the inner product function

-/

/-- The gradient of the inner product is given by `2 • x`. -/
lemma grad_inner {d : ℕ} :
    ∇ (fun y : Space d => ⟪y, y⟫_ℝ) = fun z => (2:ℝ) • z := by
  ext z i
  simp [Space.grad]
  rw [deriv]
  erw [fderiv_fun_sum]
  · simp
    rw [Finset.sum_eq_single i]
    · trans (fderiv ℝ (fun y => y i ^ 2) z) (EuclideanSpace.single i 1)
      · congr
        funext y
        ring
      trans deriv i ((fun x => x^ 2) ∘ fun y => y i) z
      · rfl
      rw [deriv, fderiv_comp]
      · simp
        rw [← deriv_eq]
        simp
      · fun_prop
      · fun_prop
    · intro b _ hb
      trans (fderiv ℝ (fun y => y b ^ 2) z) (EuclideanSpace.single i 1)
      · congr
        funext y
        ring
      trans deriv i ((fun x => x^ 2) ∘ fun y => y b) z
      · rfl
      rw [deriv, fderiv_comp]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
        smul_eq_mul, mul_eq_zero]
      · left
        rw [← deriv_eq]
        rw [deriv_component_diff]
        omega
      · fun_prop
      · fun_prop
    · simp
  · intro i _
    refine DifferentiableAt.inner ℝ ?_ ?_
    · fun_prop
    · fun_prop

lemma grad_inner_left {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪y, x⟫_ℝ) = fun _ => x := by
  ext z i
  simp [Space.grad]
  rw [deriv]
  erw [fderiv_fun_sum]
  · simp
    rw [Finset.sum_eq_single i]
    rw [fderiv_const_mul]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    trans x i * fderiv ℝ (Space.coordCLM i) z (EuclideanSpace.single i 1)
    · congr
      funext x
      simp [Space.coordCLM, Space.coord_apply]
    simp only [ContinuousLinearMap.fderiv]
    simp [Space.coordCLM, Space.coord_apply]
    · fun_prop
    · intro b hb _
      rw [fderiv_const_mul]
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_eq_zero]
      right
      trans fderiv ℝ (Space.coordCLM b) z (EuclideanSpace.single i 1)
      · congr
        funext x
        simp [Space.coordCLM, Space.coord_apply]
      simp only [ContinuousLinearMap.fderiv]
      simp [Space.coordCLM, Space.coord_apply]
      (expose_names; exact h)
      fun_prop
    · simp
  · intro i _
    apply DifferentiableAt.inner ℝ ?_ ?_
    fun_prop
    fun_prop

lemma grad_inner_right {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪x, y⟫_ℝ) = fun _ => x := by
  rw [← grad_inner_left x]
  congr
  funext y
  exact real_inner_comm y x

/-!

## C. Properties of the curl operator

-/

/-!

### C.1. The curl on the zero function

-/

@[simp]
lemma curl_zero : ∇ × (0 : Space → EuclideanSpace ℝ (Fin 3)) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, Pi.ofNat_apply, fderiv_fun_const, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-!

### C.2. The curl on a constant function

-/

@[simp]
lemma curl_const : ∇ × (fun _ : Space => v₃) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-!

### C.3. The curl distributes over addition

-/

lemma curl_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ × (f1 + f2) = ∇ × f1 + ∇ × f2 := by
  unfold curl coord basis
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Pi.add_apply, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    PiLp.add_apply, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.zero_eta]
    repeat rw [deriv_coord_add]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat assumption

/-!

### C.4. The curl distributes over scalar multiplication

-/

lemma curl_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ × (k • f) = k • ∇ × f := by
  unfold curl coord basis
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Pi.smul_apply, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.zero_eta]
    rw [deriv_coord_smul, deriv_coord_smul, mul_sub]
    simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul]
    repeat fun_prop

/-!

### C.5. The curl of a linear map is a linear map

-/

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma curl_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ × (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [curl_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [curl_smul]
    fun_prop

/-!

### C.6. Preliminary lemmas about second derivatives

-/

/-- Second derivatives distribute coordinate-wise over addition (all three components for div). -/
lemma deriv_coord_2nd_add (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[i] (fun x => ∂[u] (fun x => f x u) x + (∂[v] (fun x => f x v) x + ∂[w] (fun x => f x w) x)) =
    (∂[i] (∂[u] (fun x => f x u))) + (∂[i] (∂[v] (fun x => f x v))) +
    (∂[i] (∂[w] (fun x => f x w))) := by
  unfold deriv
  ext x
  rw [fderiv_fun_add, fderiv_fun_add]
  simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
  ring
  repeat fun_prop

/-- Second derivatives distribute coordinate-wise over subtraction (two components for curl). -/
lemma deriv_coord_2nd_sub (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[u] (fun x => ∂[v] (fun x => f x w) x - ∂[w] (fun x => f x v) x) =
    (∂[u] (∂[v] (fun x => f x w))) - (∂[u] (∂[w] (fun x => f x v))) := by
  unfold deriv
  ext x
  simp only [Pi.sub_apply]
  rw [fderiv_fun_sub]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply]
  repeat fun_prop

/-!

### C.7. The div of a curl is zero

-/

lemma div_of_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ ⬝ (∇ × f) = 0 := by
  unfold div curl Finset.sum coord basis
  ext x
  simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.univ_val_map, List.ofFn_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons,
    List.sum_nil, add_zero, Pi.zero_apply]
  rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub, deriv_coord_2nd_sub]
  simp only [Fin.isValue, Pi.sub_apply]
  rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
    deriv_commute fun x => f x 2]
  simp only [Fin.isValue, sub_add_sub_cancel', sub_self]
  repeat
    try apply contDiff_euclidean.mp
    exact hf

/-!

### C.8. The curl of a curl

-/

lemma curl_of_curl (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ × (∇ × f) = ∇ (∇ ⬝ f) - Δ f := by
  unfold laplacianVec laplacian div grad curl Finset.sum coord basis
  simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.univ_val_map, List.ofFn_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons,
    List.sum_nil, add_zero]
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Fin.reduceFinMk, Pi.sub_apply]
    rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub, deriv_coord_2nd_add]
    rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
      deriv_commute fun x => f x 2]
    simp only [Fin.isValue, Pi.sub_apply, Pi.add_apply]
    ring
    repeat
      try apply contDiff_euclidean.mp
      exact hf

/-!

## D. Properties of the divergence operator

-/

/-!

### D.1. The divergence on the zero function

-/

@[simp]
lemma div_zero : ∇ ⬝ (0 : Space d → EuclideanSpace ℝ (Fin d)) = 0 := by
  unfold div Space.deriv Finset.sum
  simp only [Pi.ofNat_apply, fderiv_fun_const, ContinuousLinearMap.zero_apply, Multiset.map_const',
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate, smul_zero]
  rfl

/-!

### D.2. The divergence on a constant function

-/

@[simp]
lemma div_const : ∇ ⬝ (fun _ : Space d => v) = 0 := by
  unfold div Space.deriv Finset.sum
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, Multiset.map_const',
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate, smul_zero]
  rfl

/-!

### D.3. The divergence distributes over addition

-/

lemma div_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ ⬝ (f1 + f2) = ∇ ⬝ f1 + ∇ ⬝ f2 := by
  unfold div
  simp only [Pi.add_apply]
  funext x
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr
  funext i
  simp [coord_apply, Space.deriv]
  rw [fderiv_fun_add]
  simp only [ContinuousLinearMap.add_apply]
  · fun_prop
  · fun_prop

/-!

### D.4. The divergence distributes over scalar multiplication

-/

lemma div_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ ⬝ (k • f) = k • ∇ ⬝ f := by
  unfold div
  simp only [Pi.smul_apply]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr
  funext i
  simp [coord_apply]
  simp [Space.deriv]
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  · fun_prop

/-!

### D.5. The divergence of a linear map is a linear map

-/

lemma div_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ ⬝ (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [div_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [div_smul]
    fun_prop

/-!

## E. Properties of the Laplacian operator

-/

lemma laplacian_eq_div_of_grad (f : Space → ℝ) :
    Δ f = ∇ ⬝ ∇ f := by
  unfold laplacian div grad Finset.sum coord basis
  simp only [Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero,
    EuclideanSpace.basisFun_apply, PiLp.inner_apply, EuclideanSpace.single_apply,
    RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

open InnerProductSpace

end Space

/-!

## F. Properites of derivatives of time

-/

namespace Time
lemma deriv_lorentzVector {d : ℕ} {f : Time → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin 1 ⊕ Fin d) :
    deriv (fun t => f t i) t = deriv (fun t => f t) t i := by
  rw [deriv_eq]
  change fderiv ℝ (EuclideanSpace.proj i ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq]
  · fun_prop
  · fun_prop

  end Time
