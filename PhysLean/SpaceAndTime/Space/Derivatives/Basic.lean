/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import PhysLean.Mathematics.Distribution.Function.OfFunction
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
/-!

# Derivatives on Space

In this module, we define the the type `Space d` which corresponds
to a `d`-dimensional Euclidean space and prove some properties about it.

PhysLean sits downstream of Mathlib, and above we import the necessary Mathlib modules
which contain (perhaps transitively through imports) the definitions and theorems we need.

-/

namespace Space

/-!

## A. Derivatives of functions on `Space d`

-/

/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
noncomputable def deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) : Space d → M :=
  (fun x => fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)))

@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)

/-!

### A.1. Basic equalities

-/

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)) := by
  rfl

lemma deriv_eq_fderiv_basis [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by
  rw [deriv_eq]
  congr 1
  funext i
  simp only [EuclideanSpace.single_apply, basis_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

/-!

### A.2. Derivative of the constant function

-/

@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) (μ : Fin d) :
    deriv μ (fun _ => m) t = 0 := by
  rw [deriv]
  simp



/-!

### A.3. Derivative distributes over addition

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

### A.4. Derivative distributes over scalar multiplication

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

### A.5. Two spatial derivatives commute

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

### A.6. Derivative of a component

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

### A.7. Derivative of a component squared

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

### A.8. Derivivatives of components

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

### A.9. Derivative of a norm squared

-/

/-!

#### A.9.1. Differentiability of the norm squared function

-/
@[fun_prop]
lemma norm_sq_differentiable : Differentiable ℝ (fun x : Space d => ‖x‖ ^ 2) := by
  simp [@PiLp.norm_sq_eq_of_L2]
  fun_prop

/-!

#### A.9.2. Derivative of the norm squared function

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

### A.9. Derivative of the inner product

-/

open InnerProductSpace

/-!

#### A.10.1. Differentiability of the inner product function

-/

/-- The inner product is differentiable. -/
lemma inner_differentiable {d : ℕ} :
    Differentiable ℝ (fun y : Space d => ⟪y, y⟫_ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  fun_prop

/-!

#### A.10.2. Derivative of the inner product function

-/

lemma deriv_eq_inner_self (x : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x⟫_ℝ) x = 2 * x i := by
  convert deriv_norm_sq x i
  exact real_inner_self_eq_norm_sq _

/-!

### A.11. Differentiability of derivatives

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

## B. Derivatives of distributions on `Space d`

-/

open Distribution SchwartzMap

/-!

### B.1. The definition

-/
/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) : ((Space d) →d[ℝ] M) →ₗ[ℝ] (Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (basis μ)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp


/-!

### B.2. Basic equality

-/

lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : (Space d) →d[ℝ] M) (ε : 𝓢(Space d, ℝ)) :
    (distDeriv μ f) ε = fderivD ℝ f ε (basis μ) := by
  simp [distDeriv, Distribution.fderivD]


/-!

### B.3. Commutation of derivatives

-/

lemma schwartMap_fderiv_comm { d}
    (μ ν : Fin d) (x : Space d) (η : 𝓢(Space d, ℝ)) :
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis μ))
      ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis ν)) ((fderivCLM ℝ) η)))) x =
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis ν))
      ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis μ)) ((fderivCLM ℝ) η)))) x := by
  have h1 := η.smooth
  have h2 := h1 2
  change fderiv ℝ (fun x => fderiv ℝ η x (basis ν)) x (basis μ) =
    fderiv ℝ (fun x => fderiv ℝ η x (basis μ)) x (basis ν)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  apply ContDiffAt.isSymmSndFDerivAt (n := 2)
  · refine ContDiff.contDiffAt ?_
    exact h2
  · simp
  · fun_prop
  · exact differentiableAt_const (basis μ)
  · fun_prop
  · exact differentiableAt_const (basis ν)

lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin d) (f : (Space d) →d[ℝ] M) :
    (distDeriv ν (distDeriv μ f)) = (distDeriv μ (distDeriv ν f)) := by
  ext η
  simp [distDeriv, Distribution.fderivD]
  congr 1
  ext x
  rw [schwartMap_fderiv_comm μ ν x η]

end Space
