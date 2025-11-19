/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.LorentzAction
/-!

# Derivatives on SpaceTime

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions and
distributions on `SpaceTime d`.

## ii. Key results

- `deriv` : The derivative of a function `SpaceTime d → M` along the `μ` coordinate.
- `deriv_sum_inr` : The derivative along a spatial coordinate in terms of the
  derivative on `Space d`.
- `deriv_sum_inl` : The derivative along the temporal coordinate in terms of the
  derivative on `Time`.
- `distDeriv` : The derivative of a distribution on `SpaceTime d` along the `μ` coordinate.
- `distDeriv_commute` : Derivatives of distributions on `SpaceTime d` commute.

## iii. Table of contents

- A. Derivatives of functions on `SpaceTime d`
  - A.1. The definition of the derivative
  - A.2. Basic equality lemmas
  - A.3. Derivative of the zero function
  - A.4. The derivative of a function composed with a Lorentz transformation
  - A.5. Spacetime derivatives in terms of time and space derivatives
- B. Derivatives of distributions
  - B.1. Commutation of derivatives of distributions
  - B.2. Lorentz group action on derivatives of distributions

## iv. References

-/
noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## A. Derivatives of functions on `SpaceTime d`

-/

/-!

### A.1. The definition of the derivative

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinate. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)

@[inherit_doc deriv]
scoped notation "∂_" => deriv

/-!

### A.2. Basic equality lemmas

-/

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
lemma deriv_eq {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    ∂_ μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

lemma differentiable_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, Differentiable ℝ (fun x => f x ν)) ↔ Differentiable ℝ f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · intro h ν
    change Differentiable ℝ (Lorentz.Vector.coordCLM ν ∘ f)
    apply Differentiable.comp
    · fun_prop
    · exact h

lemma contDiff_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, ContDiff ℝ n (fun x => f x ν)) ↔ ContDiff ℝ n f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    apply contDiff_pi'
    intro ν
    exact h ν
  · intro h ν
    change ContDiff ℝ n (Lorentz.Vector.coordCLM ν ∘ f)
    apply ContDiff.comp
    · fun_prop
    · exact h

lemma deriv_apply_eq {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f)
    (y : SpaceTime d) :
    ∂_ μ f y ν = fderiv ℝ (fun x => f x ν) y (Lorentz.Vector.basis μ) := by
  rw [deriv_eq]
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) y) (Lorentz.Vector.basis μ)
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

lemma fderiv_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f) (y dt : SpaceTime d) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f y dt ν = fderiv ℝ (fun x => f x ν) y dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) y) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

@[simp]
lemma deriv_coord {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => x ν) = if μ = ν then 1 else 0 := by
  change ∂_ μ (coordCLM ν) = _
  funext x
  rw [deriv_eq]
  simp only [ContinuousLinearMap.fderiv]
  simp [coordCLM]
  split_ifs
  rfl
  rfl

/-!

### A.3. Derivative of the zero function

-/

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

attribute [-simp] Fintype.sum_sum_type

/-!

### A.4. The derivative of a function composed with a Lorentz transformation

-/

lemma deriv_comp_lorentz_action {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d)
    (f : SpaceTime d → M) (hf : Differentiable ℝ f) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∂_ μ (fun x => f (Λ • x)) x = ∑ ν, Λ.1 ν μ • ∂_ ν f (Λ • x) := by
  change fderiv ℝ (f ∘ Lorentz.Vector.actionCLM Λ) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_comp]
  simp only [Lorentz.Vector.actionCLM_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
    -- Fintype.sum_sum_type
  rw [Lorentz.Vector.smul_basis]
  simp
  rfl
  · fun_prop
  · fun_prop

/-!

### A.5. Spacetime derivatives in terms of time and space derivatives

-/

lemma deriv_sum_inr {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) (i : Fin d) :
    ∂_ (Sum.inr i) f x
    = Space.deriv i (fun y => f ((toTimeAndSpace c).symm ((toTimeAndSpace c x).1, y)))
      (toTimeAndSpace c x).2 := by
  rw [deriv_eq, Space.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  congr 1
  rw [fderiv_comp']
  simp only [Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  change _ = (toTimeAndSpace c).symm ((fderiv ℝ ((toTimeAndSpace c x).1, ·) (toTimeAndSpace c x).2)
    (EuclideanSpace.single i 1))
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_fun_const, Pi.zero_apply, fderiv_id', ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  trans (toTimeAndSpace c).symm (0, Space.basis i)
  · rw [← toTimeAndSpace_basis_inr (c := c)]
    simp
  · congr
    rw [Space.basis]
    simp
  repeat' fun_prop

lemma deriv_sum_inl {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) :
    ∂_ (Sum.inl 0) f x
    = (1/(c : ℝ)) • Time.deriv (fun t => f ((toTimeAndSpace c).symm (t, (toTimeAndSpace c x).2)))
      (toTimeAndSpace c x).1 := by
  rw [deriv_eq, Time.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Fin.isValue, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  trans
    (fderiv ℝ f x)
      ((1 / c.val) • (fderiv ℝ (fun t => (toTimeAndSpace c).symm (t, ((toTimeAndSpace c) x).2))
      ((toTimeAndSpace c) x).1) 1)
  swap
  · exact ContinuousLinearMap.map_smul_of_tower (fderiv ℝ f x) (1 / c.val) _
  congr 1

  rw [fderiv_comp']
  simp only [Fin.isValue, Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [Fin.isValue, fderiv_id', fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.zero_apply]
  rw [← map_smul]
  rw [← toTimeAndSpace_basis_inl' (c := c)]
  simp only [Fin.isValue, ContinuousLinearEquiv.symm_apply_apply]
  repeat' fun_prop

/-!

## B. Derivatives of distributions

-/

open Distribution SchwartzMap
/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) : ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] (SpaceTime d) →d[ℝ] M where
  toFun f :=
    let ev : (SpaceTime d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (Lorentz.Vector.basis μ)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    distDeriv μ f ε = fderivD ℝ f ε (Lorentz.Vector.basis μ) := by
  simp [distDeriv, Distribution.fderivD]

/-!

### B.1. Commutation of derivatives of distributions

-/

open ContDiff
lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (distDeriv ν f) = distDeriv ν (distDeriv μ f) := by
  ext κ
  rw [distDeriv_apply, distDeriv_apply, fderivD_apply, fderivD_apply]
  rw [distDeriv_apply, distDeriv_apply, fderivD_apply, fderivD_apply]
  simp only [neg_neg]
  congr 1
  ext x
  change fderiv ℝ (fun x => fderiv ℝ κ x (Lorentz.Vector.basis μ)) x (Lorentz.Vector.basis ν) =
    fderiv ℝ (fun x => fderiv ℝ κ x (Lorentz.Vector.basis ν)) x (Lorentz.Vector.basis μ)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt (n := ∞)
    apply ContDiff.contDiffAt
    exact smooth κ ⊤
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop

/-!

### B.2. Lorentz group action on derivatives of distributions

We now show how the Lorentz group action on distributions interacts with derivatives.

-/

variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]

lemma _root_.SchwartzMap.sum_apply {α : Type} [NormedAddCommGroup α]
    [NormedSpace ℝ α]
    {ι : Type} [Fintype ι]
    (f : ι → 𝓢(α, ℝ)) (x : α) :
    (∑ i, f i) x = ∑ i, f i x := by
  let P (ι : Type) [Fintype ι] := ∀ (f : ι → 𝓢(α, ℝ)),
    (∑ i, f i) x = ∑ i, f i x
  revert f
  change P ι
  apply Fintype.induction_empty_option
  · intro ι1 ι2 _ e h1 f
    rw [← @e.sum_comp, ← @e.sum_comp, h1]
  · simp [P]
  · intro a _ ih f
    simp [Fintype.sum_option]
    rw [ih]

lemma distDeriv_comp_lorentz_action {μ : Fin 1 ⊕ Fin d} (Λ : LorentzGroup d)
    (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (Λ • f) = ∑ ν, Λ⁻¹.1 ν μ • (Λ • distDeriv ν f) := by
  symm
  trans (∑ ν, Λ • Λ⁻¹.1 ν μ • (distDeriv ν) f)
  · congr
    funext i
    rw [SMulCommClass.smul_comm]
  trans Λ • (∑ ν, Λ⁻¹.1 ν μ • (distDeriv ν) f)
  · exact Eq.symm Finset.smul_sum
  ext η
  rw [lorentzGroup_smul_dist_apply, distDeriv_apply, fderivD_apply,
    lorentzGroup_smul_dist_apply]
  rw [← smul_neg]
  congr
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
  conv_lhs =>
    enter [2, x]
    rw [distDeriv_apply, fderivD_apply]
    simp only [smul_neg]
    rw [← map_smul]
  rw [Finset.sum_neg_distrib]
  congr
  rw [← map_sum]
  congr
  /- Reduced to Schwartz maps -/
  ext x
  rw [SchwartzMap.sum_apply]
  symm
  simp [schwartzAction_apply]
  change ∂_ μ η (Λ • x) = ∑ ν, Λ⁻¹.1 ν μ • ∂_ ν (schwartzAction Λ⁻¹ η) (x)
  obtain ⟨η, rfl⟩ := schwartzAction_surjective Λ η
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul]
  rw [schwartzAction_mul_apply]
  simp only [inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  change ∂_ μ (fun x => η (Λ⁻¹ • x)) (Λ • x) = _
  rw [deriv_comp_lorentz_action]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, inv_smul_smul, smul_eq_mul]
  exact SchwartzMap.differentiable η

end SpaceTime

end
