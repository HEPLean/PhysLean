/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Distributions.Basic
import PhysLean.SpaceAndTime.SpaceTime.Basic
/-!

# Distributions on SpaceTime

## i. Overview

In this module we give the basic properties of distributions on `SpaceTime d`,
and derivatives thereof.

## ii. Key results

- `SpaceTime.constD d m` : the constant distribution on `SpaceTime d` with value `m`.
- `SpaceTime.timeSliceD` : the time slice of a distribution on `SpaceTime d` to a distribution
  on `Time × Space d`.
- `SpaceTime.derivD μ f` : the derivative of a distribution `f : (SpaceTime d) →d[ℝ] M` in
  direction `μ : Fin 1 ⊕ Fin d`.

## iii. Table of contents

- A. The constant distribution on SpaceTime
- B. The time slice of a distribution on SpaceTime
- C. Derivatives of distributions
  - C.1. Relationship between the time slice and derivatives

## iv. References

-/
namespace SpaceTime

open Distribution
open SchwartzMap

/-!

## A. The constant distribution on SpaceTime

-/

/-- The constant distribution from `SpaceTime d` to a module `M` associated with
  `m : M`. -/
noncomputable def constD {M } [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    (SpaceTime d) →d[ℝ] M := const ℝ (SpaceTime d) m

/-!

## B. The time slice of a distribution on SpaceTime

-/

/-- The time slice of a distribution on `SpaceTime d` to form a distribution
  on `Time × Space d`. -/
noncomputable def timeSliceD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight := 1) :
    ((SpaceTime d) →d[ℝ] M) ≃L[ℝ] ((Time × Space d) →d[ℝ] M) where
  toFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ (SpaceTime.toTimeAndSpace c (d := d))
  invFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv
      (F := ℝ) ℝ (SpaceTime.toTimeAndSpace c (d := d)).symm
  left_inv f := by
    ext κ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    congr
    ext x
    simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  right_inv f := by
    ext κ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    congr
    ext x
    simp
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp
  continuous_toFun := ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c)).precomp M).continuous
  continuous_invFun :=
    ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c).symm).precomp M).continuous

/-!

## C. Derivatives of distributions

-/

/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def derivD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
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

lemma derivD_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    (derivD μ f) ε = fderivD ℝ f ε (Lorentz.Vector.basis μ) := by
  simp [derivD, Distribution.fderivD]

/-!

### C.1. Relationship between the time slice and derivatives

-/

lemma timeSliceD_derivD_inl {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (f : (SpaceTime d) →d[ℝ] M) :
    timeSliceD c (derivD (Sum.inl 0) f) =
    Space.timeDerivD (timeSliceD c f) := by
  ext ε
  simp [timeSliceD]
  rw [derivD_apply, Space.timeDerivD_apply]
  rw [fderivD_apply, fderivD_apply]
  simp only [Fin.isValue, ContinuousLinearMap.coe_comp', Function.comp_apply, neg_inj]
  congr 1
  ext x
  simp only [Fin.isValue, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  change ((fderivCLM ℝ) ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c)) ε))
    x (Lorentz.Vector.basis (Sum.inl 0)) = ((fderivCLM ℝ) ε) (toTimeAndSpace c x) (1, 0)
  trans SpaceTime.deriv (Sum.inl 0) ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c)) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inl c]
  simp [Time.deriv]
  change (fderiv ℝ (ε ∘ (fun t => (t, (toTimeAndSpace c x).2))) (toTimeAndSpace c x).1) 1 = _
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk]
  simp only [Prod.mk.eta, fderiv_id', fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.zero_apply]
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact SchwartzMap.differentiable ε
  · fun_prop
  exact SchwartzMap.differentiable ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε)

lemma timeSliceD_symm_derivD_inl {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) :
    (derivD (Sum.inl 0) (timeSliceD.symm f)) =
    timeSliceD.symm (Space.timeDerivD f) := by
  obtain ⟨f, rfl⟩ := timeSliceD.surjective f
  simp only [Fin.isValue, ContinuousLinearEquiv.symm_apply_apply]
  apply timeSliceD.injective
  simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
  exact timeSliceD_derivD_inl f

lemma timeSliceD_derivD_inr {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    timeSliceD (derivD (Sum.inr i) f) =
    Space.spaceDerivD i (timeSliceD f) := by
  ext ε
  simp [timeSliceD]
  rw [derivD_apply, Space.spaceDerivD_apply]
  rw [fderivD_apply, fderivD_apply]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, neg_inj]
  congr 1
  ext x
  simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  change ((fderivCLM ℝ) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε))
    x (Lorentz.Vector.basis (Sum.inr i)) = ((fderivCLM ℝ) ε) (toTimeAndSpace 1 x) (0, Space.basis i)
  trans SpaceTime.deriv (Sum.inr i) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inr 1]
  simp [Space.deriv]
  change (fderiv ℝ (ε ∘ (fun y => ((toTimeAndSpace 1 x).1, y))) (toTimeAndSpace 1 x).2) _ = _
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk]
  simp only [Prod.mk.eta, fderiv_fun_const, Pi.zero_apply, fderiv_id',
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  congr 1
  simp only [Prod.mk.injEq, true_and]
  rw [Space.basis]
  simp only [EuclideanSpace.basisFun_apply]
  · fun_prop
  · fun_prop
  · apply Differentiable.differentiableAt
    exact SchwartzMap.differentiable ε
  · fun_prop
  · exact SchwartzMap.differentiable ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε)

lemma timeSliceD_symm_derivD_inr {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] (i : Fin d)
    (f : (Time × Space d) →d[ℝ] M) :
    (derivD (Sum.inr i) (timeSliceD.symm f)) =
    timeSliceD.symm (Space.spaceDerivD i f) := by
  obtain ⟨f, rfl⟩ := timeSliceD.surjective f
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  apply timeSliceD.injective
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact timeSliceD_derivD_inr i f

end SpaceTime
