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

/-- The time slice of a distribution on `SpaceTime d` to forma a distribution
  on `Time × Space d`. -/
noncomputable def timeSliceD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    ((SpaceTime d) →d[ℝ] M) ≃L[ℝ] ((Time × Space d) →d[ℝ] M) where
  toFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ (SpaceTime.toTimeAndSpace (d := d))
  invFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv
      (F := ℝ) ℝ (SpaceTime.toTimeAndSpace (d := d)).symm
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
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp
  continuous_toFun := ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace).precomp M).continuous
  continuous_invFun :=
    ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace.symm).precomp M).continuous

lemma timeSliceD_symm_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (η : 𝓢(SpaceTime d, ℝ)) :
    timeSliceD.symm f η = f (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace.symm η) :=
  rfl

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
    (f : (SpaceTime d) →d[ℝ] M) :
    timeSliceD (derivD (Sum.inl 0) f) =
    Space.timeDerivD (timeSliceD f) := by
  ext ε
  simp [timeSliceD]
  rw [derivD_apply, Space.timeDerivD_apply]
  rw [fderivD_apply, fderivD_apply]
  simp only [Fin.isValue, ContinuousLinearMap.coe_comp', Function.comp_apply, neg_inj]
  congr 1
  ext x
  simp only [Fin.isValue, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  change ((fderivCLM ℝ) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε))
    x (Lorentz.Vector.basis (Sum.inl 0)) = ((fderivCLM ℝ) ε) (toTimeAndSpace x) (1, 0)
  trans SpaceTime.deriv (Sum.inl 0) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inl]
  simp [Time.deriv]
  change (fderiv ℝ (ε ∘ (fun t => (t, (toTimeAndSpace x).2))) (toTimeAndSpace x).1) 1 = _
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
    x (Lorentz.Vector.basis (Sum.inr i)) = ((fderivCLM ℝ) ε) (toTimeAndSpace x) (0, Space.basis i)
  trans SpaceTime.deriv (Sum.inr i) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inr]
  simp [Space.deriv]
  change (fderiv ℝ (ε ∘ (fun y => ((toTimeAndSpace x).1, y))) (toTimeAndSpace x).2) _ = _
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

/-!

## D. Lorentz actions on distributions

-/

open ContDiff
/-- The continuous linear map translating Schwartz maps. -/
noncomputable def lorentzActionSchwartz {d : ℕ} (Λ : LorentzGroup d) :
    𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SpaceTime d, ℝ) := by
  refine SchwartzMap.compCLM (𝕜 := ℝ) (g := Lorentz.Vector.actionCLM (Λ⁻¹)) ?_ ?_
  · apply And.intro
    · fun_prop
    · intro n
      match n with
      | 0 =>
        simp
        use 1, ‖Lorentz.Vector.actionCLM (Λ⁻¹)‖
        intro x
        apply le_trans (ContinuousLinearMap.le_opNorm (Lorentz.Vector.actionCLM Λ⁻¹) x)
        simp [mul_add]
      | 1 =>
        have h1 (x : SpaceTime d) :
            ‖iteratedFDeriv ℝ 1 (⇑(Lorentz.Vector.actionCLM Λ⁻¹)) x‖ =
              ‖Lorentz.Vector.actionCLM Λ⁻¹‖ := by
          rw [iteratedFDeriv_succ_eq_comp_right]
          simp
        use 1, ‖Lorentz.Vector.actionCLM (Λ⁻¹)‖
        intro x
        rw [h1]
        simp [mul_add]
        positivity
      | .succ (.succ n) =>
        have h1 (x : SpaceTime d) :
            ‖iteratedFDeriv ℝ (n.succ.succ) (⇑(Lorentz.Vector.actionCLM Λ⁻¹)) x‖ = 0 := by
          rw [iteratedFDeriv_succ_eq_comp_right]
          simp [iteratedFDeriv_succ_const]
          exact ContinuousMultilinearMap.opNorm_zero
        use 0, 1
        intro x
        rw [h1]
        simp
  · use 1, ‖Lorentz.Vector.actionCLM (Λ)‖
    intro x
    obtain ⟨x, rfl⟩ := (Lorentz.Vector.actionCLM_surjective Λ) x
    apply le_trans (ContinuousLinearMap.le_opNorm (Lorentz.Vector.actionCLM Λ) x)
    simp [Lorentz.Vector.actionCLM_apply, mul_add]

lemma lorentzActionSchwartz_apply {d : ℕ} (Λ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    lorentzActionSchwartz Λ η x = η ((Λ⁻¹) • x) := by
  simp [lorentzActionSchwartz, SchwartzMap.compCLM_apply, Lorentz.Vector.actionCLM_apply]

lemma lorentzActionSchwartz_mul {d : ℕ} (Λ1 Λ2 : LorentzGroup d) :
    (lorentzActionSchwartz (Λ2 * Λ1)) =
    (lorentzActionSchwartz Λ2).comp (lorentzActionSchwartz Λ1) := by
  ext η x
  simp [lorentzActionSchwartz_apply, mul_smul]

@[simp]
lemma lorentzActionSchwartz_id {d : ℕ} :
    (lorentzActionSchwartz (1 : LorentzGroup d)) =
    ContinuousLinearMap.id ℝ (𝓢(SpaceTime d, ℝ)) := by
  ext η x
  simp [lorentzActionSchwartz_apply, one_smul]

noncomputable instance {d} :
    SMul (LorentzGroup d) ((SpaceTime d) →d[ℝ] Lorentz.Vector d) where
  smul Λ f := (Lorentz.Vector.actionCLM Λ).comp (f.comp  (lorentzActionSchwartz Λ⁻¹))

lemma distribution_smul_lorentzGroup_eq {d} (Λ : LorentzGroup d)
    (f : (SpaceTime d) →d[ℝ] Lorentz.Vector d) :
    (Λ • f)  = (Lorentz.Vector.actionCLM Λ).comp (f.comp  (lorentzActionSchwartz Λ⁻¹)) := by rfl

lemma distribution_smul_lorentzGroup_apply {d} (Λ : LorentzGroup d)
    (f : (SpaceTime d) →d[ℝ] Lorentz.Vector d) (η : 𝓢(SpaceTime d, ℝ)) :
    (Λ • f) η = Λ • (f (lorentzActionSchwartz Λ⁻¹ η)) := by
  simp [distribution_smul_lorentzGroup_eq, ContinuousLinearMap.comp_apply]
  rfl

noncomputable instance {d} :
    MulAction (LorentzGroup d) ((SpaceTime d) →d[ℝ] Lorentz.Vector d) where
  one_smul f := by
    ext η
    simp [distribution_smul_lorentzGroup_apply]
  mul_smul Λ1 Λ2 f := by
    ext η
    simp [distribution_smul_lorentzGroup_apply, mul_smul, lorentzActionSchwartz_mul]

lemma distribution_mulAction_lorentzGroup_derivD {d} (Λ : LorentzGroup d)
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] Lorentz.Vector d) :
    Λ • (derivD μ f) = derivD μ (Λ • f) := by
  ext η
  rw [distribution_smul_lorentzGroup_apply, derivD_apply, derivD_apply,
  fderivD_apply, fderivD_apply]
  simp [distribution_smul_lorentzGroup_apply]
  congr 1
  ext x
  change fderiv ℝ  (⇑((lorentzActionSchwartz Λ⁻¹) η)) _ _ = fderiv ℝ _ _ _
  have h1 : (⇑((lorentzActionSchwartz Λ⁻¹) η)) = η ∘ ( Lorentz.Vector.actionCLM (Λ)) := by
    ext x
    simp [lorentzActionSchwartz_apply]
    rfl
  rw [h1]
  rw [fderiv_comp]
  simp
  sorry



end SpaceTime
