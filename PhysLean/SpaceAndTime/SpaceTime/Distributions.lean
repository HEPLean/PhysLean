/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Space.Distributions
import PhysLean.SpaceAndTime.SpaceTime.Basic
import PhysLean.Mathematics.Distribution.Function.OfFunction
import Mathlib.MeasureTheory.SpecificCodomains.WithLp


namespace SpaceTime

open Distribution
open SchwartzMap

/-!

## The constant distribution on SpaceTime

-/

/-- The constant distribution from `SpaceTime d` to a module `M` associated with
  `m : M`. -/
noncomputable def constD {M } [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    (SpaceTime d) →d[ℝ] M := const ℝ (SpaceTime d) m

/-!

## Derivatives

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

noncomputable def timeSliceD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    ((SpaceTime d) →d[ℝ] M) ≃L[ℝ] ((Time × Space d) →d[ℝ] M) where
  toFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ (SpaceTime.toTimeAndSpace (d := d))
  invFun f :=
    f ∘L SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ (SpaceTime.toTimeAndSpace (d := d)).symm
  left_inv f := by
    ext κ
    simp
    congr
    ext x
    simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  right_inv f := by
    ext κ
    simp
    congr
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp
  continuous_toFun := ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace).precomp M ).continuous
  continuous_invFun := ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace.symm).precomp M ).continuous


lemma timeSliceD_derivD_inl {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (SpaceTime d) →d[ℝ] M) :
    timeSliceD (derivD (Sum.inl 0) f) =
    Space.timeDerivD (timeSliceD f) := by
  ext ε
  simp [timeSliceD]
  rw [derivD_apply, Space.timeDerivD_apply]
  rw [fderivD_apply, fderivD_apply]
  simp
  congr 1
  ext x
  simp
  change ((fderivCLM ℝ) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε))
    x (Lorentz.Vector.basis (Sum.inl 0)) = ((fderivCLM ℝ) ε) (toTimeAndSpace x) (1, 0)
  trans SpaceTime.deriv (Sum.inl 0) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inl]
  simp [Time.deriv]
  change  (fderiv ℝ (ε ∘ (fun t =>  (t, (toTimeAndSpace x).2))) (toTimeAndSpace x).1) 1 = _
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk]
  simp
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
  simp
  apply timeSliceD.injective
  simp
  exact timeSliceD_derivD_inl f


lemma timeSliceD_derivD_inr {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    timeSliceD (derivD (Sum.inr i) f) =
    Space.spaceDerivD i (timeSliceD f) := by
  ext ε
  simp [timeSliceD]
  rw [derivD_apply, Space.spaceDerivD_apply]
  rw [fderivD_apply, fderivD_apply]
  simp
  congr 1
  ext x
  simp
  change ((fderivCLM ℝ) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε))
    x (Lorentz.Vector.basis (Sum.inr i)) = ((fderivCLM ℝ) ε) (toTimeAndSpace x) (0, Space.basis i)
  trans SpaceTime.deriv (Sum.inr i) ((compCLMOfContinuousLinearEquiv ℝ toTimeAndSpace) ε) x
  · rfl
  rw [SpaceTime.deriv_sum_inr]
  simp [Space.deriv]
  change  (fderiv ℝ (ε ∘ (fun y =>  ((toTimeAndSpace x).1, y))) (toTimeAndSpace x).2) _ = _
  rw [fderiv_comp, DifferentiableAt.fderiv_prodMk]
  simp
  congr 1
  simp
  rw [Space.basis]
  simp
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
  simp
  apply timeSliceD.injective
  simp
  exact timeSliceD_derivD_inr i f

end SpaceTime
