/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Distributions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
/-!

# Translations on space

-/

section

variable
  {𝕜} [NontriviallyNormedField 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ  X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {ι : Type*} [Fintype ι] {Y' : ι → Type*} [∀ i, NormedAddCommGroup (Y' i)]
  [∀ i, NormedSpace 𝕜 (Y' i)] {Φ : X → ∀ i, Y' i} {x : X}

namespace Space


noncomputable instance {d} : VAdd (EuclideanSpace ℝ (Fin d)) (Space d) where
  vadd v s := v + s

noncomputable instance {d} : AddAction (EuclideanSpace ℝ (Fin d)) (Space d) where
  add_vadd v1 v2 s := by simp [add_assoc]
  zero_vadd s := by simp

/-!

## Translations of distributions

-/


open Distribution
open SchwartzMap


noncomputable def translateSchwartz {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    𝓢(Space d, X) →L[ℝ] 𝓢(Space d, X) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
      (g := fun x => x - a)
      (by
        apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖a‖)
        · have hx : (fderiv ℝ (fun x => x - a)) =
              fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
            funext x
            simp only
            erw [fderiv_sub]
            simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, sub_zero]
            fun_prop
            fun_prop
          rw [hx]
          exact
            Function.HasTemperateGrowth.const
              (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))
        · fun_prop
        · intro x
          simp only [pow_one]
          trans ‖x‖ + ‖a‖
          · apply norm_sub_le
          simp [mul_add, add_mul]
          trans 1 + (‖x‖ + ‖a‖)
          · simp
          trans (1 + (‖x‖ + ‖a‖)) + ‖x‖ * ‖a‖
          · simp
            positivity
          ring_nf
          rfl) (by
          simp only
          use 1, (1 + ‖a‖)
          intro x
          simp only [pow_one]
          apply (norm_le_norm_add_norm_sub' x a).trans
          trans 1 + (‖a‖ + ‖x - a‖)
          · simp
          trans (1 + (‖a‖ + ‖x - a‖)) + ‖a‖ * ‖x - a‖
          · simp
            positivity
          ring_nf
          rfl)

@[simp]
lemma translateSchwartz_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) (x : Space d) :
    translateSchwartz a η x = η (x - a) := rfl

lemma translateSchwartz_coe_eq {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) :
    (translateSchwartz a η : Space d → X) = fun x => η (x - a) := by
  ext
  simp

noncomputable def translateD {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    ((Space d) →d[ℝ] X) →ₗ[ℝ] ((Space d) →d[ℝ] X) where
  toFun T := T.comp (translateSchwartz (-a))
  map_add' T1 T2 := by
    ext η
    simp
  map_smul' c T := by
    simp

lemma translateD_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] X) (η : 𝓢(Space d, ℝ)) :
    translateD a T η = T (translateSchwartz (-a) η) := rfl

open InnerProductSpace

@[simp]
lemma translateD_gradD {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] ℝ) :
    gradD (translateD a T) = translateD a (gradD T) := by
  apply gradD_eq_of_inner
  intro η y
  rw [translateD_apply, gradD_inner_eq]
  rw [fderivD_apply, fderivD_apply, translateD_apply]
  congr 2
  ext x
  simp
  change fderiv ℝ η (x + a) y = fderiv ℝ _ x y
  rw [translateSchwartz_coe_eq]
  simp only [sub_neg_eq_add]
  rw [fderiv_comp_add_right]

open MeasureTheory
lemma translateD_ofFunction {d : ℕ} (a : EuclideanSpace ℝ (Fin d.succ))
    (f : Space d.succ → X) (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable f volume) :
    translateD a (ofFunction f hf hae) =
    ofFunction (fun x => f (x - a)) (IsDistBounded.comp_add_right hf fun i => -a i)
    (by
      change AEStronglyMeasurable (f ∘ fun x => x - a) volume
      rw [MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff (μb := volume)]
      · fun_prop
      · exact measurePreserving_sub_right volume a
      · exact measurableEmbedding_subRight a) := by
  ext η
  rw [translateD_apply, ofFunction_apply, ofFunction_apply]
  trans  ∫ (x : EuclideanSpace ℝ (Fin d.succ)), η ((x - a) + a) • f (x - a); swap
  · simp
  let f' := fun x : EuclideanSpace ℝ (Fin d.succ) => η (x  + a) • f (x)
  change _ = ∫ (x : EuclideanSpace ℝ (Fin d.succ)), f' (x - a)
  rw [MeasureTheory.integral_sub_right_eq_self]
  congr
  funext x
  simp [f']

@[simp]
lemma divD_translateD {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) ) :
    divD (translateD a T) = translateD a (divD T) := by
  ext η
  rw [divD_apply_eq_sum_fderivD]
  rw [translateD_apply, divD_apply_eq_sum_fderivD]
  congr
  funext i
  rw [fderivD_apply, fderivD_apply, translateD_apply]
  simp
  have h1 : ((translateSchwartz (-a)) ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis i)) ((fderivCLM ℝ) η)))
      = ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis i))
        ((fderivCLM ℝ) ((translateSchwartz (-a)) η))) := by
    ext x
    rw [translateSchwartz_apply]
    simp
    change fderiv ℝ η (x + a) (basis i) = fderiv ℝ _ x (basis i)
    rw [translateSchwartz_coe_eq]
    simp
    rw [fderiv_comp_add_right]
  rw [h1]


end Space
