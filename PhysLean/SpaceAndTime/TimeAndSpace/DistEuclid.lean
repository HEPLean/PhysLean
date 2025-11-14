/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
import PhysLean.SpaceAndTime.Space.DistOfFunction
/-!
# Distributions of functions on spacetime

-/

noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open Time
open Space SchwartzMap

def distEuclid {d : ℕ} {n : ℕ} :
    (Fin n → (Time × Space d) →d[ℝ] ℝ) ≃ₗ[ℝ]
    ((Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun A := {
    toFun := fun ε μ => A μ ε
    map_add' ε1 ε2 := by
      funext μ
      simp
    map_smul' c ε := by
      funext μ
      simp
    cont := by fun_prop}
  invFun A := fun i => {
    toFun := fun ε => A ε i
    map_add' ε1 ε2 := by simp
    map_smul' c ε := by simp
    cont := by fun_prop}
  left_inv A := by
    ext ε
    simp
  right_inv A := by
    ext μ ε
    simp
  map_add' A1 A2 := by
    ext μ ε
    simp
  map_smul' c A := by
    ext μ ε
    simp

lemma distEuclid_apply {d n : ℕ} (A : Fin n → (Time × Space d) →d[ℝ] ℝ)
    (ε : 𝓢(Time × Space d, ℝ)) (μ : Fin n) :
    distEuclid A ε μ = A μ ε := by rfl

lemma distEuclid_symm_apply {d n : ℕ}
    (A : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin n))
    (μ : Fin n) (ε : 𝓢(Time × Space d, ℝ)) :
    distEuclid.symm A μ ε = A ε μ := by rfl

end Space

end
