/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.TODO.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# Temperature

In this module we define the type `Temperature`, and give basic properties thereof.

-/
open NNReal

/-- The type of temperatures. -/
def Temperature : Type := ℝ≥0

namespace Temperature
open Constants

noncomputable instance : LinearOrder Temperature :=
  Subtype.instLinearOrder _

/-- The underlying real-number associated with the tempature. -/
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T

noncomputable instance : Coe Temperature ℝ := ⟨toReal⟩

instance : TopologicalSpace Temperature := inferInstanceAs (TopologicalSpace ℝ≥0)

instance : Zero Temperature := ⟨0, Preorder.le_refl 0⟩

/-- The inverse temperature. -/
noncomputable def β (T : Temperature) : ℝ≥0 := ⟨1 / (kB * T), by
  apply div_nonneg
  · exact zero_le_one' ℝ
  · apply mul_nonneg
    · exact kB_nonneg
    · exact T.2⟩

/-- The temperature associated with a given inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ≥0) : Temperature :=
    ⟨1 / (kB * β), by
  apply div_nonneg
  · exact zero_le_one' ℝ
  · apply mul_nonneg
    · exact kB_nonneg
    · exact β.2⟩

lemma ofβ_eq : ofβ = fun β => ⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one' ℝ
    · apply mul_nonneg
      · exact kB_nonneg
      · exact β.2⟩ := by rfl

@[simp]
lemma β_ofβ (β' : ℝ≥0) : β (ofβ β') = β' := by
  simp [β, ofβ]
  ext
  change ((↑β' : ℝ)⁻¹ * (↑kB : ℝ)⁻¹)⁻¹ * (kB)⁻¹ = _
  field_simp [kB_neq_zero]

@[simp]
lemma ofβ_β (T : Temperature) : ofβ (β T) = T := by
  simp [ofβ_eq, β]
  apply Subtype.ext
  simp only [val_eq_coe]
  field_simp [kB_neq_zero]
  rfl

lemma ofβ_continuousOn : ContinuousOn (ofβ : ℝ≥0 → Temperature) (Set.Ioi 0) := by
  rw [ofβ_eq]
  refine continuousOn_of_forall_continuousAt ?_
  intro x h
  have h1 : ContinuousAt (fun x => 1 / (kB * x)) x.1 := by
    refine ContinuousAt.div₀ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · simp
      apply And.intro
      · exact kB_neq_zero
      · exact ne_of_gt h
  rw [@Metric.continuousAt_iff] at ⊢ h1
  intro ε hε
  obtain ⟨δ, hδ, h1⟩ := h1 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x h
  exact h1 h

lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (x : ℝ) => (ofβ (Real.toNNReal x)).1) (Set.Ioi 0) := by
  refine DifferentiableOn.congr (f := fun x => 1 / (kB * x)) ?_ ?_
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      simp only [ne_eq, mul_eq_zero, not_or]
      apply And.intro
      · exact kB_neq_zero
      · exact ne_of_gt hx
  · intro x hx
    simp [ofβ_eq]
    simp at hx
    left
    linarith

TODO "EQTKM" "Define the function from `Temperature` to `ℝ` which gives the temperature in
  Kelvin, based on axiomized constants. "

end Temperature
