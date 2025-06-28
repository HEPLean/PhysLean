/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

import PhysLean.Mathematics.VariationalCalculus.Basic
import PhysLean.Mathematics.InnerProductSpace.Calculus
import PhysLean.Mathematics.InnerProductSpace.Adjoint
import PhysLean.Mathematics.Calculus.Divergence
import PhysLean.Mathematics.Calculus.AdjFDeriv
/-!
# Variational adjoint

Definition of adjoint of linear function between function spaces. It is inspired by the definition
of distributional adjoint of linear maps between test functions as described here:
https://en.wikipedia.org/wiki/Distribution_(mathematics) under 'Preliminaries: Transpose of a linear
operator' but we require that the adjoint is function between test functions too.

The key results are:
  - variational adjoint is unique on test functions
  - variational adjoint of identity is identity, `HasVarAdjoint.id`
  - variational adjoint of composition is composition of adjoint in reverse order,
    `HasVarAdjoint.comp`
  - variational adjoint of deriv is `- deriv`, `HasVarAdjoint.deriv`
  - variational adjoint of algebraic operations is algebraic operation of adjoints,
    `HasVarAdjoint.neg`, `HasVarAdjoint.add`, `HasVarAdjoint.sub`, `HasVarAdjoint.mul_left`,
    `HasVarAdjoint.mul_right`, `HasVarAdjoint.smul_left`, `HasVarAdjoint.smul_right`
-/

open InnerProductSpace MeasureTheory ContDiff

section

variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V}
  {W}

/-- Function transformation `F` is localizable if the values of the transformed function `F φ` on
some compact set `K` can depend only on the values of `φ` on some another compact set `L`. -/
def IsLocalizedFunctionTransform (F : (X → U) → (Y → V)) : Prop :=
  ∀ (K : Set Y) (_ : IsCompact K), ∃ L : Set X,
    IsCompact L ∧ ∀ (φ φ' : X → U), (∀ x ∈ L, φ x = φ' x) → ∀ x ∈ K, F φ x = F φ' x
end
namespace IsLocalizedFunctionTransform

section
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V}
  {W}
lemma comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (F ∘ G) := by
  intro K cK
  obtain ⟨K', cK', h'⟩ := hF K cK
  obtain ⟨K'', cK'', h''⟩ := hG K' cK'
  use K''
  constructor
  · exact cK''
  · intro φ φ' hφ
    apply h' _ _ (fun _ hx' => h'' _ _ hφ _ hx')

lemma fun_comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun x => F (G x)) := by
  apply comp hF hG

@[simp]
lemma id : IsLocalizedFunctionTransform (id : (Y → V) → (Y → V)) := by
  intro K cK
  use K
  constructor
  · exact cK
  · intro φ φ' hφ
    intro x hx
    simp
    rw [hφ x hx]

lemma neg {V} [NormedAddCommGroup V] [Module ℝ V]
    {F : (X → U) → (Y → V)} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ => - F φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  exact ⟨L,cL,by intro _ _ _ _ _; dsimp; congr 1; apply h <;> simp_all⟩

lemma add {V} [NormedAddCommGroup V] [Module ℝ V] {F G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun φ => F φ + G φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  obtain ⟨L',cL',h'⟩ := hG K cK
  use L ∪ L'
  constructor
  · exact cL.union cL'
  · intro φ φ' hφ
    have hL : ∀ x ∈ L, φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    have hL' : ∀ x ∈ L', φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    simp +contextual (disch:=assumption) [h φ φ', h' φ φ']
end
section
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasureSpace Z]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [InnerProductSpace' ℝ W]

lemma mul_left {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ}  (hF : IsLocalizedFunctionTransform F )  :
    IsLocalizedFunctionTransform (fun φ x => ψ x * F φ x) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  refine ⟨L,cL, ?_⟩
  intro _ _ hφ _ _;
  simp
  left
  apply h
  · simp_all
  · simp_all

end
end IsLocalizedFunctionTransform
