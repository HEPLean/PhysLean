/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import PhysLean.Mathematics.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!

# Generalization of calculus results to `InnerProductSpace'`
-/
variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [InnerProductSpace' 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

-- todo: move this
theorem fderiv_inner_apply'
    {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : E) :
    fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ := by
  sorry

-- todo: move this
theorem deriv_inner_apply'
    {f g : ℝ → F} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  fderiv_inner_apply' hf hg 1

-- todo: move this
open RealInnerProductSpace in
@[fun_prop]
theorem DifferentiableAt.inner' {f g : E → F} {x}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x := sorry
