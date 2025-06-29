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
  [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace' ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℝ F] [InnerProductSpace' ℝ F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner ℝ x y
open InnerProductSpace'

 noncomputable def fderivInnerCLM' (p : E × E) : E × E →L[ℝ] ℝ :=
  isBoundedBilinearMap_inner'.deriv p

theorem HasFDerivAt.inner' {f g  : E → F}
  {f' g' : E →L[ℝ] F} (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM' (f x, g x)).comp <| f'.prod g') x := by
  exact isBoundedBilinearMap_inner' (E := F)
    |>.hasFDerivAt (f x, g x) |>.comp x (hf.prodMk hg)

-- todo: move this
theorem fderiv_inner_apply'
    {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : E) :
    fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ := by
   rw [(hf.hasFDerivAt.inner' hg.hasFDerivAt).fderiv]; rfl


-- todo: move this
theorem deriv_inner_apply'
    {f g : ℝ → F} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  fderiv_inner_apply' hf hg 1

-- todo: move this
@[fun_prop]
theorem DifferentiableAt.inner' {f g : E → F} {x}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x := by
  apply HasFDerivAt.differentiableAt
  exact hf.hasFDerivAt.inner' hg.hasFDerivAt
