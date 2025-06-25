/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
noncomputable
def divergence (f : E → E) (x : E) : 𝕜 := (fderiv 𝕜 f x).toLinearMap.trace _ _

@[simp]
theorem divergence_zero : divergence 𝕜 (fun x : E => 0) = fun _ => 0 := sorry

theorem divergence_prodMk (f : E×F → E) (g : E×F → F) (xy : E×F) :
    divergence 𝕜 (fun xy : E×F => (f xy, g xy)) xy
    =
    divergence 𝕜 (fun x' => f (x',xy.2)) xy.1
    +
    divergence 𝕜 (fun y' => g (xy.1,y')) xy.2 := sorry
