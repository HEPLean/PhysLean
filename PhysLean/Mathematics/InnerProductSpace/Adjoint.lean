import PhysLean.Mathematics.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) in
structure HasAdjoint (f : E → F) (f' : F → E) where
  adjoint_inner_left (x : E) (y : F) : ⟪f' y, x⟫ = ⟪y, f x⟫

variable (𝕜) in
open Classical in
noncomputable
def adjoint (f : E → F) :=
  if h : ∃ f', HasAdjoint 𝕜 f f' then
    choose h
  else
    0


section InnerProductSpace

variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

theorem ContinuousLinearMap.hasAdjoint (f : E →L[𝕜] F) : HasAdjoint 𝕜 f f.adjoint where
  adjoint_inner_left := f.adjoint_inner_left

theorem ContinuousLinearMap.exists_hasAdjoint (f : E →L[𝕜] F) : ∃ f', HasAdjoint 𝕜 f f' :=
  ⟨f.adjoint,f.hasAdjoint⟩

theorem clm_adjoint_eq_adjoint (f : E →L[𝕜] F) :
    f.adjoint = _root_.adjoint 𝕜 f := by
  ext y; apply ext_inner_right 𝕜; intro x
  have hf := f.exists_hasAdjoint
  simp[_root_.adjoint,f.adjoint_inner_left,hf,hf.choose_spec.adjoint_inner_left]


end InnerProductSpace
