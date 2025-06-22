import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

class Norm₂ (𝕜 : Type*) (E : Type*) where
  norm₂ (𝕜) : E → 𝕜

export Norm₂ (norm₂)

notation:max "‖" x "‖₂_" 𝕜:max => norm₂ 𝕜 x
notation:max "‖" x "‖₂" => norm₂ ℝ x

open RCLike ComplexConjugate

class InnerProductSpace' (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    extends Norm₂ 𝕜 E where
  core : InnerProductSpace.Core 𝕜 E
  /-- Norm induced by inner is topologicaly equivalent to the given norm -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    c > 0 ∧ d > 0 ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (core.inner x x)) ∧ (re (core.inner x x) ≤ d • ‖x‖^2)


variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance [inst : InnerProductSpace' 𝕜 E] : InnerProductSpace.Core 𝕜 E := inst.core

instance [inst : InnerProductSpace' 𝕜 E] : Inner 𝕜 E := inst.core.toInner

instance {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [inst : InnerProductSpace 𝕜 E] :
    InnerProductSpace' 𝕜 E where
  norm₂ x := ‖x‖
  core := inst.toCore
  inner_top_equiv_norm := by
    use 1; use 1
    simp[← norm_sq_eq_re_inner]
