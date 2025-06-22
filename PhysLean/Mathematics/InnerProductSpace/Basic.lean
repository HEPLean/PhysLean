import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

class Norm₂ (E : Type*) where
  norm₂ : E → ℝ

export Norm₂ (norm₂)

notation:max "‖" x "‖₂" => norm₂ x


open RCLike ComplexConjugate

class InnerProductSpace' (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    extends Norm₂ E where
  core : InnerProductSpace.Core 𝕜 E
  /-- Norm induced by inner is topologicaly equivalent to the given norm -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    c > 0 ∧ d > 0 ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (core.inner x x)) ∧ (re (core.inner x x) ≤ d • ‖x‖^2)

section BasicInstances

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

end BasicInstances


section Constructions

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y


noncomputable
instance : InnerProductSpace' 𝕜 (E×F) where
  norm₂ := fun (x,y) => √ (‖x‖₂ ^ 2 + ‖y‖₂ ^ 2)
  core := {
    inner := fun xy xy' => ⟪xy.1,xy'.1⟫ + ⟪xy.2,xy'.2⟫
    conj_inner_symm := by intros; simp[inner,PreInnerProductSpace.Core.conj_inner_symm]
    re_inner_nonneg := by
      intro (x,y);
      have := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) inferInstance x
      have := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) inferInstance y
      simp[inner,PreInnerProductSpace.Core.re_inner_nonneg]
      linarith
    add_left := by
      intros; simp[PreInnerProductSpace.Core.add_left]; ring
    smul_left := by
      intros; simp[PreInnerProductSpace.Core.smul_left]; ring
    definite := by
      intros; sorry
  }
  inner_top_equiv_norm := sorry


variable {ι : Type*} [Fintype ι]

noncomputable
instance : InnerProductSpace' 𝕜 (ι → E) where
  norm₂ := fun x => √ (∑ i, ‖x i‖₂)
  core := {
    inner := fun x x' => ∑ i, ⟪x i, x' i⟫
    conj_inner_symm := by intros; simp[inner,PreInnerProductSpace.Core.conj_inner_symm]
    re_inner_nonneg := by
      intro x;
      have := fun i => PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) inferInstance (x i)
      simp[inner,PreInnerProductSpace.Core.re_inner_nonneg]
      sorry
    add_left := by
      intros; simp[PreInnerProductSpace.Core.add_left,Finset.sum_add_distrib]
    smul_left := by
      intros; simp[PreInnerProductSpace.Core.smul_left,Finset.mul_sum]
    definite := by
      intros; sorry
  }
  inner_top_equiv_norm := sorry


end Constructions
