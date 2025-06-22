import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.WithLp

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


section InnerProductSpace'

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [hE : InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _


namespace InnerProductSpace'

noncomputable
scoped instance toNormWithL2 : Norm (WithLp 2 E) where
  norm x := √ (RCLike.re ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E x⟫)

noncomputable
scoped instance toInnerWithL2 : Inner 𝕜 (WithLp 2 E) where
  inner x y := ⟪WithLp.equiv 2 E x, WithLp.equiv 2 E y⟫

noncomputable
scoped instance toNormedAddCommGroupWitL2 : NormedAddCommGroup (WithLp 2 E) :=
  {
    dist_self := sorry
    dist_comm := sorry
    dist_triangle := sorry
    eq_of_dist_eq_zero := sorry
  }

noncomputable
scoped instance toNormedSpaceWithL2 : NormedSpace 𝕜 (WithLp 2 E) where
  norm_smul_le := sorry

noncomputable
instance toInnerProductSpaceWithL2 :
     InnerProductSpace 𝕜 (WithLp 2 E) where
  norm_sq_eq_re_inner := sorry --by intros; simp [norm, Real.sq_sqrt,hE.core.re_inner_nonneg]
  conj_inner_symm := hE.core.conj_inner_symm
  add_left := hE.core.add_left
  smul_left := hE.core.smul_left

instance [CompleteSpace E] : CompleteSpace (WithLp 2 E) := sorry


variable (𝕜) in
noncomputable
def toL2 : E →L[𝕜] WithLp 2 E := ⟨⟨⟨(WithLp.equiv 2 _).symm, sorry⟩, sorry⟩, sorry⟩

variable (𝕜) in
noncomputable
def fromL2 : WithLp 2 E →L[𝕜] E := ⟨⟨⟨(WithLp.equiv 2 _), sorry⟩, sorry⟩, sorry⟩

theorem inner_fromL2_left (x : WithLp 2 E) (y : E) : ⟪fromL2 𝕜 x, y⟫ = ⟪x, toL2 𝕜 y⟫ := rfl
theorem inner_toL2_left (x : E) (y : WithLp 2 E) : ⟪toL2 𝕜 x, y⟫ = ⟪x, fromL2 𝕜 y⟫ := rfl

@[simp]
theorem toL2_fromL2 (x : WithLp 2 E) : toL2 𝕜 (fromL2 𝕜 x) = x := rfl
@[simp]
theorem fromL2_toL2 (x : E) : fromL2 𝕜 (toL2 𝕜 x) = x := rfl

end InnerProductSpace'

open InnerProductSpace'

variable (𝕜) in

theorem ext_inner_left' {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
  ext_inner_left (E:=WithLp 2 E) 𝕜 h

variable (𝕜) in
theorem ext_inner_right' {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  ext_inner_right (E:=WithLp 2 E) 𝕜 h

theorem inner_smul_left' (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left (E:=WithLp 2 E) x y r

theorem inner_smul_right' (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right (E:=WithLp 2 E) x y r

@[simp]
theorem inner_zero_left' (x : E) : ⟪0, x⟫ = 0 :=
  inner_zero_left (E:=WithLp 2 E) x

@[simp]
theorem inner_zero_right' (x : E) : ⟪x, 0⟫ = 0 :=
  inner_zero_right (E:=WithLp 2 E) x


theorem inner_add_left' (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  inner_add_left (E:=WithLp 2 E) x y z

theorem inner_add_right' (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
  inner_add_right (E:=WithLp 2 E) x y z

@[simp]
theorem inner_neg_left' (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ :=
  inner_neg_left (E:=WithLp 2 E) x y

@[simp]
theorem inner_neg_right' (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ :=
  inner_neg_right (E:=WithLp 2 E) x y

@[simp]
theorem inner_self_eq_zero' {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  inner_self_eq_zero (E:=WithLp 2 E)

end InnerProductSpace'


section Constructions

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open InnerProductSpace'
noncomputable
instance : InnerProductSpace' 𝕜 (E×F) where
  norm₂ := (WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)).toNorm.norm
  core := {
    -- let inst := (WithLp.instProdInnerProductSpace (𝕜:=𝕜) (WithLp 2 E) (WithLp 2 F)).toCore
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
