import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-- L₂ norm on `E`.

In particular, on product types `X×Y` and pi types `ι → X` this class provides L₂ norm unlike `‖·‖`.
 -/
class Norm₂ (E : Type*) where
  norm₂ : E → ℝ

export Norm₂ (norm₂)

notation:max "‖" x "‖₂" => norm₂ x


open RCLike ComplexConjugate

/-- Effectively as `InnerProductSpace 𝕜 E` but it does not requires that `‖x‖^2 = ⟪x,x⟫`. It is
only required that they are equivalent `∃ (c > 0) (d > 0), c • ‖x‖^2 ≤ ⟪x,x⟫ ≤ d • ‖x‖^2`. The main
purpose of this class is to provide inner product space structure on product types `ExF` and
pi types `ι → E` without using `WithLp` gadget.

If you want to access L₂ norm use `‖x‖₂ := √⟪x,x⟫`.

This class induces `InnerProductSpace 𝕜 (WithLp 2 E)` which equips `‖·‖` on `X` with L₂ norm.
This is very useful when translating results from `InnerProductSpace` to `InnerProductSpace'`
together with `toL2 : E →L[𝕜] (WithLp 2 E)` and `fromL2 : (WithL2 2 E) →L[𝕜] E`.

In short we have these implications:
```
  InnerProductSpace 𝕜 E → InnerProductSpace' 𝕜 E
  InnerProductSpace' 𝕜 E → InnerProductSpace 𝕜 (WithLp 2 E)
```

The reason behind this type class is that with current mathlib design the requirement
`‖x‖^2 = ⟪x,x⟫` prevents us to give inner product space structure on product type `E×F` and pi
type `ι → E` as they are equipped with max norm. One has to work with `WithLp 2 (E×F)` and
`WithLp 2 (ι → E)`. This places quite a bit inconvenience on users in certain scenarios.
In particular, the main motivation behind this class is to make computations of `adjFDeriv` and
`gradient` easy.
-/
class InnerProductSpace' (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    extends Norm₂ E where
  core : InnerProductSpace.Core 𝕜 E
  norm₂_sq_eq_re_inner : ∀ x : E, ‖x‖₂ ^ 2 = re (core.inner x x)
  /-- Norm induced by inner is topologicaly equivalent to the given norm -/
  inner_top_equiv_norm : ∃ c d : ℝ,
    0 < c ∧ 0 < d ∧
    ∀ x : E, (c • ‖x‖^2 ≤ re (core.inner x x)) ∧ (re (core.inner x x) ≤ d • ‖x‖^2)

section BasicInstances

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance [inst : InnerProductSpace' 𝕜 E] : InnerProductSpace.Core 𝕜 E := inst.core

instance [inst : InnerProductSpace' 𝕜 E] : Inner 𝕜 E := inst.core.toInner

instance {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [inst : InnerProductSpace 𝕜 E] :
    InnerProductSpace' 𝕜 E where
  norm₂ x := ‖x‖
  core := inst.toCore
  norm₂_sq_eq_re_inner := norm_sq_eq_re_inner
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
  let core : InnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
  {
  dist_self := core.toNormedAddCommGroup.dist_self
  dist_comm := core.toNormedAddCommGroup.dist_comm
  dist_triangle := core.toNormedAddCommGroup.dist_triangle
  eq_of_dist_eq_zero := fun {x y} => core.toNormedAddCommGroup.eq_of_dist_eq_zero (x:=x) (y:=y)
  }

noncomputable
scoped instance toNormedSpaceWithL2 : NormedSpace 𝕜 (WithLp 2 E) where
  norm_smul_le := by
    let core : InnerProductSpace.Core (𝕜:=𝕜) (F:=E) := by infer_instance
    apply core.toNormedSpace.norm_smul_le


noncomputable
instance toInnerProductSpaceWithL2 : InnerProductSpace 𝕜 (WithLp 2 E) where
  norm_sq_eq_re_inner := by intros; simp [norm, Real.sq_sqrt,hE.core.re_inner_nonneg]; rfl
  conj_inner_symm := hE.core.conj_inner_symm
  add_left := hE.core.add_left
  smul_left := hE.core.smul_left

variable (𝕜) in
noncomputable
def toL2 : E →L[𝕜] WithLp 2 E where
  toFun := (WithLp.equiv 2 _).symm
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use √d
      constructor
      · apply Real.sqrt_pos.2 hd
      · intro x
        have h := Real.sqrt_le_sqrt (h x).2
        simp [smul_eq_mul] at h
        exact h

variable (𝕜) in
noncomputable
def fromL2 : WithLp 2 E →L[𝕜] E where
  toFun := (WithLp.equiv 2 _)
  map_add' := by simp
  map_smul' := by simp
  cont := by
    apply IsBoundedLinearMap.continuous (𝕜:=𝕜)
    constructor
    · constructor <;> simp
    · obtain ⟨c,d,hc,hd,h⟩ := InnerProductSpace'.inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
      use (√c)⁻¹
      have hc : 0 < √c := Real.sqrt_pos.2 hc
      constructor
      · apply inv_pos.2 hc
      · intro x
        have h := Real.sqrt_le_sqrt (h x).1
        simp [smul_eq_mul,norm] at h
        apply (le_inv_mul_iff₀' hc).2
        exact h

theorem fromL2_inner_left (x : WithLp 2 E) (y : E) : ⟪fromL2 𝕜 x, y⟫ = ⟪x, toL2 𝕜 y⟫ := rfl
theorem toL2_inner_left (x : E) (y : WithLp 2 E) : ⟪toL2 𝕜 x, y⟫ = ⟪x, fromL2 𝕜 y⟫ := rfl

@[simp]
theorem toL2_fromL2 (x : WithLp 2 E) : toL2 𝕜 (fromL2 𝕜 x) = x := rfl
@[simp]
theorem fromL2_toL2 (x : E) : fromL2 𝕜 (toL2 𝕜 x) = x := rfl

variable (𝕜 E) in
noncomputable
def equivL2 : (WithLp 2 E) ≃L[𝕜] E where
  toFun := fromL2 𝕜
  invFun := toL2 𝕜
  map_add' := (fromL2 𝕜).1.1.2
  map_smul' := (fromL2 𝕜).1.2
  left_inv := by intro _; rfl
  right_inv := by intro _; rfl
  continuous_toFun := (fromL2 𝕜).2
  continuous_invFun := (toL2 𝕜).2

instance [CompleteSpace E] : CompleteSpace (WithLp 2 E) := by
  have e := (equivL2 𝕜 E)
  have he := ContinuousLinearEquiv.isUniformEmbedding e
  apply (completeSpace_congr (α:=WithLp 2 E) (β:=E) (e:=e) he).2
  infer_instance

end InnerProductSpace'

open InnerProductSpace'

variable (𝕜) in

theorem ext_inner_left' {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y :=
  ext_inner_left (E:=WithLp 2 E) 𝕜 h

variable (𝕜) in
theorem ext_inner_right' {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
  ext_inner_right (E:=WithLp 2 E) 𝕜 h

@[simp]
theorem inner_conj_symm' (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  inner_conj_symm (E:=WithLp 2 E) x y

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

theorem inner_sub_left' (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
  inner_sub_left (E:=WithLp 2 E) x y z

theorem inner_sub_right' (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
  inner_sub_right (E:=WithLp 2 E) x y z

@[simp]
theorem inner_neg_left' (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ :=
  inner_neg_left (E:=WithLp 2 E) x y

@[simp]
theorem inner_neg_right' (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ :=
  inner_neg_right (E:=WithLp 2 E) x y

@[simp]
theorem inner_self_eq_zero' {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  inner_self_eq_zero (E:=WithLp 2 E)

@[fun_prop]
theorem Continuous.inner' {α} [TopologicalSpace α] (f g : α → E)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => ⟪f a, g a⟫) :=
  have hf : Continuous (fun x => toL2 𝕜 (f x)) := by fun_prop
  have hg : Continuous (fun x => toL2 𝕜 (g x)) := by fun_prop
  Continuous.inner (𝕜:=𝕜) (E:=WithLp 2 E) hf hg

section Real

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [InnerProductSpace' ℝ F]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem real_inner_self_nonneg' {x : F} : 0 ≤ re (⟪x, x⟫) :=
  real_inner_self_nonneg (F:=WithLp 2 F)

@[fun_prop]
theorem ContDiffAt.inner' {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  have hf : ContDiffAt ℝ n (fun x => toL2 ℝ (f x)) x := by fun_prop
  have hg : ContDiffAt ℝ n (fun x => toL2 ℝ (g x)) x := by fun_prop
  hf.inner ℝ hg

@[fun_prop]
theorem ContDiff.inner' {f g : E → F}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => ⟪f x, g x⟫) :=
  have hf : ContDiff ℝ n (fun x => toL2 ℝ (f x)) := by fun_prop
  have hg : ContDiff ℝ n (fun x => toL2 ℝ (g x)) := by fun_prop
  hf.inner ℝ hg

end Real

end InnerProductSpace'


section Constructions

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local instance : Inner 𝕜 (E×F) := ⟨fun (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫⟩

@[simp]
theorem prod_inner_apply' (x y : (E × F)) : ⟪x, y⟫ = ⟪x.fst, y.fst⟫ + ⟪x.snd, y.snd⟫ := rfl

open InnerProductSpace' in
noncomputable
instance : InnerProductSpace' 𝕜 (E×F) where
  norm₂ := (WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)).toNorm.norm
  core :=
    let _ := WithLp.instProdNormedAddCommGroup 2 (WithLp 2 E) (WithLp 2 F)
    let inst := (WithLp.instProdInnerProductSpace (𝕜:=𝕜) (WithLp 2 E) (WithLp 2 F)).toCore
    inst
  norm₂_sq_eq_re_inner := by
    intro (x,y)
    have hx : re ⟪(WithLp.equiv 2 E) x, (WithLp.equiv 2 E) x⟫ = re ⟪x,x⟫ := rfl
    have hy : re ⟪(WithLp.equiv 2 F) y, (WithLp.equiv 2 F) y⟫ = re ⟪y,y⟫ := rfl
    have : 0 ≤ re ⟪x,x⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=E) _ x
    have : 0 ≤ re ⟪y,y⟫ := PreInnerProductSpace.Core.re_inner_nonneg (𝕜:=𝕜) (F:=F) _ y
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceDIte, ENNReal.ofNat_ne_top, ↓reduceIte, hx,
         ENNReal.toReal_ofNat, Real.rpow_two, hy, one_div, prod_inner_apply', map_add]
    repeat rw [Real.sq_sqrt (by assumption)]
    norm_num
    rw[← Real.rpow_mul_natCast (by linarith)]
    simp
  inner_top_equiv_norm := by
    obtain ⟨c₁,d₁,hc₁,hd₁,h₁⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=E)
    have h₁₁ := fun x => (h₁ x).1
    have h₁₂ := fun x => (h₁ x).2
    obtain ⟨c₂,d₂,hc2,hd₂,h₂⟩ := inner_top_equiv_norm (𝕜:=𝕜) (E:=F)
    have h₂₁ := fun x => (h₂ x).1
    have h₂₂ := fun x => (h₂ x).2
    use min c₁ c₂; use 2 * max d₁ d₂
    constructor
    · positivity
    constructor
    · positivity
    · intro (x,y)
      have : 0 ≤ re ⟪y, y⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      have : 0 ≤ re ⟪x, x⟫ := by apply PreInnerProductSpace.Core.re_inner_nonneg
      simp
      constructor
      · by_cases h : ‖x‖ ≤ ‖y‖
        · have : max ‖x‖ ‖y‖ ≤ ‖y‖ := by simp[h]
          calc _ ≤ c₂ * ‖y‖ ^ 2 := by gcongr; simp
               _ ≤ re ⟪y,y⟫ := h₂₁ y
               _ ≤ _ := by simpa
        · have : max ‖x‖ ‖y‖ ≤ ‖x‖ := by simp at h; simp[h]; linarith
          calc _ ≤ c₁ * ‖x‖ ^ 2 := by gcongr; simp
               _ ≤ re ⟪x,x⟫ := h₁₁ x
               _ ≤ _ := by simpa
      · by_cases h : re ⟪x,x⟫ ≤ re ⟪y,y⟫
        · calc _ ≤ re ⟪y,y⟫ + re ⟪y,y⟫ := by simp[h]
               _ ≤ d₂ * ‖y‖ ^ 2 + d₂ * ‖y‖ ^ 2 := by gcongr <;> exact h₂₂ y
               _ ≤ _ := by ring_nf; gcongr <;> simp
        · have h : re ⟪y,y⟫ ≤ re ⟪x,x⟫ := by linarith
          calc _ ≤ re ⟪x,x⟫ + re ⟪x,x⟫ := by simp[h]
               _ ≤ d₁ * ‖x‖ ^ 2 + d₁ * ‖x‖ ^ 2 := by gcongr <;> exact h₁₂ x
               _ ≤ _ := by ring_nf; gcongr <;> simp


open InnerProductSpace' in
noncomputable
instance {ι : Type*} [Fintype ι] : InnerProductSpace' 𝕜 (ι → E) where
  norm₂ := (PiLp.seminormedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))).toNorm.norm
  core :=
    let _ := PiLp.normedAddCommGroup 2 (fun _ : ι => (WithLp 2 E))
    let inst := (PiLp.innerProductSpace (𝕜:=𝕜) (fun _ : ι => (WithLp 2 E)))
    inst.toCore
  norm₂_sq_eq_re_inner := by
    intro x
    simp only [norm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      Real.rpow_two, one_div]
    conv_rhs => rw [inner]
    simp [InnerProductSpace.toCore, InnerProductSpace.toInner, PiLp.innerProductSpace]
    rw [← Real.rpow_two, ← Real.rpow_mul]
    swap
    · apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg √(re ⟪(WithLp.equiv 2 E) (x i), (WithLp.equiv 2 E) (x i)⟫)
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, Real.rpow_one]
    congr
    funext i
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two,
      ← Real.rpow_mul InnerProductSpace.Core.inner_self_nonneg]
    simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, Real.rpow_one]
    rfl
  inner_top_equiv_norm := by
    rename_i i1 i2 i3 i4 i5 i6 i7 i8
    by_cases hnEmpty : Nonempty ι
    · obtain ⟨c, d, c_pos, d_pos, h⟩ := i1.inner_top_equiv_norm
      use c, Fintype.card ι * d
      simp_all
      constructor
      · positivity
      intro x
      obtain ⟨i, hi⟩ : ∃ i, ‖x‖  = ‖x i‖  := by
          simp  [norm]
          obtain ⟨i,_, hi⟩:= Finset.exists_mem_eq_sup (Finset.univ : Finset ι) (
            Finset.univ_nonempty_iff.mpr hnEmpty) (fun i => ‖x i‖₊)
          rw [hi]
          use i
          simp
      have hj : ∀ j,  ‖x j‖ ≤ ‖x i‖ := by
        rw [← hi]
        exact fun j => norm_le_pi_norm x j
      rw [hi]
      constructor
      · apply le_trans (h (x i)).1
        conv_rhs => rw [inner]
        simp [InnerProductSpace.toCore, InnerProductSpace.toInner, PiLp.innerProductSpace]
        have h1 := Finset.sum_le_univ_sum_of_nonneg  (f := fun i => re (@inner 𝕜 (WithLp 2 E) toInnerProductSpaceWithL2.2 (x i) (x i)))
          (s := {i}) (by
            intro i
            simp
            exact InnerProductSpace.Core.inner_self_nonneg)
        apply le_trans _ h1
        simp
      · have h2 := (h (x i)).2
        conv_lhs => rw [inner]
        simp [InnerProductSpace.toCore, InnerProductSpace.toInner, PiLp.innerProductSpace]
        trans ∑ j, d * ‖x j‖ ^ 2
        · refine Finset.sum_le_sum ?_
          intro j _
          exact (h (x j)).2
        trans (Fintype.card ι) • (d * ‖x i‖ ^ 2)
        swap
        · apply le_of_eq
          ring
        apply Finset.sum_le_card_nsmul
        intro j _
        refine mul_le_mul_of_nonneg (by simp) ?_ (by positivity) (by positivity)
        refine (sq_le_sq₀ ?_ ?_).mpr (hj j)
        · exact norm_nonneg (x j)
        · exact norm_nonneg (x i)
    · simp at hnEmpty
      use 1, 1
      simp
      intro x
      refine le_antisymm_iff.mp ?_
      have h1 : x = fun _ => 0 := by
        funext i
        have hn : ¬ IsEmpty ι := by
          simp
          use i
        exact False.elim (hn hnEmpty)
      subst h1
      simp [norm]
      rw [inner]
      simp [InnerProductSpace.toCore, InnerProductSpace.toInner, PiLp.innerProductSpace]

end Constructions
#check NormedSpace
