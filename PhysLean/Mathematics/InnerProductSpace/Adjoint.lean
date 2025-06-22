import PhysLean.Mathematics.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [hE : InnerProductSpace' 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [hF : InnerProductSpace' 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) in
structure HasAdjoint (f : E → F) (f' : F → E) where
  adjoint_inner_left (x : E) (y : F) : ⟪f' y, x⟫ = ⟪y, f x⟫

open Classical in
variable (𝕜) in
noncomputable
def adjoint (f : E → F) :=
  if h : ∃ f', HasAdjoint 𝕜 f f' then
    choose h
  else 0


-- evaluate ContinuousLinearMap.adjoint on normal function `f : E → F`
open Classical InnerProductSpace' in
variable (𝕜) in
noncomputable
def adjoint' [CompleteSpace E] [CompleteSpace F] (f : E → F) : F → E :=
  if h : IsLinearMap 𝕜 f ∧ Continuous f then
    let f : (WithLp 2 E) →L[𝕜] (WithLp 2 F) :=
      ⟨⟨⟨f,h.1.1⟩, h.1.2⟩,
       (by eta_expand; simp; rw[(by rfl : f = fun x => toL2 𝕜 (f (fromL2 𝕜 x)))];
           have := h.2
           apply Continuous.comp; fun_prop
           apply Continuous.comp; apply h.2
           fun_prop)⟩
    fun y => fromL2 𝕜 (f.adjoint (toL2 𝕜 y))
  else
    0


open InnerProductSpace' in
theorem ContinuousLinearMap.hasAdjoint [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    HasAdjoint 𝕜 f (fun y => fromL2 𝕜 (((toL2 𝕜) ∘L f ∘L (fromL2 𝕜)).adjoint (toL2 𝕜 y))) where
  adjoint_inner_left := by intros; simp[inner_fromL2_left,adjoint_inner_left]; rfl


open InnerProductSpace' in
theorem ContinuousLinearMap.adjoint_eq_clm_adjoint [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    _root_.adjoint 𝕜 f = fun y => fromL2 𝕜 ((toL2 𝕜 ∘L f ∘L fromL2 𝕜).adjoint (toL2 𝕜 y)) := by
  funext y; apply ext_inner_right' 𝕜; intro x
  rw [f.hasAdjoint.adjoint_inner_left]
  have h : ∃ f', HasAdjoint 𝕜 f f' := ⟨_,f.hasAdjoint⟩
  simp[_root_.adjoint,h,h.choose_spec.adjoint_inner_left]

-- section InnerProductSpace

-- variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
--   [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
--   [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
--   [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

-- theorem ContinuousLinearMap.hasAdjoint (f : E →L[𝕜] F) : HasAdjoint 𝕜 f f.adjoint where
--   adjoint_inner_left := f.adjoint_inner_left

-- theorem ContinuousLinearMap.exists_hasAdjoint (f : E →L[𝕜] F) : ∃ f', HasAdjoint 𝕜 f f' :=
--   ⟨f.adjoint,f.hasAdjoint⟩

-- open InnerProductSpace' in
-- theorem clm_adjoint_eq_adjoint (f : E →L[𝕜] F) :
--     f.adjoint = _root_.adjoint 𝕜 f := by
--   ext y; apply ext_inner_right 𝕜; intro x
--   have h : ∃ f', HasAdjoint 𝕜 f f' := ⟨f.adjoint, f.hasAdjoint⟩
--   simp [_root_.adjoint]
--   simp[ContinuousLinearMap.adjoint_inner_left,h,h.choose_spec.adjoint_inner_left]


-- open InnerProductSpace' in
-- theorem clm_adjoint_eq_adjoint' (f : E →L[𝕜] F) :
--     f.adjoint = _root_.adjoint' 𝕜 f := by
--   ext y; apply ext_inner_right 𝕜; intro x
--   have h₁ : IsLinearMap 𝕜 f := ⟨f.1.1.2,f.1.2⟩
--   have h₂ : Continuous f := by fun_prop
--   simp [_root_.adjoint', h₁, h₂];
--   rw[ContinuousLinearMap.adjoint_inner_left]
--   have h (x y : WithLp 2 E) : inner 𝕜 (E:=E) x y = inner 𝕜 (E:=WithLp 2 E) x y := by rfl
--   conv => rhs; rw[h]
--   rw[ ContinuousLinearMap.adjoint_inner_left]
--   rfl

-- end InnerProductSpace

theorem HasAdjoint.adjoint
    {f : E → F} {f' : F → E}
    (hf : HasAdjoint 𝕜 f f') : adjoint 𝕜 f = f' := by
  funext y
  apply ext_inner_right' 𝕜
  unfold _root_.adjoint
  have h : ∃ f', HasAdjoint 𝕜 f f' := ⟨f', hf⟩
  have := h.choose_spec.adjoint_inner_left
  simp_all
  simp [hf.adjoint_inner_left]

theorem HasAdjoint.congr_adj (f : E → F) (f' g')
   (adjoint : HasAdjoint 𝕜 f g')
   (eq : g' = f') : HasAdjoint 𝕜 f f' := by simp[← eq,adjoint]

theorem hasAdjoint_id : HasAdjoint 𝕜 (fun x : E => x) (fun x => x) := by
  constructor; intros; rfl

theorem hasAdjoint_zero : HasAdjoint 𝕜 (fun _ : E => (0 : F)) (fun _ => 0) := by
  constructor; intros; simp

theorem HasAdjoint.comp {f : F → G} {g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f (g x)) (fun x => g' (f' x)) := by
  constructor; intros; simp[hf.adjoint_inner_left, hg.adjoint_inner_left]

theorem HasAdjoint.prodMk {f : E → F} {g : E → G} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => (f x, g x)) (fun yz => f' yz.1 + g' yz.2) := by
  constructor; intros
  simp[inner,inner_add_left',
       hf.adjoint_inner_left, hg.adjoint_inner_left]

theorem HasAdjoint.fst {f : E → F×G} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => (f x).1) (fun y => f' (y, 0)) := by
  constructor; intros
  simp[inner, hf.adjoint_inner_left]

theorem HasAdjoint.snd {f : E → F×G} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => (f x).2) (fun z => f' (0, z)) := by
  constructor; intros
  simp[inner, hf.adjoint_inner_left]

theorem HasAdjoint.neg {f : E → F} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => -f x) (fun y => -f' y) := by
  constructor; intros
  simp[inner, hf.adjoint_inner_left]

theorem HasAdjoint.add {f g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f x + g x) (fun y => f' y + g' y) := by
  constructor; intros
  simp[inner, inner_add_left', inner_add_right',
       hf.adjoint_inner_left, hg.adjoint_inner_left]

theorem HasAdjoint.sub {f g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f x - g x) (fun y => f' y - g' y) := by
  constructor; intros
  simp[inner, sub_eq_add_neg, inner_add_left', inner_add_right',
       hf.adjoint_inner_left, hg.adjoint_inner_left]

open ComplexConjugate in
theorem HasAdjoint.smul_left {f : E → F} {f'} (c : 𝕜)
    (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => c • f x) (fun y => (conj c) • f' y) := by
  constructor; intros
  simp[inner, inner_smul_left', inner_smul_right', hf.adjoint_inner_left]

open ComplexConjugate in
theorem HasAdjoint.smul_right {f : E → 𝕜} {f'} (v : F)
    (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => f x • v) (fun y => f' (conj ⟪y, v⟫)) := by
  constructor; intros
  simp[inner, inner_smul_left', inner_smul_right', hf.adjoint_inner_left]
