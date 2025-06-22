/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2

import PhysLean.Mathematics.InnerProductSpace.Adjoint
import PhysLean.Mathematics.FDerivCurry

/-!
# Adjoint Fréchet derivative

  `adjFDeriv 𝕜 f x = (fderiv 𝕜 f x).adjoint`

The main purpose of defining `adjFDeriv` is to compute `gradient f x = adjFDeriv 𝕜 f x 1`.
The advantage of working with `adjFDeriv` is that we can formulate composition theorem.

The reason why we do not want to compute `fderiv` and then `adjoint` is that to compute `fderiv 𝕜 f`
or `adjoint f` we decompose `f = f₁ ∘ ... ∘ fₙ` and then apply composition theorem. The problem is
that this decomposition has to be done differently for `fderiv` and `adjoint`. The problem is
that when working with `fderiv` the natural product type is `X × Y` but when working with `adjoint`
the natural product is `WithLp 2 (X × Y)`.
For example:
-/

noncomputable section

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

variable (𝕜) in
noncomputable
def adjFDeriv (f : E → F) (x : E) (dy : F) : E := adjoint 𝕜 (fderiv 𝕜 f x) dy

variable (𝕜) in
@[fun_prop]
structure HasAdjFDerivAt (f : E → F) (f' : F → E) (x : E) where
  differentiableAt : DifferentiableAt 𝕜 f x
  hasAdjoint_fderiv : HasAdjoint 𝕜 (fderiv 𝕜 f x) f'

protected theorem HasAdjFDerivAt.adjFDeriv {f : E → F} {f'} {x} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    adjFDeriv 𝕜 f x = f' := by
  unfold adjFDeriv; funext y;
  rw[hf.hasAdjoint_fderiv.adjoint]

open InnerProductSpace' in
protected theorem DifferentiableAt.hasAdjFDerivAt [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {x} (hf : DifferentiableAt 𝕜 f x) :
    HasAdjFDerivAt 𝕜 f (adjFDeriv 𝕜 f x) x where
  differentiableAt := hf
  hasAdjoint_fderiv := by
    unfold adjFDeriv
    apply HasAdjoint.congr_adj
    · apply ContinuousLinearMap.hasAdjoint
    · funext y; rw[ContinuousLinearMap.adjoint_eq_clm_adjoint]

theorem gradient_eq_adjFDeriv
    {f : U → 𝕜} {x : U} (hf : DifferentiableAt 𝕜 f x) :
    gradient f x = adjFDeriv 𝕜 f x 1 := by
  apply ext_inner_right 𝕜
  unfold gradient
  simp [ContinuousLinearMap.adjoint_inner_left,
        hf.hasAdjFDerivAt.hasAdjoint_fderiv.adjoint_inner_left]

attribute [fun_prop] HasAdjFDerivAt.differentiableAt

theorem hasAdjFDerivAt_id (x : E) : HasAdjFDerivAt 𝕜 (fun x : E => x) (fun dx => dx) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp; apply hasAdjoint_id

theorem adjFDeriv_id : adjFDeriv 𝕜 (fun x : E => x) = fun _ dx => dx := by
  funext x
  rw[HasAdjFDerivAt.adjFDeriv (hasAdjFDerivAt_id x)]

theorem hasAdjFDerivAt_const (x : E) (y : F) :
    HasAdjFDerivAt 𝕜 (fun _ : E => y) (fun _ => 0) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp; apply hasAdjoint_zero

theorem adjFDeriv_const (y : F) : adjFDeriv 𝕜 (fun _ : E => y) = fun _ _ => 0 := by
  funext x
  rw[HasAdjFDerivAt.adjFDeriv (hasAdjFDerivAt_const x y)]

theorem HasAdjFDerivAt.comp {f : F → G} {g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' (g x)) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f (g x)) (fun dz => g' (f' dz)) x where
  differentiableAt := by
    fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv_comp']
    exact hf.hasAdjoint_fderiv.comp hg.hasAdjoint_fderiv

theorem adjFDeriv_comp [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {f : F → G} {g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f (g x)) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f (g x)) x = fun dy => adjFDeriv 𝕜 g x (adjFDeriv 𝕜 f (g x) dy) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.comp
  apply hf.hasAdjFDerivAt
  apply hg.hasAdjFDerivAt

theorem HasAdjFDerivAt.prodMk {f : E → F} {g : E → G} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => (f x, g x)) (fun dyz => f' dyz.fst + g' dyz.snd) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [DifferentiableAt.fderiv_prodMk]
    apply HasAdjoint.prodMk
    · exact hf.hasAdjoint_fderiv
    · exact hg.hasAdjoint_fderiv

theorem HasAjdFDerivAt.fst {f : E → F×G} {f'} {x : E} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => (f x).fst) (fun dy => f' (dy, 0)) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv.fst]
    apply HasAdjoint.fst hf.hasAdjoint_fderiv

theorem adjFDeriv_fst [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
   {f : E → F×G} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => (f x).fst) x = fun dy => adjFDeriv 𝕜 f x (dy, 0) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.fst hf.hasAdjFDerivAt

theorem HasAjdFDerivAt.snd {f : E → F×G} {f'} {x : E} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => (f x).snd) (fun dz => f' (0, dz)) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv.snd]
    apply HasAdjoint.snd hf.hasAdjoint_fderiv

theorem adjFDeriv_snd [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {f : E → F×G} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => (f x).snd) x = fun dy => adjFDeriv 𝕜 f x (0, dy) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.snd hf.hasAdjFDerivAt

theorem hasAdjFDerivAt_uncurry {f : E → F → G} {xy} {fx' fy'}
    (hf : DifferentiableAt 𝕜 (↿f) xy)
    (hfx : HasAdjFDerivAt 𝕜 (f · xy.2) fx' xy.1) (hfy : HasAdjFDerivAt 𝕜 (f xy.1 ·) fy' xy.2) :
    HasAdjFDerivAt 𝕜 (↿f) (fun dz => (fx' dz, fy' dz)) xy where
  differentiableAt :=hf
  hasAdjoint_fderiv := by
    eta_expand
    simp (disch:=fun_prop) [fderiv_uncurry]
    apply HasAdjoint.congr_adj
    case adjoint =>
      apply HasAdjoint.add
      apply HasAdjoint.comp (g:=Prod.fst) hfx.hasAdjoint_fderiv (HasAdjoint.fst hasAdjoint_id)
      apply HasAdjoint.comp (g:=Prod.snd) hfy.hasAdjoint_fderiv (HasAdjoint.snd hasAdjoint_id)
    case eq =>
      simp

theorem adjFDeriv_uncurry [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {f : E → F → G} {xy} (hfx : DifferentiableAt 𝕜 (↿f) xy) :
    adjFDeriv 𝕜 (↿f) xy = fun dz => (adjFDeriv 𝕜 (f · xy.snd) xy.fst dz,
                                     adjFDeriv 𝕜 (f xy.fst ·) xy.snd dz) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply hasAdjFDerivAt_uncurry
  fun_prop
  apply DifferentiableAt.hasAdjFDerivAt (by fun_prop)
  apply DifferentiableAt.hasAdjFDerivAt (by fun_prop)


theorem HasAdjFDerivAt.neg {f : E → F} {f'} {x : E} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => - f x) (fun dy => - f' dy) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by simp; apply hf.hasAdjoint_fderiv.neg

theorem adjFDeriv_neg [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => - f x) x = fun dy => - adjFDeriv 𝕜 f x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.neg hf.hasAdjFDerivAt

theorem HasAjdFDerivAt.add {f g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f x + g x) (fun dy => f' dy + g' dy) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv_add]
    apply hf.hasAdjoint_fderiv.add hg.hasAdjoint_fderiv

theorem adjFDeriv_add [CompleteSpace E] [CompleteSpace F]
    {f g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f x + g x) x = fun dy => adjFDeriv 𝕜 f x dy + adjFDeriv 𝕜 g x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.add
  apply hf.hasAdjFDerivAt
  apply hg.hasAdjFDerivAt


theorem HasAdjFDerivAt.sub
    {f g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f x - g x) (fun dy => f' dy - g' dy) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv_sub]
    apply hf.hasAdjoint_fderiv.sub hg.hasAdjoint_fderiv

theorem adjFDeriv_sub [CompleteSpace E] [CompleteSpace F] {f g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f x - g x) x = fun dy => adjFDeriv 𝕜 f x dy - adjFDeriv 𝕜 g x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.sub
  apply hf.hasAdjFDerivAt
  apply hg.hasAdjFDerivAt

open ComplexConjugate in
theorem HasAdjFDerivAt.smul {f : E → F} {g : E → 𝕜} {f' g'}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => g x • f x ) (fun dy => conj (g x) • f' dy + g' (conj (inner 𝕜 dy (f x)))) x where
  differentiableAt := by fun_prop
  hasAdjoint_fderiv := by
    simp (disch:=fun_prop) [fderiv_smul]
    apply HasAdjoint.add
    · apply hf.hasAdjoint_fderiv.smul_left
    · apply hg.hasAdjoint_fderiv.smul_right

open ComplexConjugate in
theorem adjFDeriv_smul [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {g : E → 𝕜} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => g x • f x) x = fun dy => conj (g x) • adjFDeriv 𝕜 f x dy +
                                                   adjFDeriv 𝕜 g x (conj (inner 𝕜 dy (f x))) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.smul
  apply hf.hasAdjFDerivAt
  apply hg.hasAdjFDerivAt
