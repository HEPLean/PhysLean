/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2

import PhysLean.Mathematics.Calculus.ProdL2

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
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

variable (𝕜) in
noncomputable
def adjFDeriv (f : E → F) (x : E) (dy : F) : E := (fderiv 𝕜 f x).adjoint dy

variable (𝕜) in
@[fun_prop]
structure HasAdjFDerivAt (f : E → F) (f' : F → E) (x : E) where
  differentiableAt : DifferentiableAt 𝕜 f x
  eq_adjoint_fderiv : f' = (fderiv 𝕜 f x).adjoint

protected theorem HasAdjFDerivAt.adjFDeriv {f : E → F} {f'} {x} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    adjFDeriv 𝕜 f x = f' := by
  unfold adjFDeriv; rw[hf.eq_adjoint_fderiv]

protected theorem DifferentiableAt.HasAdjFDerivAt {f : E → F} {x}
    (hf : DifferentiableAt 𝕜 f x) :
    HasAdjFDerivAt 𝕜 f (adjFDeriv 𝕜 f x) x where
  differentiableAt := hf
  eq_adjoint_fderiv := rfl

theorem gradient_eq_adjFDeriv {f : E → 𝕜} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    gradient f x = adjFDeriv 𝕜 f x 1 := sorry

attribute [fun_prop] HasAdjFDerivAt.differentiableAt

theorem hasAdjFDerivAt_id (x : E) : HasAdjFDerivAt 𝕜 (fun x : E => x) (fun dx => dx) x where
  differentiableAt := by fun_prop
  eq_adjoint_fderiv := by funext dx; simp

theorem adjFDeriv_id : adjFDeriv 𝕜 (fun x : E => x) = fun _ dx => dx := by
  funext x
  rw[HasAdjFDerivAt.adjFDeriv (hasAdjFDerivAt_id x)]

theorem hasAdjFDerivAt_const (x : E) (y : F) :
    HasAdjFDerivAt 𝕜 (fun _ : E => y) (fun _ => 0) x where
  differentiableAt := by fun_prop
  eq_adjoint_fderiv := by funext dx; simp

theorem adjFDeriv_const (y : F) : adjFDeriv 𝕜 (fun _ : E => y) = fun _ _ => 0 := by
  funext x
  rw[HasAdjFDerivAt.adjFDeriv (hasAdjFDerivAt_const x y)]

theorem HasAdjFDerivAt.comp {f : F → G} {g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' (g x)) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f (g x)) (fun dz => g' (f' dz)) x where
  differentiableAt := by
    fun_prop
  eq_adjoint_fderiv := by
    funext dx; simp (disch:=fun_prop)
      [fderiv_comp',ContinuousLinearMap.adjoint_comp,hf.eq_adjoint_fderiv,hg.eq_adjoint_fderiv]

theorem adjFDeriv_comp {f : F → G} {g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f (g x)) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f (g x)) x = fun dy => adjFDeriv 𝕜 g x (adjFDeriv 𝕜 f (g x) dy) := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.comp
  apply hf.HasAdjFDerivAt
  apply hg.HasAdjFDerivAt

theorem HasAdjFDerivAt.prod {f : E → F} {g : E → G} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜
      (fun x => (f x, g x)₂)
      (fun dyz => adjFDeriv 𝕜 f x dyz.fst + adjFDeriv 𝕜 g x dyz.snd) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    unfold adjFDeriv
    sorry

theorem HasAjdFDerivAt.fst {f : E → F×₂G} {f'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => (f x).fst) (fun dy => adjFDeriv 𝕜 f x (dy, 0)₂) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    unfold adjFDeriv
    sorry

theorem adjFDeriv_fst {f : E → F×₂G} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => (f x).fst) x = fun dy => adjFDeriv 𝕜 f x (dy, 0)₂ := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.fst hf.HasAdjFDerivAt

theorem HasAjdFDerivAt.snd {f : E → F×₂G} {f'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => (f x).snd) (fun dz => adjFDeriv 𝕜 f x (0, dz)₂) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    unfold adjFDeriv
    sorry

theorem adjFDeriv_snd {f : E → F×₂G} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => (f x).snd) x = fun dy => adjFDeriv 𝕜 f x (0, dy)₂ := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.snd hf.HasAdjFDerivAt

theorem hasAdjFDerivAt_uncurry {f : E → F → G} {x y} {fx' fy'}
    (hfx : HasAdjFDerivAt 𝕜 (f · y) fx' x) (hfy : HasAdjFDerivAt 𝕜 (f x ·) fy' y) :
    HasAdjFDerivAt 𝕜 (↿₂f) (fun dz => (fx' dz, fy' dz)₂) (x,y)₂ where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    sorry

theorem adjFDeriv_uncurry {f : E → F → G} {xy : E×₂F}
    (hfx : DifferentiableAt 𝕜 (↿f) xy) :
    adjFDeriv 𝕜 (↿₂f) xy = fun dz => (adjFDeriv 𝕜 (f · xy.snd) xy.fst dz,
                                         adjFDeriv 𝕜 (f xy.fst ·) xy.snd dz)₂ := by
  apply HasAdjFDerivAt.adjFDeriv
  apply hasAdjFDerivAt_uncurry
  apply DifferentiableAt.HasAdjFDerivAt (by fun_prop)
  apply DifferentiableAt.HasAdjFDerivAt (by fun_prop)


theorem HasAdjFDerivAt.neg {f : E → F} {f'} {x : E} (hf : HasAdjFDerivAt 𝕜 f f' x) :
    HasAdjFDerivAt 𝕜 (fun x => - f x) (fun dy => - f' dy) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    sorry

theorem adjFDeriv_neg {f : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f x) :
    adjFDeriv 𝕜 (fun x => - f x) x = fun dy => - adjFDeriv 𝕜 f x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.neg hf.HasAdjFDerivAt

theorem HasAjdFDerivAt.add {f g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f x + g x) (fun dy => f' dy + g' dy) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    sorry

theorem adjFDeriv_add {f g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f x + g x) x = fun dy => adjFDeriv 𝕜 f x dy + adjFDeriv 𝕜 g x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAjdFDerivAt.add
  apply hf.HasAdjFDerivAt
  apply hg.HasAdjFDerivAt


theorem HasAdjFDerivAt.sub {f g : E → F} {f' g'} {x : E}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => f x - g x) (fun dy => f' dy - g' dy) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    sorry

theorem adjFDeriv_sub {f g : E → F} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => f x - g x) x = fun dy => adjFDeriv 𝕜 f x dy - adjFDeriv 𝕜 g x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.sub
  apply hf.HasAdjFDerivAt
  apply hg.HasAdjFDerivAt

theorem HasAdjFDerivAt.smul {f : E → F} {g : E → 𝕜} {f' g'}
    (hf : HasAdjFDerivAt 𝕜 f f' x) (hg : HasAdjFDerivAt 𝕜 g g' x) :
    HasAdjFDerivAt 𝕜 (fun x => g x • f x ) (fun dy => g' (inner 𝕜 dy (f x)) + g x • f' dy) x where
  differentiableAt := by
    sorry
  eq_adjoint_fderiv := by
    sorry

theorem adjFDeriv_smul {f : E → F} {g : E → 𝕜} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    adjFDeriv 𝕜 (fun x => g x • f x) x = fun dy => adjFDeriv 𝕜 g x (inner 𝕜 dy (f x)) +
                                                   g x • adjFDeriv 𝕜 f x dy := by
  apply HasAdjFDerivAt.adjFDeriv
  apply HasAdjFDerivAt.smul
  apply hf.HasAdjFDerivAt
  apply hg.HasAdjFDerivAt
