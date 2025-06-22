/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

abbrev ProdL2 (X Y : Type*) := WithLp 2 (X×Y)

macro X:term " ×₂ " Y:term : term => `(ProdL2 $X $Y)

variable {X Y : Type*}

def WithLp.prodMk (x : X) (y : Y) : X×₂Y := (x,y)
def WithLp.fst (xy : X ×₂ Y) : X := xy.1
def WithLp.snd (xy : X ×₂ Y) : Y := xy.2

open Lean Parser in
/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))

syntax "(" term ", " term,* ")₂" : term
macro_rules
| `(( $x:term, $y:term )₂) =>
  `(WithLp.prodMk $x $y)
| `(( $x:term, $y:term, $xs:term,* )₂) => do
  `(( $x, ( $y, $xs,* )₂)₂)

namespace WithLp

@[simp]
theorem prodMk_fst (x : X) (y : Y) :
  (x, y)₂.fst = x := rfl

@[simp]
theorem prodMk_snd (x : X) (y : Y) :
  (x, y)₂.snd = y := rfl


class HasUncurry (α : Type*) (β : outParam Type*) (γ : outParam Type*) where
  uncurry : α → β → γ

notation:arg "↿₂" x:arg => WithLp.HasUncurry.uncurry x

instance hasUncurryBase : HasUncurry (α → β) α β :=
  ⟨fun x => x⟩

instance hasUncurryInduction {β γ δ} [HasUncurry β γ δ] : HasUncurry (α → β) (α ×₂ γ) δ :=
  ⟨fun f p ↦ (↿₂(f p.fst)) p.snd⟩


variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]


section ToMathlib

variable {e : Y ≃L[𝕜] Z} {f : X → Y}

@[fun_prop]
theorem ContinuousLinearEquiv.continuous (hf : Continuous f) : Continuous (fun x => e (f x)) := sorry

set_option trace.Meta.Tactic.fun_prop.attr true in
@[fun_prop]
theorem ContinuousLinearEquiv.differentiable (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (fun x => e (f x)) := sorry

@[fun_prop]
theorem ContinuousLinearEquiv.differentiableAt (hf : DifferentiableAt 𝕜 f x) :
   DifferentiableAt 𝕜 (fun x => e (f x)) x := sorry

@[fun_prop]
theorem ContinuousLinearEquiv.contDif (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => e (f x)) := sorry

@[fun_prop]
theorem ContinuousLinearEquiv.contDiffAt (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => e (f x)) x := sorry

end ToMathlib


variable (𝕜 X Y) in
def prodL2Equiv :
    (WithLp 2 (X × Y) ≃L[𝕜] X × Y) :=
    ⟨⟨⟨⟨fun x => x,sorry⟩,sorry⟩,fun x => x,(by intro _; simp),(by intro _; simp)⟩,sorry,sorry⟩

def _root_.ContinuousLinearMap.prodL2 (f : X →L[𝕜] Y) (g : X →L[𝕜] Z) : X →L[𝕜] Y×₂Z :=
    ⟨⟨⟨fun x => (f x, g x), sorry⟩, sorry⟩, sorry⟩

variable (𝕜 X Y) in
def _root_.ContinuousLinearMap.WithLp.fst : (X×₂Y) →L[𝕜] X :=
    ContinuousLinearMap.fst 𝕜 X Y ∘L prodL2Equiv 𝕜 X Y

variable (𝕜 X Y) in
def _root_.ContinuousLinearMap.WithLp.snd : (X×₂Y) →L[𝕜] Y :=
    ContinuousLinearMap.snd 𝕜 X Y ∘L prodL2Equiv 𝕜 X Y

@[simp]
theorem ContinuousLinearMap.WithLp.fst_apply (x : X×₂Y) :
  ContinuousLinearMap.WithLp.fst 𝕜 X Y x = x.fst := rfl

@[simp]
theorem ContinuousLinearMap.WithLp.snd_apply (x : X×₂Y) :
  ContinuousLinearMap.WithLp.snd 𝕜 X Y x = x.snd := rfl

variable (𝕜) in
theorem mk_as_clm : (prodMk : X → Y → X×₂Y) = fun x y => (prodL2Equiv 𝕜 X Y).symm (x,y) := rfl
variable (𝕜) in
theorem fst_as_clm : (fst : (X×₂Y) → X) = ContinuousLinearMap.WithLp.fst 𝕜 X Y := rfl
variable (𝕜) in
theorem snd_as_clm : (snd : (X×₂Y) → Y) = ContinuousLinearMap.WithLp.snd 𝕜 X Y := rfl

@[fun_prop]
theorem prodMk_continuous (f : X → Y) (g : X → Z)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x, g x)₂) := sorry

@[fun_prop]
theorem prodMk_differentiableAt (f : X → Y) (g : X → Z) (x : X)
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x => (f x, g x)₂) x := by
  simp only [mk_as_clm 𝕜]; fun_prop

@[fun_prop]
theorem prodMk_contDiffAt (f : X → Y) (g : X → Z) (x : X)
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => (f x, g x)₂) x := by
  simp only [mk_as_clm 𝕜]; fun_prop

@[fun_prop]
theorem fst_differentiable :
    Differentiable 𝕜 (fun xy : X×₂Y => xy.fst) := by
  simp only [fst_as_clm 𝕜]; fun_prop

@[fun_prop]
theorem fst_contDiff :
    ContDiff 𝕜 n (fun xy : X×₂Y => xy.fst) := by
  simp only [fst_as_clm 𝕜]; fun_prop

@[fun_prop]
theorem snd_differentiable :
    Differentiable 𝕜 (fun xy : X×₂Y => xy.snd) := by
  simp only [snd_as_clm 𝕜]; fun_prop

@[fun_prop]
theorem snd_contDiff :
   ContDiff 𝕜 n (fun xy : X×₂Y => xy.snd) := by
  simp only [snd_as_clm 𝕜]; fun_prop

theorem fderiv_prodMk {f : X → Y} {g : X → Z} {x : X}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x => (f x, g x)₂) x = (fderiv 𝕜 f x).prodL2 (fderiv 𝕜 g x) := by
  sorry

theorem fderiv_fst : fderiv 𝕜 (fun xy : X×₂Y => xy.fst) = fun _ => ContinuousLinearMap.WithLp.fst 𝕜 X Y := by
  funext x; ext dx
  simp only [fst_as_clm 𝕜]
  rw[fderiv_clm_apply (by fun_prop) (by fun_prop)]; simp

theorem fderiv_snd : fderiv 𝕜 (fun xy : X×₂Y => xy.snd) = fun _ => ContinuousLinearMap.WithLp.snd 𝕜 X Y := by
  funext x; ext dx
  simp only [snd_as_clm 𝕜]
  rw[fderiv_clm_apply (by fun_prop) (by fun_prop)]; simp

end WithLp
