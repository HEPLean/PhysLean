/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint

import PhysLean.Mathematics.FDerivCurry
import PhysLean.Mathematics.Calculus.AdjFDeriv
import PhysLean.SpaceAndTime.Space.Basic

noncomputable section

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
noncomputable
def divergence (f : E → E) (x : E) : 𝕜 := (fderiv 𝕜 f x).toLinearMap.trace _ _

@[simp]
lemma divergence_zero : divergence 𝕜 (fun _ : E => 0) = fun _ => 0 := by
  unfold divergence
  simp

lemma divergence_eq_sum_fderiv {s : Finset E} (b : Basis s 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i : s, b.repr (fderiv 𝕜 f x (b i)) i := by
  funext x
  unfold divergence
  rw[LinearMap.trace_eq_matrix_trace_of_finset (s:=s) _ b]
  simp[Matrix.trace,Matrix.diag,LinearMap.toMatrix]

lemma divergence_eq_sum_fderiv' {ι} [Fintype ι] (b : Basis ι 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i, b.repr (fderiv 𝕜 f x (b i)) i := by
  sorry

lemma divergence_eq_space_div {d} (f : Space d → Space d) : divergence ℝ f = Space.div f := by
  let b := (Space.basis (d:=d)).toBasis
  rw[divergence_eq_sum_fderiv' b]
  funext x
  simp +zetaDelta [Space.div,Space.deriv,Space.coord,Space.basis]
  -- ugh again can't use `fderiv_apply` because of `EuclideanSpace`
  sorry

lemma divergence_prodMk {f : E×F → E} {g : E×F → F} {xy : E×F}
    (hf : DifferentiableAt 𝕜 f xy) (hg : DifferentiableAt 𝕜 g xy) :
    divergence 𝕜 (fun xy : E×F => (f xy, g xy)) xy
    =
    divergence 𝕜 (fun x' => f (x',xy.2)) xy.1
    +
    divergence 𝕜 (fun y' => g (xy.1,y')) xy.2 := by
  have bX : Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := sorry
  have bY : Basis (Fin (Module.finrank 𝕜 E)) 𝕜 F := sorry
  let bXY := bX.prod bY
  rw[divergence_eq_sum_fderiv' bX]
  rw[divergence_eq_sum_fderiv' bY]
  rw[divergence_eq_sum_fderiv' bXY]
  simp[hf.fderiv_prodMk hg,bXY,fderiv_wrt_prod hf,fderiv_wrt_prod hg]

lemma divergence_add {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x + g x) x
    =
    divergence 𝕜 f x + divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_add hf hg]

lemma divergence_neg {f : E → E} {x : E} :
    divergence 𝕜 (fun x => -f x) x
    =
    -divergence 𝕜 f x := by
  unfold divergence
  simp [fderiv_neg]

lemma divergence_sub {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x - g x) x
    =
    divergence 𝕜 f x - divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_sub hf hg]

lemma divergence_const_smul {f : E → E} {x : E} {c : 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (fun x => c • f x) x
    =
    c * divergence 𝕜 f x := by
  unfold divergence
  simp [fderiv_const_smul hf]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

lemma divergence_smul [InnerProductSpace' 𝕜 E] {f : E → 𝕜} {g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x • g x) x
    =
    f x * divergence 𝕜 g x + ⟪adjFDeriv 𝕜 f x 1, g x⟫  := by
  unfold divergence
  simp [fderiv_smul hf hg]
  sorry
