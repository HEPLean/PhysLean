/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import PhysLean.Mathematics.FDerivCurry
/-!
# Variational adjoint derivative

Variational adjoint derivative of `F` at `u` is a generalization of `(fderiv ℝ F u).adjoint`
to function spaces. In particular, variational gradient is an analog of
`gradient F u := (fderiv ℝ F u).adjoint 1`.

The definition of `HasVarAdjDerivAt` is constructed exactly such that we can prove composition
theorem saying
```
  HasVarAdjDerivAt F F' (G u)) → HasVarAdjDerivAt G G' u →
    HasVarAdjDerivAt (F ∘ G) (G' ∘ F') u
```
This theorem is the main tool to mechanistically compute variational gradient.
-/

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasureSpace Z]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [InnerProductSpace' ℝ W]

/-- This is analogue of saying `F' = (fderiv ℝ F u).adjoint`.

This definition is useful as we can prove composition theorem for it and `HasVarGradient F grad u`
can be computed by `grad := F' (fun _ => 1)`. -/
structure HasVarAdjDerivAt (F : (X → U) → (Y → V)) (F' : (Y → V) → (X → U)) (u : X → U) : Prop
    where
  smooth_at : ContDiff ℝ ∞ u
  diff : ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
    ContDiff ℝ ∞ (fun sx : ℝ×Y => F (φ sx.1) sx.2)
  linearize :
    ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
      ∀ x,
        deriv (fun s' : ℝ => F (φ s') x) 0
        =
        deriv (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) 0
  adjoint : HasVarAdjoint (fun δu x => deriv (fun s : ℝ => F (fun x' => u x' + s • δu x') x) 0) F'

namespace HasVarAdjDerivAt

variable {μ : Measure X}

lemma apply_smooth_of_smooth {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u v : X → U}
    (h : HasVarAdjDerivAt F F' u) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (F v) := by
  have h1 := h.diff (fun _ => v) (by fun_prop)
  simp at h1
  have hf : F v = (fun (sx : ℝ × X) => F v sx.2) ∘ fun x => (0, x) := by
    funext x
    simp
  rw [hf]
  apply ContDiff.comp h1
  fun_prop

lemma apply_smooth_self {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) : ContDiff ℝ ∞ (F u) := by
  exact h.apply_smooth_of_smooth (h.smooth_at)

lemma smooth_R {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) (x : X) :
    ContDiff ℝ ∞ (fun s : ℝ => F (fun x' => φ s x') x) :=
  (h.diff (fun s x => φ s x) hφ).comp (by fun_prop : ContDiff ℝ ∞ fun s => (s,x))

lemma smooth_linear {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) :
    ContDiff ℝ ∞ (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) := by
  apply h.smooth_R (φ := (fun s' x => φ 0 x + s' • deriv (φ · x) 0))
  fun_prop [deriv]

lemma differentiable_linear {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) (x : X) :
    Differentiable ℝ (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) := by
  exact fun x => (h.smooth_linear hφ).differentiable (ENat.LEInfty.out) x

lemma id (u) (hu : ContDiff ℝ ∞ u) : HasVarAdjDerivAt (fun φ : X → U => φ) (fun ψ => ψ) u where
  smooth_at := hu
  diff := by intros; fun_prop
  linearize := by intro φ hφ x; simp [deriv_smul_const]
  adjoint := by simp [deriv_smul_const]; apply HasVarAdjoint.id

lemma const (u : X → U) (v : X → V) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    HasVarAdjDerivAt (fun _ : X → U => v) (fun _ => 0) u where

  smooth_at := hu
  diff := by intros; fun_prop
  linearize := by simp
  adjoint := by simp; exact HasVarAdjoint.zero

lemma comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)} {u : X → U}
    {F' G'} (hF : HasVarAdjDerivAt F F' (G u)) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun u => F (G u)) (fun ψ => G' (F' ψ)) u where
  smooth_at := hG.smooth_at
  diff := by
    intro φ hφ
    apply hF.diff (φ := fun t x => G (φ t) x)
    exact hG.diff φ hφ
  linearize := by
    intro φ hφ x
    rw[hF.linearize (fun t x => G (φ t) x) (hG.diff φ hφ)]
    rw[hF.linearize (fun s' => G fun x => φ 0 x + s' • deriv (fun x_1 => φ x_1 x) 0)]
    simp[hG.linearize φ hφ]
    eta_expand; simp[Function.HasUncurry.uncurry]
    apply hG.diff (φ := fun a x => φ 0 x + a • deriv (fun x_1 => φ x_1 x) 0)
    fun_prop [deriv]
  adjoint := by
    have : ContDiff ℝ ∞ u := hG.smooth_at
    have h := hF.adjoint.comp hG.adjoint
    apply h.congr_fun
    intro φ hφ; funext x
    rw[hF.linearize]
    · simp
    · simp [Function.HasUncurry.uncurry];
      apply hG.diff (φ := (fun s x => u x + s • φ x))
      fun_prop

lemma unique_on_test_functions
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (F : (X → U) → (Y → V)) (u : X → U)
    (F' G') (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt F G' u)
    (φ : Y → V) (hφ : IsTestFunction φ) :
    F' φ = G' φ := HasVarAdjoint.unique_on_test_functions hF.adjoint hG.adjoint φ hφ

lemma unique {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasureSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] [MeasureSpace Y]
    {F : (X → U) → (Y → V)} {u : X → U}
    {F' G'} (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt F G' u)
    (φ : Y → V) (hφ : ContDiff ℝ ∞ φ) :
    F' φ = G' φ :=
  HasVarAdjoint.unique hF.adjoint hG.adjoint φ hφ

attribute [fun_prop] differentiableAt_id'

lemma deriv' (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt (fun φ : ℝ → ℝ => deriv φ) (fun φ x => - deriv φ x) u where
  smooth_at := hu
  diff := by intros; fun_prop [deriv]
  linearize := by
    intro φ hφ x
    have hd : DifferentiableAt ℝ (fun x => deriv (fun x_1 => φ x_1 x) 0) x :=
      fderiv_curry_differentiableAt_fst_comp_snd _ _ _ _ (ContDiff.of_le hφ (ENat.LEInfty.out))
    conv_rhs =>
      enter [1, s']
      rw [deriv_add (function_differentiableAt_snd _ _ _ (hφ.differentiable ENat.LEInfty.out))
        (by fun_prop)]
    have hd2 : DifferentiableAt ℝ (fun s' =>
        deriv (fun x => s' • deriv (fun x_1 => φ x_1 x) (0 : ℝ)) x) (0 : ℝ) := by
      conv_lhs =>
        enter [s']
        simp
      fun_prop
    rw [deriv_add (by fun_prop) (hd2)]
    simp only [deriv_const', smul_eq_mul, differentiableAt_const, deriv_const_mul_field',
      differentiableAt_id', deriv_mul, deriv_id'', one_mul, mul_zero, add_zero, zero_add]
    dsimp [deriv]
    exact fderiv_swap (𝕜 := ℝ) φ 0 1 x 1 (ContDiff.of_le hφ (ENat.LEInfty.out))
  adjoint := by
    simp (disch:=fun_prop) [deriv_add]
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ
      have := hφ.smooth.differentiable (ENat.LEInfty.out)
      have := hu.differentiable (ENat.LEInfty.out)
      simp (disch:=fun_prop) [deriv_add]
      rfl
    case h =>
      apply HasVarAdjoint.deriv

protected lemma deriv (F : (ℝ → U) → (ℝ → ℝ)) (F') (u) (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt (fun φ : ℝ → U => deriv (F φ))
    (fun ψ x => F' (fun x' => - deriv ψ x') x) u :=
  comp (F:=deriv) (G:=F) (hF := deriv' (F u) hF.apply_smooth_self) (hG := hF)

lemma neg (F : (X → U) → (X → V)) (F') (u) (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt (fun φ x => -F φ x) (fun ψ x => - F' ψ x) u where

  smooth_at := hF.smooth_at
  diff := by intro φ hφ; apply ContDiff.neg; apply hF.diff; assumption
  linearize := by intros; rw[deriv.neg']; simp; rw[hF.linearize]; assumption
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      conv =>
        lhs
        rw[deriv.neg']
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp[deriv_smul_const]
    case h =>
      apply HasVarAdjoint.neg
      apply hF.adjoint

section OnFiniteMeasures

variable [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (@volume X _)]

lemma add
    (F G : (X → U) → (X → V)) (F' G') (u)
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun φ x => F φ x + G φ x) (fun ψ x => F' ψ x + G' ψ x) u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    apply ContDiff.add
    · apply hF.diff; assumption
    · apply hG.diff; assumption
  linearize := by
    intro φ hφ x; rw[deriv_add]; rw[deriv_add]; rw[hF.linearize _ hφ, hG.linearize _ hφ]
    · exact hF.differentiable_linear hφ x 0
    · exact hG.differentiable_linear hφ x 0
    · apply ContDiff.differentiable _ ENat.LEInfty.out
      have hf := hF.diff φ hφ
      change ContDiff ℝ ∞ ((fun sx : ℝ × X => F (φ sx.1) sx.2) ∘ fun s' => (s', x))
      apply ContDiff.comp hf
      fun_prop
    · apply ContDiff.differentiable _ ENat.LEInfty.out
      have hf := hG.diff φ hφ
      change ContDiff ℝ ∞ ((fun sx : ℝ × X => G (φ sx.1) sx.2) ∘ fun s' => (s', x))
      apply ContDiff.comp hf
      fun_prop
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      have h1 : DifferentiableAt ℝ (fun s => F (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hF.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable ENat.LEInfty.out 0
      have h2 : DifferentiableAt ℝ (fun s => G (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hG.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable ENat.LEInfty.out 0
      conv =>
        lhs
        rw[deriv_add h1 h2]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp[deriv_smul_const]
    case h =>
      apply HasVarAdjoint.add
      apply hF.adjoint
      apply hG.adjoint

lemma mul
    (F G : (X → ℝ) → (X → ℝ)) (F' G') (u)
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun φ x => F φ x * G φ x)
      (fun ψ x => F' (fun x' => ψ x' * G u x') x + G' (fun x' => F u x' * ψ x') x) u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    apply ContDiff.mul
    · apply hF.diff; assumption
    · apply hG.diff; assumption
  linearize := by
    intro φ hφ x; rw[deriv_mul]; rw[deriv_mul]; rw[hF.linearize _ hφ, hG.linearize _ hφ]; simp
    · exact hF.differentiable_linear hφ x 0
    · exact hG.differentiable_linear hφ x 0
    · apply ContDiff.differentiable _ ENat.LEInfty.out
      have hf := hF.diff φ hφ
      change ContDiff ℝ ∞ ((fun sx : ℝ × X => F (φ sx.1) sx.2) ∘ fun s' => (s', x))
      apply ContDiff.comp hf
      fun_prop
    · apply ContDiff.differentiable _ ENat.LEInfty.out
      have hf := hG.diff φ hφ
      change ContDiff ℝ ∞ ((fun sx : ℝ × X => G (φ sx.1) sx.2) ∘ fun s' => (s', x))
      apply ContDiff.comp hf
      fun_prop
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      -- Same two results as the `add` case
      have h1 : DifferentiableAt ℝ (fun s => F (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hF.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable ENat.LEInfty.out 0
      have h2 : DifferentiableAt ℝ (fun s => G (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hG.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable ENat.LEInfty.out 0
      conv =>
        lhs
        rw[deriv_mul h1 h2]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
    case h =>
      apply HasVarAdjoint.add
      · apply HasVarAdjoint.mul_right
        apply hF.adjoint
        exact apply_smooth_self hG
      · apply HasVarAdjoint.mul_left
        apply hG.adjoint
        exact apply_smooth_self hF

end OnFiniteMeasures
