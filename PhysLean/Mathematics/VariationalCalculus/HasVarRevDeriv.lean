/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
  {U} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {W} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


/-- This is analogue of saying `F' = (fderiv ℝ F u).adjoint`.

This definition is useful as we can prove composition theorem for it and `HasVarGradient F grad u`
can be computed by `grad := F' (fun _ => 1)`. -/
structure HasVarAdjDerivAt (F : (X → U) → (X → V)) (F' : (X → V) → (X → U)) (u : X → U) : Prop where
  smooth_at : ContDiff ℝ ∞ u
  diff : ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
    ContDiff ℝ ∞ (fun sx : ℝ×X => F (φ sx.1) sx.2)
  linearize :
    ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
      ∀ x,
        deriv (fun s' : ℝ => F (φ s') x) 0
        =
        deriv (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) 0
  adjoint : HasVarAdjoint (fun δu x => deriv (fun s : ℝ => F (fun x' => u x' + s • δu x') x) 0) F'


namespace HasVarAdjDerivAt

variable {μ : Measure X}

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

lemma comp {F : (X → V) → (X → W)} {G : (X → U) → (X → V)} {u : X → U}
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

    constructor
    · intro φ hφ
      conv =>
        enter [1,x]
        rw[hF.linearize _ (by apply hG.diff (fun s x' => u x' + s • φ x');
                              simp[Function.HasUncurry.uncurry]; fun_prop)]
      simp
      apply hF.adjoint.test_fun_preserving
      apply hG.adjoint.test_fun_preserving
      apply hφ
    · intro φ hφ; apply hG.adjoint.test_fun_preserving' _ (hF.adjoint.test_fun_preserving' _ hφ)
    · intro φ ψ hφ hψ
      have hFψ := (hF.adjoint.test_fun_preserving' _ hψ)
      have h := hG.adjoint.adjoint φ (F' ψ) hφ (hF.adjoint.test_fun_preserving' _ hψ)
      rw[←hG.adjoint.adjoint φ (F' ψ) hφ hFψ]
      rw[←hF.adjoint.adjoint _ ψ ?ts1 hψ]
      congr; funext x; congr 1
      rw[hF.linearize _ (by apply hG.diff (fun s x' => u x' + s • φ x');
                            simp[Function.HasUncurry.uncurry]; fun_prop) x]
      simp
      case ts1 =>
        conv =>
          enter [1,x]
          rw[hG.linearize _ (by fun_prop)]
          simp
        apply hG.adjoint.test_fun_preserving
        conv =>
          enter [1,x]
          rw[deriv_smul_const (by fun_prop)]
          simp
        apply hφ

lemma unique
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (F : (X → U) → (X → V)) (u : X → U)
    (F' G') (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt F G' u)
    (φ : X → V) (hφ : IsTestFunction φ) :
    F' φ = G' φ := HasVarAdjoint.unique (μ:=volume) hF.adjoint hG.adjoint φ hφ


attribute [fun_prop] differentiableAt_id'

lemma deriv' (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt (fun φ : ℝ → ℝ => deriv φ) (fun φ x => - deriv φ x) u where

  smooth_at := hu
  diff := by intros; fun_prop [deriv]
  linearize := by
    intros
    sorry
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
    HasVarAdjDerivAt (fun φ : ℝ → U => deriv (F φ)) (fun ψ x => F' (fun x' => - deriv ψ x') x) u :=
  comp (F:=deriv) (G:=F) (hF := deriv' (F u) sorry) (hG := hF)

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


lemma add
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure] [OpensMeasurableSpace X]
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
    sorry
    sorry
    sorry
    sorry
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      conv =>
        lhs
        rw[deriv_add sorry sorry]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp[deriv_smul_const]
    case h =>
      apply HasVarAdjoint.add
      apply hF.adjoint
      apply hG.adjoint


lemma mul
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure] [OpensMeasurableSpace X]
    (F G : (X → ℝ) → (X → ℝ)) (F' G') (u)
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun φ x => F φ x * G φ x) (fun ψ x => F' (fun x' => ψ x' * G u x') x + G' (fun x' => F u x' * ψ x') x) u where

  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    apply ContDiff.mul
    · apply hF.diff; assumption
    · apply hG.diff; assumption
  linearize := by
    intro φ hφ x; rw[deriv_mul]; rw[deriv_mul]; rw[hF.linearize _ hφ, hG.linearize _ hφ]; simp
    sorry
    sorry
    sorry
    sorry
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      conv =>
        lhs
        rw[deriv_mul sorry sorry]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
    case h =>
      apply HasVarAdjoint.add
      · apply HasVarAdjoint.mul_right
        apply hF.adjoint
        sorry
      · apply HasVarAdjoint.mul_left
        apply hG.adjoint
        sorry
