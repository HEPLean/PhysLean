/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
import Mathlib.Tactic.FunProp.Differentiable
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-!

# Variational adjoint derivative


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

lemma id (u) : HasVarAdjDerivAt (fun φ : X → U => φ) (fun ψ => ψ) u := sorry

lemma const (u : X → U) (v : X → V) : HasVarAdjDerivAt (fun φ : X → U => v) (fun ψ => 0) u := sorry

lemma comp (F : (X → V) → (X → W)) (G : (X → U) → (X → V)) (u : X → U)
    (F' G') (hF : HasVarAdjDerivAt F F' (G u)) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun u => F (G u)) (fun ψ => G' (F' ψ)) u where

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

    constructor
    · sorry
    · intro φ hφ; apply hG.adjoint.test_fun_preserving' _ (hF.adjoint.test_fun_preserving' _ hφ)
    · intro φ ψ hφ hψ
      have := hφ.smooth
      have : ContDiff ℝ ∞ u := sorry
      have hFψ := (hF.adjoint.test_fun_preserving' _ hψ)
      have h := hG.adjoint.adjoint φ (F' ψ) hφ (hF.adjoint.test_fun_preserving' _ hψ)
      rw[←hG.adjoint.adjoint φ (F' ψ) hφ hFψ]
      rw[←hF.adjoint.adjoint _ ψ ?ts1 hψ]
      congr; funext x; congr 1
      rw[hF.linearize _ (by apply hG.diff (fun s x' => u x' + s • φ x'); simp[Function.HasUncurry.uncurry]; fun_prop) x]
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
