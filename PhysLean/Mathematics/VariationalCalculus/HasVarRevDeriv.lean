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
  diff : ∀ (φ : ℝ → X → U), IsTestFunction ↿φ →
    IsTestFunction (fun (s,x) => F (φ s) x)
  linearize :
    ∀ (φ : ℝ → X → U), IsTestFunction ↿φ →
      ∀ s x,
        deriv (fun s' => F (φ s') x) s
        =
        deriv (fun s' => F (fun x => φ s x + (s' - s) • deriv (φ · x) s) x) s
  adjoint : HasVarAdjoint (fun δu x => deriv (fun s : ℝ => F (fun x' => u x' + s • δu x') x) 0) F'


namespace HasVarAdjDerivAt

variable {μ : Measure X}

lemma id (u) : HasVarAdjDerivAt (fun φ : X → U => φ) (fun ψ => ψ) u := sorry

lemma const (u : X → U) (v : X → V) : HasVarAdjDerivAt (fun φ : X → U => v) (fun ψ => 0) u := sorry

lemma comp (F : (X → V) → (X → W)) (G : (X → U) → (X → V)) (u : X → U)
    (F' G') (hF : HasVarAdjDerivAt F F' (G u)) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun u => F (G u)) (fun ψ => G' (F' ψ)) u where

  diff := by
    intro φ hφ; dsimp
    apply hF.diff (φ := fun t x => G (φ t) x)
    exact hG.diff φ hφ

  linearize := by
    intro φ hφ s x
    rw[hF.linearize (fun t x => G (φ t) x) (hG.diff φ hφ)]
    rw[hF.linearize (fun s' => G fun x => φ s x + (s' - s) • deriv (fun x_1 => φ x_1 x) s)]
    simp[hG.linearize φ hφ]
    sorry

  adjoint := by

    constructor
    · sorry
    · intro φ hφ; apply hG.adjoint.test_fun_preserving' _ (hF.adjoint.test_fun_preserving' _ hφ)
    · intro φ ψ hφ hψ
      have h := hG.adjoint.adjoint φ (F' ψ) hφ sorry
      rw[←hG.adjoint.adjoint φ (F' ψ) hφ sorry]
      rw[←hF.adjoint.adjoint _ ψ sorry hψ]
      congr; funext x; congr 1
      rw[hF.linearize _ sorry 0 x]
      simp
