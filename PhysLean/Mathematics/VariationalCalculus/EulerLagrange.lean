/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/

import PhysLean.Mathematics.VariationalCalculus.HasVarGradient

open MeasureTheory ContDiff InnerProductSpace

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem hasVarGradient_action_eq_euler_lagrange
    (L : ℝ → X → X → ℝ) (q : ℝ → X)
    (hq : ContDiff ℝ ∞ q) (hL : ContDiff ℝ ∞ ↿L) :
    (δ (q':=q), ∫ t, L t (q' t) (deriv q' t))
    =
    (fun t =>
      gradient (L t · (deriv q t)) (q t)
      -
      deriv (fun t' => gradient (L t' (q t') ·) (deriv q t')) t) := by

  apply HasVarGradientAt.varGradient
  constructor
  case hF' =>
    apply HasVarAdjDerivAt.comp
      (F := fun (φ : ℝ → (X×X)) t => L t (φ t).fst (φ t).snd)
      (G := fun (φ : ℝ → X) t => (φ t, deriv φ t))
    · apply HasVarAdjDerivAt.fmap' (f := fun t => ↿(L t))
      · fun_prop
      · fun_prop
    · apply HasVarAdjDerivAt.prod (F:=fun φ => φ) (G:=fun φ => deriv φ)
      · apply HasVarAdjDerivAt.id _ hq
      · apply HasVarAdjDerivAt.deriv
        · apply HasVarAdjDerivAt.id _ hq
  case hgrad =>
    funext t
    simp (disch:=sorry) only [adjFDeriv_uncurry,gradient_eq_adjFDeriv]
    simp[sub_eq_add_neg]

/-- Euler-Lagrange equations for fields
```
S[u] = ∫ t, ∫ x, L(t, x, u(t,x), ∂ₜu(t,x), ∇ₓu(t,x))
```
-/
theorem hasVarGradient_action_eq_euler_lagrange_field
    (L : (t : ℝ) → (x : Space d) → (u : ℝ) → (dudt : ℝ) → (dudx : Space d) → ℝ)
    (u : ℝ → Space d → ℝ)
    (hu : ContDiff ℝ ∞ ↿u) (hL : ContDiff ℝ ∞ ↿L) :
    HasVarGradientAt
      (fun (u : ℝ×Space d → ℝ) ((t,x) : ℝ×Space d) =>
           L t x (u (t,x)) (deriv (fun t' => u (t',x)) t) (gradient (fun x' => u (t,x')) x))
      (fun (t,x) =>
           -- ∂L/∂u
           gradient (fun u' => L t x u' (deriv (u · x) t) (gradient (u t ·) x)) (u t x)
           -
           -- d/dt ∂L/∂(∂ₜu)
           deriv (fun t' => deriv (fun dudt => L t' x (u t' x) dudt (gradient (u t' ·) x)) (deriv (u · x) t')) t
           -
           -- divₓ ∂L/∂(∂ₓu)
           Space.div (fun x' => gradient (fun dudx => L t x' (u t x') (deriv (u · x') t) dudx) (gradient (u t ·) x')) x)
      (↿u) := sorry
