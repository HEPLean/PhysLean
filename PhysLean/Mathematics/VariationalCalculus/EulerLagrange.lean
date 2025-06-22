/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/

import PhysLean.Mathematics.VariationalCalculus.HasVarGradient

open MeasureTheory ContDiff InnerProductSpace

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

#check HasVarAdjDerivAt.deriv

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
      (F := fun (φ : ℝ → (X×₂X)) t => L t (φ t).fst (φ t).snd)
      (G := fun (φ : ℝ → X) t => (φ t, deriv φ t)₂)

    · apply HasVarAdjDerivAt.fmap (f := fun t (xv : X×₂X) => L t xv.fst xv.snd) _ (fun t => (q t, deriv q t)₂) _
      · simp[Function.HasUncurry.uncurry];
        sorry --fun_prop -- fixed in #26244
      · sorry
    · apply HasVarAdjDerivAt.prod (F:=fun φ => φ) (G:=fun φ => deriv φ)
      · apply HasVarAdjDerivAt.id _ hq
      · apply HasVarAdjDerivAt.deriv
        · apply HasVarAdjDerivAt.id _ hq
  case hgrad =>
    simp
    have h := fun t xy => adjFDeriv_uncurry (𝕜:=ℝ) (f:=fun u v => L t u v) (xy:=xy)
    simp only [WithLp.HasUncurry.uncurry,id] at h
    conv in (adjFDeriv _ (fun _ => L _ _ _) _) =>
      rw[h _ _ (by sorry)]
    conv in (adjFDeriv _ (fun _ => L _ _ _) _) =>
      rw[h _ _ (by sorry)]


    -- simp only
    have h'' := fun t => fderiv_comp' (𝕜:=ℝ) (g:=fun uv : ℝ×ℝ => L t uv.1 uv.2) (f:=fun uv : ℝ×₂ℝ => (uv.fst, uv.snd))
    -- have h := fun t => fderiv_comp' (𝕜:=ℝ) (f:=WithLp.equiv 2 (ℝ × ℝ)) (g:=fun uv : ℝ×ℝ => L t uv.fst uv.snd)
    conv in (fderiv _ _ _) =>
      rw[h'' _ _ sorry sorry]; simp
      rw[h' _ (by sorry)]
      simp
      simp (disch:=sorry) only [fderiv_clm_apply]
    simp



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
