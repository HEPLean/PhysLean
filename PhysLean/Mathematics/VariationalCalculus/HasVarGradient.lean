/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
import Mathlib.Tactic.FunProp.Differentiable
/-!

# Variational gradient

Definition of variational gradient that allows for formal treatement of variational calculus
as used in physics textbooks.
-/

/-! Variational gradient

Definition of variational gradient that allows for formal treatement of variational calculus
as used in physics textbooks.
-/

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {U} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Function `grad` is variational gradient of functional `S` at point `u`.

This formalizes the notion of variational gradient `δS/δu` of a functional `S` at a point `u`.

However, it is not defined for a functional `S : (X → U) → ℝ` but rather for the function
`S' : (X → U) → (X → ℝ)` which is related to the usual functional as `S u = ∫ x, S' (u x) x ∂μ`.
For example for action integral, `S u = ∫ t, L (u t) (deriv u t)` we have
`S' u t = L (u t) (deriv u t)`. Working with `S'` rather than with `S` allows us to ignore certain
technicalities with integrability.

Examples:

Euler-Lagrange equations:
```
δ/δx ∫ L(x,ẋ) dt = ∂L/∂ x - d/dt (∂L/∂ẋ)
```
can be expressed as
```
HasVarGradientAt
  (fun u t => L (u t) (deriv u t))
  (fun t =>
    deriv (L · (deriv u t)) ((u t))
    -
    deriv (fun t' => deriv (L (u t') ·) (deriv u t')) t)
  u
```

Laplace equation is variational gradient of Dirichlet energy:
```
δ/δu ∫ 1/2*‖∇u‖² = - Δu
```
can be expressed as
```
HasVarGradientAt
  (fun u t => 1/2 * deriv u t^2)
  (fun t => - deriv (deriv u) t)
  u
```
-/
inductive HasVarGradientAt (S' : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U)
    (μ : Measure X := by volume_tac) : Prop
  | intro (F')
      (adjoint : HasVarAdjoint (fun δu t => deriv (fun s : ℝ => S' (u + s • δu) t) 0) F' μ)
      (eq : F' (fun _ => 1) = grad)

/-- Variation of `S(x) = ∫ 1/2*m*‖ẋ‖² - V(x)` gives Newton's law of motion `δS(x) = - m*ẍ - V'(x)`-/
example (m : ℝ) (u V : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hV : ContDiff ℝ ∞ V) :
    HasVarGradientAt
      (fun (u : ℝ → ℝ) (t : ℝ) => 1/2 * m * deriv u t ^ 2 - V (u t))
      (fun t => - m * deriv (deriv u) t - deriv V (u t))
      u := by
  apply HasVarGradientAt.intro
  case adjoint =>
    eta_expand
    have := hu.differentiable ENat.LEInfty.out
    have := hV.differentiable ENat.LEInfty.out
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro δu hδu; funext t
      have := hδu.differentiable
      have hd : deriv (fun y => V (u t + y * δu t)) 0
                =
                deriv V (u t) * δu t := by
        have h := deriv_comp (h₂:=V) (h:=fun y => u t + y * δu t) 0 (by fun_prop) (by fun_prop)
        simp +unfoldPartialApp [Function.comp] at h
        exact h
      conv =>
        lhs
        simp (disch:=fun_prop (config:={maxTransitionDepth:=2}) (disch:=simp)) [deriv_add,hd]
        ring_nf
    case h =>
      apply HasVarAdjoint.sub
      · apply HasVarAdjoint.mul_left (ψ := fun x => m * deriv u x) (hψ := by fun_prop)
        apply HasVarAdjoint.deriv
      · apply HasVarAdjoint.mul_left (hψ := by fun_prop)
        apply HasVarAdjoint.id
  case eq =>
    simp only [mul_one, deriv_const_mul_field', Pi.neg_apply, neg_mul]
