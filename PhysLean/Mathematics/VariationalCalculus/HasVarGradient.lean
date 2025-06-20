/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjDeriv
/-!

# Variational gradient

Definition of variational gradient that allows for formal treatement of variational calculus
as used in physics textbooks.
-/

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
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
inductive HasVarGradientAt (F : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U) : Prop
  | intro (F') (hF' : HasVarAdjDerivAt F F' u) (hgrad : grad = F' (fun _ => 1))

open Classical in
noncomputable def varGradient (F : (X → U) → (X → ℝ)) (u : X → U) : X → U :=
  if h : ∃ grad, HasVarGradientAt F grad u then
    choose h
  else
    0

macro "δ" u:term ", " "∫ " x:term ", " b:term : term =>
  `(varGradient (fun $u $x => $b))
macro "δ" "(" u:term " := " u':term ")" ", " "∫ " x:term ", " b:term : term =>
  `(varGradient (fun $u $x => $b) $u')

namespace HasVarGradientAt

variable
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasureSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]

lemma unique
    {S' : (X → U) → (X → ℝ)} {grad grad' : X → U} {u : X → U}
    (h : HasVarGradientAt S' grad u) (h' : HasVarGradientAt S' grad' u) :
    grad = grad' := by

  obtain ⟨F,hF,eq⟩ := h
  obtain ⟨G,hG,eq'⟩ := h'
  rw[eq,eq',hF.unique hG (fun _ => 1) (by fun_prop)]

open Classical in
protected lemma varGradient
    (F : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U)
    (hF : HasVarGradientAt F grad u) :
    varGradient F u = grad := by

  have h := Exists.intro grad hF (p:= fun grad' => HasVarGradientAt F grad' u)
  unfold varGradient;
  simp[h, hF.unique h.choose_spec]
