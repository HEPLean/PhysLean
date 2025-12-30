/-
Copyright (c) 2025 Rein Zustand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rein Zustand, Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient

/-!

# Gauge Equivalence of Lagrangians

## i. Overview

Two Lagrangians are physically equivalent if they differ by a total time derivative
d/dt F(q, t). This is because the Euler-Lagrange equations depend only on extremizing
the action integral, and total derivatives don't affect which paths are extremal.

This module defines the key concept of a function being a total time derivative,
which is essential for analyzing symmetries like Galilean invariance.

## ii. Key insight

A general function δL(r, v, t) is a total time derivative if there exists a function
F(r, t) (independent of velocity) such that:
  δL(r, v, t) = d/dt F(r, t) = fderiv ℝ F (r, t) (v, 1)

By the chain rule, this expands to:
  δL(r, v, t) = ∂F/∂t + ⟨∇ᵣF, v⟩

For the special case where δL depends only on velocity v (not position or time),
this implies a strong constraint:
  δL(v) = ⟨g, v⟩ for some constant vector g

This is because:
1. d/dt F(r, t) = ∂F/∂t + ⟨∇F, v⟩
2. For δL to be r-independent, ∇F must be r-independent
3. For δL to be t-independent, the time-dependent part must vanish
4. The result is δL = ⟨g, v⟩ for constant g

## iii. Key definitions

- `IsTotalTimeDerivative`: General case for δL(r, v, t)
- `IsTotalTimeDerivativeVelocity`: Velocity-only case, equivalent to δL(v) = ⟨g, v⟩

## iv. References

- Landau & Lifshitz, "Mechanics", §2 (The principle of least action)
- Landau & Lifshitz, "Mechanics", §4 (The Lagrangian for a free particle)

-/

namespace ClassicalMechanics

open InnerProductSpace

namespace Lagrangian

/-!

## A. General Total Time Derivative

A function δL(r, v, t) is a total time derivative if there exists F(r, t) such that
δL(r, v, t) = fderiv ℝ F (r, t) (v, 1).

By the chain rule, this equals ∂F/∂t(r, t) + ⟨∇ᵣF(r, t), v⟩.

-/

/-- A function δL(r, v, t) is a total time derivative if it can be written as d/dt F(r, t)
    for some function F that depends on position and time but not velocity.

    Mathematically: δL(r, v, t) = fderiv ℝ F (r, t) (v, 1)

    By the chain rule, this equals ∂F/∂t(r, t) + ⟨∇ᵣF(r, t), v⟩.

    This is the most general form of gauge equivalence for Lagrangian perturbations.
    The key point is that F must be independent of velocity. -/
def IsTotalTimeDerivative {n : ℕ}
    (δL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop :=
  ∃ (F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) (_ : Differentiable ℝ F),
    ∀ r v t, δL r v t = fderiv ℝ F (r, t) (v, 1)

/-!

## B. Velocity-Only Total Time Derivative

When δL depends only on velocity (the free particle case), the condition simplifies.

-/

/-- A velocity-dependent function δL is a total time derivative (of a position-time function)
    iff it has the form δL(v) = ⟨g, v⟩ for some constant vector g.

    This characterization comes from the requirement that:
    - d/dt F(r, t) = ∂F/∂t + ⟨∇F, ṙ⟩ = ∂F/∂t + ⟨∇F, v⟩
    - For the result to be independent of r and t, we need ∇F = g (constant) and ∂F/∂t = 0
    - Thus δL(v) = ⟨g, v⟩ -/
def IsTotalTimeDerivativeVelocity {n : ℕ} (δL : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n), ∀ v, δL v = ⟪g, v⟫_ℝ

end Lagrangian

end ClassicalMechanics
