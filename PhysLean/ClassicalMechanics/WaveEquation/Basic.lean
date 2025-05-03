/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import PhysLean.ClassicalMechanics.Time.Basic
/-!
# Wave equation

The general wave equation.

-/

namespace ClassicalMechanics

open Space
open Time

/-- The general form of the wave equation where c is the propagation speed. -/
def WaveEquation (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) (c : ℝ) : Prop :=
    c^2 • Δ (f t) x -  ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t  = 0
