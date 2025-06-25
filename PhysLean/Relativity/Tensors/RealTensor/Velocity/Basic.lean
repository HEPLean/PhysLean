/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.Basic
/-!

# Lorentz Velocities

In this module we define Lorentz velocities to be
Lorentz vectors which have norm equal to one and which are future-directed.

-/

open TensorProduct

namespace Lorentz

/-- A Lorentz Velocity is a Lorentz vector which has norm equal to one
  and which is future-directed. -/
def Velocity (d : ℕ := 3) : Set (Vector d) := fun v => ⟪v, v⟫ₘ = (1 : ℝ)
  ∧ 0 < v.timeComponent

namespace Velocity

variable {d : ℕ}

@[ext]
lemma ext {v w : Velocity d} (h : v.1 = w.1) : v = w := by
  exact SetCoe.ext h

lemma mem_iff {v : Vector d} : v ∈ Velocity d ↔ ⟪v, v⟫ₘ = (1 : ℝ) ∧ 0 < v.timeComponent := by
  rfl

@[simp]
lemma contr_self (v : Velocity d) : ⟪v.1, v.1⟫ₘ = (1 : ℝ) := v.2.1

@[simp]
lemma timeComponent_pos (v : Velocity d) : 0 < v.1.timeComponent := v.2.2

end Velocity

end Lorentz
