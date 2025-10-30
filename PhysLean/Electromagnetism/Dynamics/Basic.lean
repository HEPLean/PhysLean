/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
/-!

# Maxwell's equations

Note that currently the equations are defined for isotropic and homogeneous domains.

This module is old, and will soon be replaced.
-/

namespace Electromagnetism

/-- Free space consists of the specification of the
  electric permittivity and the magnetic permeability. -/
structure FreeSpace where
  /-- The permittivity. -/
  ε₀ : ℝ
  /-- The permeability. -/
  μ₀ : ℝ
  ε₀_pos : 0 < ε₀
  μ₀_pos : 0 < μ₀

namespace FreeSpace

variable (𝓕 : FreeSpace)

@[simp]
lemma ε₀_nonneg : 0 ≤ 𝓕.ε₀ := le_of_lt 𝓕.ε₀_pos

@[simp]
lemma μ₀_nonneg : 0 ≤ 𝓕.μ₀ := le_of_lt 𝓕.μ₀_pos

@[simp]
lemma ε₀_ne_zero : 𝓕.ε₀ ≠ 0 := ne_of_gt 𝓕.ε₀_pos

@[simp]
lemma μ₀_ne_zero : 𝓕.μ₀ ≠ 0 := ne_of_gt 𝓕.μ₀_pos

/-- The speed of light in free space. -/
noncomputable def c : SpeedOfLight :=
  ⟨1 / √(𝓕.ε₀ * 𝓕.μ₀), by
    apply div_pos
    · exact zero_lt_one
    · refine Real.sqrt_pos_of_pos ?_
      apply mul_pos 𝓕.ε₀_pos 𝓕.μ₀_pos⟩

lemma c_val : (𝓕.c : ℝ) = 1 / √(𝓕.ε₀ * 𝓕.μ₀) := rfl

lemma c_sq : (𝓕.c : ℝ) ^ 2 = 1 / (𝓕.ε₀ * 𝓕.μ₀) := by
  rw [c_val, sq, div_eq_mul_inv]
  field_simp
  refine (Real.sqrt_eq_iff_eq_sq ?_ ?_).mp rfl
  · apply mul_nonneg 𝓕.ε₀_nonneg 𝓕.μ₀_nonneg
  · positivity

@[simp]
lemma c_abs : abs (𝓕.c : ℝ) = 𝓕.c := by
  rw [abs_of_pos (SpeedOfLight.val_pos 𝓕.c)]

end FreeSpace

end Electromagnetism
