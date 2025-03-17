/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import PhysLean.Meta.TODO.Basic
/-!

# The Classical Harmonic Oscillator

-/

namespace ClassicalMechanics
open Real

/-- The classical harmonic oscillator is specified by a mass `m`, and a spring constant `k`.
  Both the mass and the string constant are assumed to be positive. -/
structure HarmonicOscillator where
  /-- The mass of the harmonic Oscillator. -/
  m : ℝ
  /-- The spring constant of the harmonic oscillator. -/
  k : ℝ
  m_pos : 0 < m
  k_pos : 0 < k

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

@[simp]
lemma k_neq_zero : S.k ≠ 0 := Ne.symm (ne_of_lt S.k_pos)

@[simp]
lemma m_neq_zero : S.m ≠ 0 := Ne.symm (ne_of_lt S.m_pos)

/-- The angular frequence of the classical harmonic osscilator, `ω`, is defined
  as `√(k/m)`. -/
noncomputable def ω : ℝ := √(S.k / S.m)

/-- The angular frequence of the classical harmonic osscilator is positive. -/
@[simp]
lemma ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

/-- The square of the angular frequence of the classical harmonic osscilator is equal to `k/m`. -/
lemma ω_sq : S.ω^2 = S.k / S.m := by
  rw [ω, sq_sqrt]
  exact div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)

/-- The angular frequence of the classical harmonic osscilator is not equal to zero. -/
@[simp]
lemma ω_neq_zero : S.ω ≠ 0 := Ne.symm (ne_of_lt S.ω_pos)

/-- The inverse of the square of the angular frequence of the classical harmonic osscilator
  is `m/k`. -/
lemma inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.m/S.k := by
  rw [ω_sq]
  field_simp

/-- The kinetic energy of the harmonic oscillator is `1/2 m (dx/dt) ^ 2`. -/
noncomputable def kineticEnergy (x : ℝ → ℝ) : ℝ → ℝ := fun t =>
  1/2 * S.m * (deriv x t)^2

/-- The potential energy of the harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : ℝ → ℝ) : ℝ → ℝ := fun t =>
  1/2 * S.k * (x t)^2

/-- The energy of the harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (x : ℝ → ℝ) : ℝ → ℝ := fun t =>
  kineticEnergy S x t + potentialEnergy S x t

/-- The lagrangian of the harmonic oscillator is the kinetic energy minus the potential energy. -/
noncomputable def lagrangian (x : ℝ → ℝ) : ℝ → ℝ := fun t =>
  kineticEnergy S x t - potentialEnergy S x t

/-- The lagrangian of the classical harmonic oscillator obeys the condition

  `lagrangian S (- x) = lagrangian S x`.
-/
lemma lagrangian_parity (x : ℝ → ℝ) (hx : Differentiable ℝ x) :
    lagrangian S (- x) = lagrangian S x := by
  funext t
  simp only [lagrangian, kineticEnergy, one_div, potentialEnergy, Pi.neg_apply, even_two,
    Even.neg_pow, sub_left_inj, mul_eq_mul_left_iff, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
    false_or]
  left
  trans (deriv (Neg.neg ∘ x) t)^2
  · rfl
  rw [deriv_comp]
  · simp
  · fun_prop
  · exact hx t

TODO "Derive the force from the lagrangian of the classical harmonic oscillator"

TODO "Derive the Euler-Lagraange equation for the classical harmonic oscillator
  from the lagrangian."

TODO "Include damping into the classical harmonic oscillator."

end HarmonicOscillator

end ClassicalMechanics
