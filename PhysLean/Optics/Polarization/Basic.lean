/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.WaveEquation.HarmonicWave
import PhysLean.Electromagnetism.Vacuum.Wave
/-!

# Polarization

In this file the real representation is used to develop representations of polarizations
such as the polarization ellipse, Stokes parameters and the Poincaré sphere for monochromatic
time-harmonic electromagnetic plane waves.

More general definitions that can be applied to a wider range of situations will be shown to
be equivalent to the definitions in this file where appropriate.

-/

/-!

## Monochromatic wave

-/

namespace Optics
open ClassicalMechanics
open Electromagnetism
open Real

/-- x-component of monochromatic time-harmonic wave. -/
noncomputable def monochromX (k : WaveVector) (E₀x ω δx : ℝ) :=
    harmonicWave (fun _ _ => E₀x) (fun _ r => inner ℝ k r - δx) (fun _ => ω) k

/-- y-component of monochromatic time-harmonic wave. -/
noncomputable def monochromY (k : WaveVector) (E₀y ω δy : ℝ) :=
    harmonicWave (fun _ _ => E₀y) (fun _ r => inner ℝ k r - δy) (fun _ => ω) k

set_option linter.unusedVariables false in
/-- General form of monochromatic time-harmonic electromagnetic plane wave where
  the direction of propagation is taken to be `EuclideanSpace.single 2 1`.
  `E₀x` and `E₀y` are the respective amplitudes, `ω` is the angular frequency,
  `δx` and `δy` are the respective phases for `Ex` and `Ey`. -/
@[nolint unusedArguments]
noncomputable def harmonicElectromagneticPlaneWave (k : WaveVector) (E₀x E₀y ω δx δy : ℝ)
    (hk : k = EuclideanSpace.single 2 (ω/c)) :
    ElectricField :=
    fun t r => monochromX k E₀x ω δx t r • EuclideanSpace.single 0 1 +
    monochromY k E₀y ω δy t r • EuclideanSpace.single 1 1

/-- The transverse harmonic planewave representation is equivalent to the general electric field
  planewave expression with `‖k‖ = ω/c`. -/
lemma harmonicElectromagneticPlaneWave_eq_electricplaneWave {c : ℝ} {k : WaveVector}
    {E₀x E₀y ω δx δy : ℝ} (hc_ge_zero : 0 < c) (hω_ge_zero : 0 < ω)
    (hk : k = EuclideanSpace.single 2 (ω/c)) :
    (harmonicElectromagneticPlaneWave k E₀x E₀y ω δx δy hk) = electricPlaneWave
    (fun p => (E₀x * cos (-(ω/c)*p + δx)) • (EuclideanSpace.single 0 1) +
    (E₀y * cos (-(ω/c)*p + δy)) • (EuclideanSpace.single 1 1)) c
    (WaveVector.toDirection k (by rw [hk]; simp [ne_of_gt, hc_ge_zero, hω_ge_zero])) := by
  unfold harmonicElectromagneticPlaneWave monochromX monochromY electricPlaneWave
  trans transverseHarmonicPlaneWave k E₀x E₀y ω δx δy hk
  rfl
  rw [transverseHarmonicPlaneWave_eq_planeWave hc_ge_zero hω_ge_zero]

/-!

## Polarization ellipse

-/

variable {k : WaveVector} {E₀x E₀y τ ω δx δy : ℝ} {t : Time} {r : Space}

/-- `monochromX` is equivalent to `E₀x * cos (τ + δx)` with `τ = ω * t - inner ℝ k r`. -/
lemma eq_monochromX (h : τ = ω * t - inner ℝ k r) :
    monochromX k E₀x ω δx t r = E₀x * cos (τ + δx) := by
  rw [h, monochromX, harmonicWave, sub_add]

/-- `monochromY` is equivalent to `E₀y * cos (τ + δy)` with `τ = ω * t - inner ℝ k r`. -/
lemma eq_monochromY (h : τ = ω * t - inner ℝ k r) :
    monochromY k E₀y ω δy t r = E₀y * cos (τ + δy) := by
  rw [h, monochromY, harmonicWave, sub_add]

local notation "Ex" => monochromX k E₀x ω δx t r
local notation "Ey" => monochromY k E₀y ω δy t r

/-- The locus of the electric field vector of an monochromatic time-harmonic
  electromagnetic plane wave is an ellipse. -/
theorem polarizationEllipse (hx : E₀x ≠ 0) (hy : E₀y ≠ 0) (h : τ = ω * t - inner ℝ k r) :
    (Ex / E₀x)^2 + (Ey / E₀y)^2 - 2 * (Ex / E₀x) * (Ey / E₀y) * cos (δy - δx) =
    sin (δy - δx) ^ 2 := by
  rw [eq_monochromX h, eq_monochromY h]
  have h1 : (E₀x * cos (τ + δx)) / E₀x * sin δy - (E₀y * cos (τ + δy)) / E₀y * sin δx =
      cos τ * sin (δy - δx) := by
    field_simp
    rw [cos_add, cos_add, sin_sub]
    ring
  have h2 : (E₀x * cos (τ + δx)) / E₀x * cos δy - (E₀y * cos (τ + δy)) / E₀y * cos δx =
      sin τ * sin (δy - δx) := by
    field_simp
    rw [cos_add, cos_add, sin_sub]
    ring
  trans (E₀x * cos (τ + δx) / E₀x) ^ 2 * (sin δy ^ 2 + cos δy ^ 2) +
      (E₀y * cos (τ + δy) / E₀y) ^ 2 * (sin δx ^ 2 + cos δx ^ 2) -
      2 * (E₀x * cos (τ + δx) / E₀x) * (E₀y * cos (τ + δy) / E₀y) * cos (δy - δx)
  · simp
  trans (cos τ * sin (δy - δx)) ^ 2 + (sin τ * sin (δy - δx)) ^ 2
  · rw [← h1, ← h2]
    rw [cos_sub]
    ring
  trans (cos τ ^ 2 + sin τ ^ 2) * sin (δy - δx) ^ 2
  · ring
  simp

end Optics
