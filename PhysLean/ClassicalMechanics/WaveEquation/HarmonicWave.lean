/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.WaveEquation.Basic
/-!

# Harmonic Wave

Time-harmonic waves.

Note TODO `EGU3E` may require considerable effort to be made rigorous and may heavily depend on
the status of Fourier theory in Mathlib.

-/

namespace ClassicalMechanics
open Space

/-- The wavevector which indicates a direction and has magnitude `2π/λ`. -/
abbrev WaveVector (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

/-- Direction of a wavevector. -/
noncomputable def WaveVector.toDirection {d : ℕ} (k : WaveVector d) (h : k ≠ 0) :
    Direction d where
  unit := (‖k‖⁻¹) • (k)
  norm := norm_smul_inv_norm h

/-- General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`. -/
noncomputable def harmonicWave (a g : ℝ → Space d → ℝ) (ω : WaveVector d → ℝ) (k : WaveVector d) :
    Time → Space d → ℝ :=
    fun t r => a (ω k) r * Real.cos (ω k * t - g (ω k) r)

TODO "EGQUA" "Show that the wave equation is invariant under rotations and any direction `s`
    can be rotated to `EuclideanSpace.single 2 1` if only one wave is concerened."

set_option linter.unusedVariables false in
/-- Transverse monochromatic time-harmonic plane wave where the direction of propagation
  is taken to be `EuclideanSpace.single 2 1`. `f₀x` and `f₀y` are the respective amplitudes,
  `ω` is the angular frequency, `δx` and `δy` are the respective phases for `fx` and `fy`. -/
@[nolint unusedArguments]
noncomputable def transverseHarmonicPlaneWave (k : WaveVector) (f₀x f₀y ω δx δy : ℝ)
    (hk : k = EuclideanSpace.single 2 (ω/c)) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
    let fx := harmonicWave (fun _ _ => f₀x) (fun _ r => inner ℝ k r - δx) (fun _ => ω) k
    let fy := harmonicWave (fun _ _ => f₀y) (fun _ r => inner ℝ k r - δy) (fun _ => ω) k
    fun t r => fx t r • EuclideanSpace.single 0 1 + fy t r • EuclideanSpace.single 1 1

/-- Pending #25552. -/

@[simp]
theorem _root_.WithLp.equiv_symm_eq_zero_iff {p V} [AddCommGroup V] {v : V} :
    (WithLp.equiv p V).symm v = 0 ↔ v = 0 := Iff.rfl

@[simp]
theorem _root_.WithLp.equiv_eq_zero_iff {p V} [AddCommGroup V] {v : WithLp p V} :
    WithLp.equiv p V v = 0 ↔ v = 0 := Iff.rfl

@[simp]
theorem _root_.EuclideanSpace.single_eq_zero_iff {ι 𝕜} [RCLike 𝕜] [DecidableEq ι] {i : ι} {x : 𝕜} :
    EuclideanSpace.single i x = 0 ↔ x = 0 := Pi.single_eq_zero_iff

/-- The transverse harmonic planewave representation is equivalent to the general planewave
  expression with `‖k‖ = ω/c`. -/
lemma transverseHarmonicPlaneWave_eq_planeWave {c : ℝ} {k : WaveVector} {f₀x f₀y ω δx δy : ℝ}
    (hc_ge_zero : 0 < c) (hω_ge_zero : 0 < ω) (hk : k = EuclideanSpace.single 2 (ω/c)) :
    (transverseHarmonicPlaneWave k f₀x f₀y ω δx δy hk) = planeWave
    (fun p => (f₀x * Real.cos (-(ω/c)*p + δx)) • (EuclideanSpace.single 0 1) +
    (f₀y * Real.cos (-(ω/c)*p + δy)) • (EuclideanSpace.single 1 1)) c
    (WaveVector.toDirection k (by rw [hk]; simp [ne_of_gt, hc_ge_zero, hω_ge_zero])) := by
  unfold transverseHarmonicPlaneWave planeWave
  ext1 t
  ext1 r
  rw [harmonicWave, harmonicWave, WaveVector.toDirection]
  simp [-PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.isValue, PiLp.smul_apply,
    smul_eq_mul, neg_mul]
  have normk: ‖k‖ = ω/c := by
    rw [hk]
    simp [← abs_div, hc_ge_zero, hω_ge_zero, le_of_lt]
  rw [normk]
  rw [mul_sub, inner_smul_right, real_inner_comm, ← mul_assoc]
  ring_nf
  simp [ne_of_gt, hc_ge_zero, hω_ge_zero, mul_comm ω, mul_assoc]

TODO "EGU3E" "Show that any disturbance (subject to certian conditions) can be expressed
    as a superposition of harmonic plane waves via Fourier integral."

end ClassicalMechanics
