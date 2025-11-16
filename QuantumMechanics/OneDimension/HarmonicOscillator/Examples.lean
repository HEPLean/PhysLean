/-
Copyright (c) 2025 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE

/-!
# Examples: 1d Quantum Harmonic Oscillator

This module gives simple examples of how to use the
`QuantumMechanics.OneDimension.HarmonicOscillator` API.

It is intended for experimentation and pedagogical use, and should
not be imported into other modules.

To run it from the command line:
```
lake env lean PhysLean/QuantumMechanics/OneDimension/HarmonicOscillator/Examples.lean
```
-/

namespace HarmonicOscillatorExamples

open QuantumMechanics OneDimension HarmonicOscillator

/-- A concrete harmonic oscillator with `m = 1`, `ω = 1`. -/
noncomputable def Q : HarmonicOscillator where
  m := 1
  ω := 1
  hω := by norm_num
  hm := by norm_num

-- Ground-state wavefunction and energy
-- Commenting out the checks to reduce noise in the output
-- #check Q.eigenfunction 0
-- #check Q.eigenValue 0

-- Schrödinger operator acting on the ground state
-- Commenting out the checks to reduce noise in the output
-- #check Q.schrodingerOperator (Q.eigenfunction 0)

-- The time-independent Schrödinger equation for n = 0
-- Commenting out the checks to reduce noise in the output
-- #check Q.schrodingerOperator_eigenfunction 0

/-- The explicit pointwise form of the time-independent Schrödinger equation
for the ground state `n = 0`. -/
example :
    ∀ x, Q.schrodingerOperator (Q.eigenfunction 0) x =
      (Q.eigenValue 0) * Q.eigenfunction 0 x :=
  Q.schrodingerOperator_eigenfunction 0

end HarmonicOscillatorExamples
