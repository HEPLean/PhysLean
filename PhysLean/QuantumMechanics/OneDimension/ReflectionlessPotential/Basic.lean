/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
import PhysLean.QuantumMechanics.OneDimension.Operators.Parity
import PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
import PhysLean.QuantumMechanics.OneDimension.Operators.Position
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
/-!

# 1d Reflectionless Potential

The quantum reflectionless potential in 1d.
This file contains
- the definition of the reflectionless potential as defined https://arxiv.org/pdf/2411.14941
- properties of reflectionless potentials

## TODO
- Define creation and annihilation operators for reflectionless potentials
- Write the proof of the general solution of the reflectionless potential using the creation and
annihilation operators
- Show reflectionless properties
-/

namespace QuantumMechanics
open Real
open Space
open SchwartzMap
open HilbertSpace
open NNReal
open Field
namespace OneDimension

/-- A reflectionless potential is specified by three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, the
  parameter `κ`, as well as a positive integer family number `N`.
  All of these parameters are assumed to be positive. --/
structure ReflectionlessPotential where
  /-- mass of the particle -/
  m : ℝ
  /-- parameter of the reflectionless potential -/
  κ : ℝ
  /-- Planck's constant -/
  ℏ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- parameter of the reflectionless potential is positive
  N_pos : 0 < N -- family number is positive
  ℏ_pos : 0 < ℏ -- Planck's constant is positive

namespace ReflectionlessPotential

variable (Q : ReflectionlessPotential)

/-!
## Theorems
TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
-/

/-- Define the reflectionless potential as
  V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) --/
noncomputable def reflectionlessPotential (x : ℝ) : ℝ :=
  - (Q.ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / ((2 : ℝ) * Q.m * (Real.cosh (Q.κ * x)) ^ 2)

/-- Define tanh(κ X) operator -/
noncomputable def tanhOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Real.tanh (Q.κ * x) * ψ x

/-- Creation operator: a† as defined in https://arxiv.org/pdf/2411.14941
  a† = 1/√(2m) (P + iℏκ tanh(κX)) -/
noncomputable def creationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x + Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

/-- Annihilation operator: a as defined in https://arxiv.org/pdf/2411.14941
  a = 1/√(2m) (P - iℏκ tanh(κX)) -/
noncomputable def annihilationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x - Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

end ReflectionlessPotential
end OneDimension
end QuantumMechanics
