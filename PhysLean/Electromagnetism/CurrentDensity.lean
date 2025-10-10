/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.KineticTerm
import PhysLean.ClassicalMechanics.VectorFields
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

## ii. Key results

- `LorentzCurrentDensity` : The type of Lorentz current densities.
- `LorentzCurrentDensity.chargeDensity` : The charge density associated with a
  Lorentz current density.
- `LorentzCurrentDensity.currentDensity` : The current density associated with a
  Lorentz current density.

## iii. Table of contents

## iv. References

-/

namespace Electromagnetism
open TensorSpecies
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The Lorentz Current Density

The Lorentz current density is a Lorentz Vector field on spacetime.

-/

/-- The Lorentz current density, also called four-current. -/
abbrev LorentzCurrentDensity (d : ℕ := 3) := SpaceTime d → Lorentz.Vector d

namespace LorentzCurrentDensity

/-!

## B. The underlying charge desnity

-/

/-- The underlying charge density associated with a Lorentz current density. -/
noncomputable def chargeDensity (J : LorentzCurrentDensity d) : Time → Space d → ℝ :=
  fun t x => J (toTimeAndSpace.symm (t, x)) (Sum.inl 0)

/-!

## C. The underlying current desnity

-/

/-- The underlying (non-Lorentz) current density associated with a Lorentz current density. -/
noncomputable def currentDensity (J : LorentzCurrentDensity d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x i => J (toTimeAndSpace.symm (t, x)) (Sum.inr i)

end LorentzCurrentDensity

end Electromagnetism
