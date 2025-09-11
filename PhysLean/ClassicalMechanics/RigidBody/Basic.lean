/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Distributions
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
/-!

# Rigid bodies

A rigid body is one where the distance and relative orientation between particles does not change.
In otherwords, the body remains undeformed.

In this module we will define the basic properties of a rigid body, including
- mass
- center of mass
- inertia tensor


## References
- Landau and Lifshitz, Mechanics, page 100, Section 32
-/

open Manifold

TODO "MEX5S" "The definition of a rigid body is currently defined via linear maps
  from the space of smooth functions to ℝ. When possible, it should be change
  to *continuous* linear maps. "

/-- A Rigid body defined by its mass distribution. -/
structure RigidBody (d : ℕ) where
  /-- The mass distribution of the rigid body. -/
  ρ : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯ →ₗ[ℝ] ℝ

namespace RigidBody

/-- The total mass of the rigid body. -/
def mass {d : ℕ} (R : RigidBody d) : ℝ := R.ρ ⟨fun _ => 1, contMDiff_const⟩

/-- The center of mass of the rigid body. -/
noncomputable def centerOfMass {d : ℕ} (R : RigidBody d) : Space d := fun i =>
  (1 / R.mass) • R.ρ ⟨fun x => x i, ContDiff.contMDiff <| by fun_prop⟩

/-- The inertia tensor of the rigid body. -/
noncomputable def inertiaTensor {d : ℕ} (R : RigidBody d) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  R.ρ ⟨fun x => (if i = j then 1 else 0) * ∑ k : Fin d, (x k)^2 - x i * x j,
    ContDiff.contMDiff <| by fun_prop⟩

lemma inertiaTensor_symmetric {d : ℕ} (R : RigidBody d) (i j : Fin d) :
    R.inertiaTensor i j = R.inertiaTensor j i := by
  simp only [inertiaTensor]
  congr
  funext x
  congr 1
  · congr 2
    exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)
  · ring

/-- The kinetic energy of a rigid body. -/
informal_definition kineticEnergy where
  tag := "MEYBM"
  deps := [``RigidBody]

end RigidBody
