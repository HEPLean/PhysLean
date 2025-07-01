/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.Space.Basic
/-!

# The Friedmann-Lemaître-Robertson-Walker metric

Everything in this file is currently informal or semiformal.

-/

namespace Cosmology

/-- The inductive type with three constructors:
- `Spherical (k : ℝ)`
- `Flat`
- `Saddle (k : ℝ)` -/
@[sorryful]
def SpatialGeometry : Type := sorry

namespace SpatialGeometry

/-- For `s` corresponding to
- `Spherical k`, `S s r = k * sin (r / k)`
- `Flat`, `S s r = r`,
- `Saddle k`, `S s r = k * sin (r / k)`.

Semiformal implementation note: There is likely a better name for this function. -/
@[sorryful]
def S (s : SpatialGeometry) : ℝ → ℝ := sorry

/-- The limit of `S (Saddle k) r` as `k → ∞` is equal to `S (Flat) r`. -/
informal_lemma limit_S_saddle where
  deps := []
  tag := "6ZZ3D"

/-- The limit of `S (Sphere k) r` as `k → ∞` is equal to `S (Flat) r`. -/
informal_lemma limit_S_sphere where
  deps := []
  tag := "62A4R"

end SpatialGeometry

/-- The structure FLRW is defined to contain the physical parameters of the
  Friedmann-Lemaître-Robertson-Walker metric. That is, it contains
- The scale factor `a(t)`
- An element of `SpatialGeometry`.

Semiformal implementation note: It is possible that we should restirct
`a(t)` to be smooth or at least twice differentiable.
-/
@[sorryful]
def FLRW : Type := sorry

namespace FLRW

/-- The hubble constant defined in terms of the scale factor
  as `(dₜ a) / a`.

  The notation `H` is used for the `hubbleConstant`.

  Semiformal implementation note: Implement also scoped notation. -/
informal_definition hubbleConstant where
  deps := []
  tag := "6Z2NB"

/-- The deceleration parameter defined in terms of the scale factor
  as `- (dₜdₜ a) a / (dₜ a)^2`.

  The notation `q` is used for the `decelerationParameter`.

  Semiformal implementation note: Implement also scoped notation. -/
informal_definition decelerationParameter where
  deps := []
  tag := "6Z2UE"

/-- The deceleration parameter is equal to `- (1 + (dₜ H)/H^2)`. -/
informal_lemma decelerationParameter_eq_one_plus_hubbleConstant where
  deps := []
  tag := "6Z23H"

/-- The time evolution of the hubble parameter is equal to `dₜ H = - H^2 (1 + q)`. -/
informal_lemma time_evolution_hubbleConstant where
  deps := []
  tag := "6Z3BS"

/-- There exists a time at which the hubble constant decreases if and only if
  there exists a time where the deceleration parameter is less then `-1`. -/
informal_lemma hubbleConstant_decrease_iff where
  deps := []
  tag := "6Z3FS"

end FLRW

end Cosmology
