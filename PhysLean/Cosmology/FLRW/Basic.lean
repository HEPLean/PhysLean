/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Luis Gabriel C. Bariuan
-/
import Mathlib
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.SpaceAndTime.Space.Basic
open Filter
open scoped Topology
/-!

# The Friedmann-Lemaître-Robertson-Walker metric

Parts of this file is currently informal or semiformal.

-/

namespace Cosmology

/-- The inductive type with three constructors:
- `Spherical (k : ℝ)`
- `Flat`
- `Saddle (k : ℝ)`
-/

-- def SpatialGeometry : Type := sorry
inductive SpatialGeometry : Type where
  | Spherical (k : ℝ) (h: k < 0)
  | Flat (k : ℝ) (h: k = 0)
  | Saddle (k : ℝ) (h : k > 0)

namespace SpatialGeometry
/-- For `s` corresponding to
- `Spherical k`, `S s r = k * sin (r / k)`
- `Flat`, `S s r = r`,
- `Saddle k`, `S s r = k * sinh (r / k)`.
-/

noncomputable def S (s : SpatialGeometry) : ℝ → ℝ :=
  fun r =>
    match s with
    | SpatialGeometry.Spherical k _ => k * Real.sin (r / k)
    | SpatialGeometry.Flat _ _ => r
    | SpatialGeometry.Saddle k _ => k * Real.sinh (r / k)
/-- The limit of `S (Saddle k) r` as `k → ∞` is equal to `S (Flat) r`. -/
/-- First show that `k * sinh(r / k) = sinh(r / k) / (1 / k)` pointwise. -/
lemma mul_sinh_as_div (r k : ℝ) :
  k * Real.sinh (r / k) = Real.sinh (r / k) / (1 / k) := by field_simp
@[sorryful]
/-- First, show that limit of `sinh(r * x) / x` is r at the limit x goes to zero.
Then the next theorem will address the rewrite using Filter.Tendsto.comp -/
lemma tendsto_sinh_rx_over_x (r : ℝ) :
  Tendsto (fun x : ℝ => Real.sinh (r * x) / x) (𝓝[≠] 0) (𝓝 r) := by sorry
@[sorryful]
lemma limit_S_saddle(r : ℝ) :
  Tendsto (fun k : ℝ => k * Real.sinh (r / k)) atTop (𝓝 r) := by sorry
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
