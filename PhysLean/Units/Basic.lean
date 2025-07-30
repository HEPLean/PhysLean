/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Dimensions and unit

A unit in physics arises from choice of something in physics which is non-canonical.
An example is the choice of translationally-invariant metric on the time manifold `TimeMan`.

A dimension is a property of a quantity related to how it changes with respect to a
change in the unit.

The fundamental choices one has in physics are related to:
- Time
- Length
- Mass
- Charge
- Temperature

(In fact temperature is not really a fundamental choice, however we leave this as a `TODO`.)

From these fundamental choices one can construct all other units and dimensions.

## Implementation details

Units within PhysLean are implemented with the following convention:
- The fundamental units, and the choices they correspond to, are defined within the
  appropriate physics directory, in particular:
  - `PhysLean/SpaceAndTime/Time/TimeUnit.lean`
  - `PhysLean/SpaceAndTime/Space/LengthUnit.lean`
  - `PhysLean/ClassicalMechanics/Mass/MassUnit.lean`
  - `PhysLean/Electromagnetism/Charge/ChargeUnit.lean`
  - `PhysLean/Thermodynamics/Temperature/TemperatureUnit.lean`
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:
- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303

## Note

A lot of the results around units is still experimental and should be adapted based on needs.
-/

/-!

## Defining dimensions

-/

/-- The foundational dimensions.
  Defined in the order ⟨length, time, mass, charge, temperature⟩ -/
structure Dimension where
  /-- The length dimension. -/
  length : ℚ
  /-- The time dimension. -/
  time : ℚ
  /-- The mass dimension. -/
  mass : ℚ
  /-- The charge dimension. -/
  charge : ℚ
  /-- The temperature dimension. -/
  temperature : ℚ

namespace Dimension

instance : Zero Dimension where
  zero := ⟨0, 0, 0, 0, 0⟩

lemma zero_eq : (0 : Dimension) = ⟨0, 0, 0, 0, 0⟩ := rfl

instance : Mul Dimension where
  mul d1 d2 := ⟨d1.length + d2.length,
    d1.time + d2.time,
    d1.mass + d2.mass,
    d1.charge + d2.charge,
    d1.temperature + d2.temperature⟩

@[simp]
lemma time_mul (d1 d2 : Dimension) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_add (d1 d2 : Dimension) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_add (d1 d2 : Dimension) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

instance : Inv Dimension where
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature⟩

instance : Pow Dimension ℚ where
  pow d n := ⟨d.length * n, d.time * n, d.mass * n, d.charge * n, d.temperature * n⟩

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0⟩

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0⟩

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0⟩

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0⟩

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1⟩

end Dimension

/-!

## Dimensionalful

Given a type `M` with a dimension `d`, a dimensionalful quantity is a
map from `UnitChoices` to `M`, which scales with the choice of unit according to `d`.

See: https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/530520545

-/

TODO "IQ34V" "Define the type of dimensionalful quantities following:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/530520545"

/-!

## Measured quantities

We defined `Measured d M` to be a type of measured quantity of type `M` and of dimension `d`,
the terms of `Measured d M` are corresponds to values of the quantity in a given but arbitary
set of units.

If `M` has the type of a vector space, then the type `Measured d M` inherits this structure.

Likewise if `M` has the type of an inner product space, then the type `Measured d M`
inherits this structure. However, note that the inner product space does not explicit track
the dimension, mapping down to `ℝ`. This is in theory fine, as it is still dimensionful, in the
sense that it scales with the choice of unit.

-/

open NNReal

/-- A measured quantity is a quantity which carries a dimension `d`, but which
  lives in a given (but arbitary) set of units. -/
structure Measured (d : Dimension) (M : Type) [SMul ℝ≥0 M] where
  /-- The value of the measured quantity. -/
  val : M

instance {d1 d2 : Dimension} {M1 M2 M : Type} [SMul ℝ≥0 M1] [SMul ℝ≥0 M2]
    [SMul ℝ≥0 M] [HMul M1 M2 M] :
    HMul (Measured d1 M1) (Measured d2 M2) (Measured (d1 * d2) M) where
  hMul x y := ⟨x.val * y.val⟩

instance {d1 d2 : Dimension} {M1 M2 M : Type} [SMul ℝ≥0 M1] [SMul ℝ≥0 M2]
    [SMul ℝ≥0 M] [HSMul M1 M2 M] :
    HSMul (Measured d1 M1) (Measured d2 M2) (Measured (d1 * d2) M) where
  hSMul x y := ⟨x.val • y.val⟩
