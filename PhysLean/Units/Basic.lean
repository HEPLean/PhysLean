/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.Basic
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
  appropriate physics directory. (Not all of these are implemented yet.)
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:
- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303

-/

/-!

## Defining dimensions

-/


/-- The foundational dimensions.
  Defined in the order ⟨length, time, mass, charge, temperature⟩ -/
structure Dimension where
  length : ℚ
  time : ℚ
  mass : ℚ
  charge : ℚ
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

## Measured quantities

-/

open NNReal

/-- A measured quantity is a quantity which carries a dimension `d`, but which
  lives in a given (but arbitary) set of units. -/
structure Measured (d : Dimension) (M : Type) [SMul ℝ≥0 M] where
  /-- The value of the measured quantity. -/
  val : M
