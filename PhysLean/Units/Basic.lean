/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.TimeUnit
import PhysLean.SpaceAndTime.Space.LengthUnit
import PhysLean.ClassicalMechanics.Mass.MassUnit
import PhysLean.Electromagnetism.Charge.ChargeUnit
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
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

open NNReal

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

@[simp]
lemma inv_length (d : Dimension) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension) : d⁻¹.temperature = -d.temperature := rfl

instance : Pow Dimension ℚ where
  pow d n := ⟨d.length * n, d.time * n, d.mass * n, d.charge * n, d.temperature * n⟩

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0⟩

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0⟩

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0⟩

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0⟩

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1⟩

end Dimension

/-!

## Units

-/

/-- The choice of units. -/
structure UnitChoices where
  /-- The length unit. -/
  length : LengthUnit
  /-- The time unit. -/
  time : TimeUnit
  /-- The mass unit. -/
  mass : MassUnit
  /-- The charge unit. -/
  charge : ChargeUnit
  /-- The temperature unit. -/
  temperature : TemperatureUnit

namespace UnitChoices

/-- Given two choices of units `u1` and `u2` and a dimension `d`, the
  element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d`
  when changing from units `u1` to `u2`. -/
noncomputable def dimScale (u1 u2 : UnitChoices) (d : Dimension) : ℝ≥0 :=
  (u1.length / u2.length) ^ (d.length : ℝ) *
  (u1.time / u2.time) ^ (d.time : ℝ) *
  (u1.mass / u2.mass) ^ (d.mass : ℝ) *
  (u1.charge / u2.charge) ^ (d.charge : ℝ) *
  (u1.temperature / u2.temperature) ^ (d.temperature : ℝ)

@[simp]
lemma dimScale_self (u : UnitChoices) (d : Dimension) :
    dimScale u u d = 1 := by
  simp [dimScale]

lemma dimScale_transitive (u1 u2 u3 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  simp [dimScale]
  trans ((u1.length / u2.length) ^ (d.length : ℝ) * (u2.length / u3.length) ^ (d.length : ℝ)) *
    ((u1.time / u2.time) ^ (d.time : ℝ) * (u2.time / u3.time) ^ (d.time : ℝ)) *
    ((u1.mass / u2.mass) ^ (d.mass : ℝ) * (u2.mass / u3.mass) ^ (d.mass : ℝ)) *
    ((u1.charge / u2.charge) ^ (d.charge : ℝ) * (u2.charge / u3.charge) ^ (d.charge : ℝ)) *
    ((u1.temperature / u2.temperature) ^ (d.temperature : ℝ) *
      (u2.temperature / u3.temperature) ^ (d.temperature : ℝ))
  · ring
  repeat rw [← mul_rpow]
  apply NNReal.eq
  simp only [LengthUnit.div_eq_val, TimeUnit.div_eq_val, MassUnit.div_eq_val, ChargeUnit.div_eq_val,
    TemperatureUnit.div_eq_val, NNReal.coe_mul, coe_rpow, coe_mk]
  field_simp

/-- The choice of units corresponding to SI units, that is
- meters,
- seconds,
- kilograms,
- columbs,
- kelvin.
-/
noncomputable def SI : UnitChoices where
  length := LengthUnit.meters
  time := TimeUnit.seconds
  mass := MassUnit.kilograms
  charge := ChargeUnit.coulombs
  temperature := TemperatureUnit.kelvin

@[simp]
lemma SI_length : SI.length = LengthUnit.meters := rfl

@[simp]
lemma SI_time : SI.time = TimeUnit.seconds := rfl

@[simp]
lemma SI_mass : SI.mass = MassUnit.kilograms := rfl

@[simp]
lemma SI_charge : SI.charge = ChargeUnit.coulombs := rfl

@[simp]
lemma SI_temperature : SI.temperature = TemperatureUnit.kelvin := rfl

end UnitChoices

/-!

## Dimensionful

Given a type `M` with a dimension `d`, a dimensionful quantity is a
map from `UnitChoices` to `M`, which scales with the choice of unit according to `d`.

See: https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/530520545

-/

/-- A quantity of type `M` which depends on a choice of units `UnitChoices` is said to be
  of dimension `d` if it scales by `UnitChoices.dimScale u1 u2 d` under a change in units. -/
def HasDimension (d : Dimension) {M : Type} [SMul ℝ≥0 M] (f : UnitChoices → M) : Prop :=
  ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 d • f u1

lemma hasDimension_iff {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    (f : UnitChoices → M) :
    HasDimension d f ↔ ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 d • f u1 := by
  rfl

/-- The type of maps from `UnitChoices` to `M` which have dimension `d`. -/
def Dimensionful (d : Dimension) (M : Type) [SMul ℝ≥0 M] :=
  {f : UnitChoices → M // HasDimension d f}

namespace Dimensionful

lemma eq_of_val {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : f1.1 = f2.1) : f1 = f2 := by
  cases f1
  cases f2
  simp_all

instance {d : Dimension} {M : Type} [MulAction ℝ≥0 M] : MulAction ℝ≥0 (Dimensionful d M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp
    rw [f.2 u1 u2]
    rw [smul_comm]⟩
  one_smul f := by
    apply eq_of_val
    ext u
    change 1 • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    apply eq_of_val
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

instance {d : Dimension} {M : Type} [MulAction ℝ M] : MulAction ℝ (Dimensionful d M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp
    rw [f.2 u1 u2]
    rw [smul_comm]⟩
  one_smul f := by
    apply eq_of_val
    ext u
    change 1 • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    apply eq_of_val
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

instance {d : Dimension} : LE (Dimensionful d ℝ≥0) where
  le f1 f2 := ∀ u, f1.1 u ≤ f2.1 u

end Dimensionful

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

/-- A measured quantity is a quantity which carries a dimension `d`, but which
  lives in a given (but arbitary) set of units. -/
structure Measured (d : Dimension) (M : Type) [SMul ℝ≥0 M] where
  /-- The value of the measured quantity. -/
  val : M

namespace Measured

@[ext]
lemma eq_of_val {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {m1 m2 : Measured d M} (h : m1.val = m2.val) : m1 = m2 := by
  cases m1
  cases m2
  simp_all

instance {d : Dimension} {α : Type} {M : Type} [SMul ℝ≥0 M] [SMul α M] : SMul α (Measured d M) where
  smul r m := ⟨r • m.val⟩

@[simp]
lemma smul_val {d : Dimension} {α : Type} {M : Type} [SMul ℝ≥0 M] [SMul α M]
    (r : α) (m : Measured d M) :
    (r • m).val = r • m.val := rfl

instance {d1 d2 : Dimension} {M1 M2 M : Type} [SMul ℝ≥0 M1] [SMul ℝ≥0 M2]
    [SMul ℝ≥0 M] [HMul M1 M2 M] :
    HMul (Measured d1 M1) (Measured d2 M2) (Measured (d1 * d2) M) where
  hMul x y := ⟨x.val * y.val⟩

instance {d1 d2 : Dimension} {M1 M2 M : Type} [SMul ℝ≥0 M1] [SMul ℝ≥0 M2]
    [SMul ℝ≥0 M] [HSMul M1 M2 M] :
    HSMul (Measured d1 M1) (Measured d2 M2) (Measured (d1 * d2) M) where
  hSMul x y := ⟨x.val • y.val⟩

instance {d : Dimension} {M : Type} [SMul ℝ≥0 M] [LE M] : LE (Measured d M) where
  le x y := x.val ≤ y.val

lemma le_eq_le_val {d : Dimension} {M : Type} [SMul ℝ≥0 M] [LE M]
    (x y : Measured d M) : x ≤ y ↔ x.val ≤ y.val := by
  rfl

end Measured

/-!

## Relating `Measured` and `Dimensionful`

-/

namespace Dimensionful

instance {d : Dimension} {M : Type} [SMul ℝ≥0 M] :
    CoeFun (Dimensionful d M) (fun _ => UnitChoices → Measured d M) where
  coe f := fun u => ⟨f.1 u⟩

lemma coe_hasDimension {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    (f : Dimensionful d M) :
    HasDimension d (f : UnitChoices → Measured d M) := by
  intro u1 u2
  simp only
  rw [f.2 u1 u2]
  rfl

lemma eq_of_apply {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : ∀ u, f1 u = f2 u) : f1 = f2 := by
  apply eq_of_val
  simp_all
  ext u
  exact h u

lemma eq_of_unitChoices {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (u : UnitChoices) (h : f1 u = f2 u) : f1 = f2 := by
  refine eq_of_apply ?_
  simp only [Measured.mk.injEq]
  simp at h
  intro u2
  rw [f1.2 u, h, ← f2.2 u]

lemma eq_of_SI {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : f1 UnitChoices.SI = f2 UnitChoices.SI) : f1 = f2 := by
  refine eq_of_unitChoices UnitChoices.SI ?_
  exact h

@[simp]
lemma smul_apply {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (f : Dimensionful d M) (u : UnitChoices) (a : ℝ≥0) :
    (a • f : Dimensionful d M) u = a • f u := by
  ext
  simp
  exact rfl

lemma le_nnReals_of_single_unitChoice {d} {f1 f2 : Dimensionful d ℝ≥0}
      (u : UnitChoices) (h : f1 u ≤ f2 u) : f1 ≤ f2 := by
  intro u2
  rw [f1.2 u, f2.2 u]
  simp
  apply mul_le_mul_left'
  exact h

end Dimensionful

namespace Measured

noncomputable instance {d : Dimension} {M : Type} [MulAction ℝ≥0 M] :
    HSMul (Measured d M) UnitChoices (Dimensionful d M) where
  hSMul m u := ⟨fun u1 => (u.dimScale u1 d) • m.val, fun u1 u2 => by
    simp [smul_smul, mul_comm, UnitChoices.dimScale_transitive]⟩

@[simp]
lemma smul_unitChoices_apply {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (m : Measured d M) (u : UnitChoices) (u1 : UnitChoices) :
    (m • u) u1 = u.dimScale u1 d • m := rfl

end Measured
