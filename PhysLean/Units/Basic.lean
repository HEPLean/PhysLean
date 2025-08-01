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
lemma length_mul (d1 d2 : Dimension) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

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

@[simp]
lemma dimScale_zero (u1 u2 : UnitChoices) :
    dimScale u1 u2 0 = 1 := by
  simp [dimScale, Dimension.zero_eq]

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

@[simp]
lemma dimScale_mul (u1 u2 : UnitChoices) (d1 d2 : Dimension) :
    dimScale u1 u2 (d1 * d2) = dimScale u1 u2 d1 * dimScale u1 u2 d2 := by
  simp [dimScale]
  repeat rw [rpow_add]
  ring
  all_goals
    simp

@[simp]
lemma dimScale_neq_zero (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d ≠ 0 := by
  simp [dimScale]

lemma dimScale_inv (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d⁻¹ = (dimScale u1 u2 d)⁻¹ := by
  simp only [dimScale, Dimension.inv_length, Rat.cast_neg, Dimension.inv_time, Dimension.inv_mass,
    Dimension.inv_charge, Dimension.inv_temperature, mul_inv]
  congr
  all_goals
  · exact rpow_neg _ _

lemma dimScale_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d = (dimScale u2 u1 d)⁻¹ := by
  simp only [dimScale, mul_inv]
  congr
  · rw [LengthUnit.div_symm, inv_rpow]
  · rw [TimeUnit.div_symm, inv_rpow]
  · rw [MassUnit.div_symm, inv_rpow]
  · rw [ChargeUnit.div_symm, inv_rpow]
  · rw [TemperatureUnit.div_symm, inv_rpow]

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

/-- Applying an element of `Dimensionful d M` to a unit choice gives an element of `M`. -/
instance {d : Dimension} {M : Type} [SMul ℝ≥0 M] :
    CoeFun (Dimensionful d M) (fun _ => UnitChoices → M) where
  coe f := f.1

lemma coe_hasDimension {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    (f : Dimensionful d M) :
    HasDimension d (f : UnitChoices → M) := by
  intro u1 u2
  rw [f.2 u1 u2]

/-!

### Equality lemmas

-/

lemma eq_of_val {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : f1.1 = f2.1) : f1 = f2 := by
  cases f1
  cases f2
  simp_all

lemma eq_of_apply {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : ∀ u, f1 u = f2 u) : f1 = f2 := by
  apply eq_of_val
  ext u
  exact h u

lemma eq_of_unitChoices {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (u : UnitChoices) (h : f1 u = f2 u) : f1 = f2 := by
  refine eq_of_apply ?_
  intro u2
  rw [f1.2 u, h, ← f2.2 u]

lemma eq_of_SI {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    {f1 f2 : Dimensionful d M} (h : f1 UnitChoices.SI = f2 UnitChoices.SI) : f1 = f2 := by
  refine eq_of_unitChoices UnitChoices.SI ?_
  exact h

/-!

### MulAction

-/

instance {d : Dimension} {M : Type} [MulAction ℝ≥0 M] : MulAction ℝ≥0 (Dimensionful d M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
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
    simp only
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

@[simp]
lemma smul_apply {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (f : Dimensionful d M) (u : UnitChoices) (a : ℝ≥0) :
    (a • f : Dimensionful d M) u = a • f u := by rfl

@[simp]
lemma smul_real_apply {d : Dimension} {M : Type} [MulAction ℝ M]
    (f : Dimensionful d M) (u : UnitChoices) (a : ℝ) :
    (a • f : Dimensionful d M) u = a • f u := by rfl

/-!

## ofUnit

-/

/-- The creation of an element `f : Dimensionful d M` given a `m : M` and a choice of
  units `u : UnitChoices`, defined such that `f u = m`. -/
noncomputable def ofUnit (d : Dimension) {M : Type} [MulAction ℝ≥0 M]
    (m : M) (u : UnitChoices) : Dimensionful d M where
  val := fun u1=> (u.dimScale u1 d) • m
  property := fun u1 u2 => by
    simp [smul_smul, mul_comm]
    rw [UnitChoices.dimScale_transitive]

lemma ofUnit_eq_mul_dimScale {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (m : M) (u1 u2 : UnitChoices) :
    ofUnit d m u1 = (UnitChoices.dimScale u1 u2 d) • ofUnit d m u2 := by
  apply eq_of_val
  ext u
  simp [ofUnit, smul_smul]
  rw [UnitChoices.dimScale_transitive]

@[simp]
lemma ofUnit_apply_self {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (m : M) (u : UnitChoices) :
    (ofUnit d m u) u = m := by
  simp [ofUnit, smul_smul]

lemma ofUnit_apply {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (m : M) (u1 u2 : UnitChoices) :
    (ofUnit d m u1) u2 = UnitChoices.dimScale u1 u2 d • m := by
  simp [ofUnit, smul_smul]

/-!

### LE

-/

instance {d : Dimension} : LE (Dimensionful d ℝ≥0) where
  le f1 f2 := ∀ u, f1.1 u ≤ f2.1 u

lemma le_nnReals_of_unitChoice {d} {f1 f2 : Dimensionful d ℝ≥0}
    (u : UnitChoices) (h : f1 u ≤ f2 u) : f1 ≤ f2 := by
  intro u2
  rw [f1.2 u, f2.2 u]
  simp only [smul_eq_mul]
  apply mul_le_mul_left'
  exact h

/-!

### Addition and module structure

-/

instance {d : Dimension} {M : Type} [AddZeroClass M] [DistribSMul ℝ≥0 M] :
    AddZeroClass (Dimensionful d M) where
  zero := ⟨fun _ => 0, fun _ _ => by simp⟩
  add f1 f2 := ⟨fun u => f1.1 u + f2.1 u, fun u1 u2 => by
    simp only
    rw [f1.2 u1 u2, f2.2 u1 u2]
    simp [smul_add]⟩
  zero_add f := by
    apply eq_of_val
    ext u
    change (0 : M) + f.1 u = f.1 u
    simp
  add_zero f := by
    apply eq_of_val
    ext u
    change f.1 u + (0 : M) = f.1 u
    simp

@[simp]
lemma add_apply {d : Dimension} {M : Type} [AddZeroClass M] [DistribSMul ℝ≥0 M]
    (f1 f2 : Dimensionful d M) (u : UnitChoices) :
    (f1 + f2 : Dimensionful d M) u = f1 u + f2 u := rfl

instance {d : Dimension} {M : Type} [AddCommGroup M] [DistribSMul ℝ≥0 M] :
    AddCommGroup (Dimensionful d M) where
  add_assoc f1 f2 f3 := by
    apply eq_of_val
    ext u
    change (f1.1 u + f2.1 u) + f3.1 u = f1.1 u + (f2.1 u + f3.1 u)
    simp [add_assoc]
  neg f := ⟨fun u => - f.1 u, fun u1 u2 => by
    simp only [smul_neg, neg_inj]
    rw [f.2 u1 u2]⟩
  nsmul n f := ⟨fun u => n • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2, smul_comm]⟩
  zsmul n f := ⟨fun u => n • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2, smul_comm]⟩
  neg_add_cancel f1 := by
    apply eq_of_val
    ext u
    simp
    rfl
  add_comm f1 f2 := by
    apply eq_of_val
    ext u
    change f1.1 u + f2.1 u = f2.1 u + f1.1 u
    simp [add_comm]
  nsmul_zero f := by simp; rfl
  nsmul_succ n f := by
    apply eq_of_val
    ext u
    simp [succ_nsmul]
  zsmul_zero' f := by
    apply eq_of_val
    ext u
    simp
    rfl
  zsmul_succ' n f := by
    apply eq_of_val
    ext u
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, natCast_zsmul, add_apply]
    rw [@add_one_zsmul]
    simp
  zsmul_neg' n f := by
    apply eq_of_val
    ext u
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    erw [← neg_zsmul]
    rfl

@[simp]
lemma neg_apply {d : Dimension} {M : Type} [AddCommGroup M] [DistribSMul ℝ≥0 M]
    (f : Dimensionful d M) (u : UnitChoices) :
    (-f : Dimensionful d M) u = -f u := rfl

@[simp]
lemma zero_apply {d : Dimension} {M : Type} [AddZeroClass M] [DistribSMul ℝ≥0 M]
    (u : UnitChoices) : (0 : Dimensionful d M) u = 0 := rfl

instance {d : Dimension} {M : Type} [AddCommGroup M] [Module ℝ M] :
    Module ℝ (Dimensionful d M) where
  smul_zero a := by
    apply eq_of_val
    ext u
    simp
  smul_add a f1 f2 := by
    apply eq_of_val
    ext u
    change a • (f1.1 u + f2.1 u) = a • f1.1 u + a • f2.1 u
    simp [smul_add]
  add_smul a1 a2 f2 := by
    apply eq_of_val
    ext u
    simp [add_smul]
  zero_smul f := by
    apply eq_of_val
    ext u
    change (0 : ℝ) • f.1 u = 0
    simp

@[simp]
lemma sub_apply {d : Dimension} {M : Type} [AddCommGroup M] [DistribSMul ℝ≥0 M]
    (f1 f2 : Dimensionful d M) (u : UnitChoices) :
    (f1 - f2 : Dimensionful d M) u = f1 u - f2 u := by
  rw [@sub_eq_neg_add]
  simp only [add_apply, neg_apply]
  abel

/-!

### Multiplication

-/

instance {d1 d2 : Dimension} :
    HMul (Dimensionful d1 ℝ) (Dimensionful d2 ℝ) (Dimensionful (d1 * d2) ℝ) where
  hMul x y := ⟨fun u => x.1 u * y.1 u, fun u1 u2 => by
    simp only
    rw [x.2 u1 u2, y.2 u1 u2]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, UnitChoices.dimScale_mul]
    change u1.dimScale u2 d2 * (u1.dimScale u2 d1 * (x u1 * y u1)) =
      (u1.dimScale u2 d1 * u1.dimScale u2 d2) * (x u1 * y u1)
    ring⟩

@[simp]
lemma mul_real_apply {d1 d2 : Dimension}
    (x : Dimensionful d1 ℝ) (y : Dimensionful d2 ℝ) (u : UnitChoices) :
    (x * y) u = x u * y u := rfl

/-!

### Division

-/

noncomputable instance {d1 d2 : Dimension} :
    HDiv (Dimensionful d1 ℝ) (Dimensionful d2 ℝ) (Dimensionful (d1 * d2⁻¹) ℝ) where
  hDiv x y := ⟨fun u => x.1 u / y.1 u, fun u1 u2 => by
    simp only
    rw [x.2 u1 u2, y.2 u1 u2]
    simp only [UnitChoices.dimScale_mul]
    change (u1.dimScale u2 d1 * x u1) / (u1.dimScale u2 d2 * y u1) =
      (u1.dimScale u2 d1 * u1.dimScale u2 d2⁻¹) * (x u1 / y u1)
    rw [UnitChoices.dimScale_inv]
    by_cases h0 : y.1 u1 = 0
    · simp [h0]
    have h0 : toReal (u1.dimScale u2 d2) ≠ 0 := by
      simp [UnitChoices.dimScale_neq_zero]
    field_simp⟩

@[simp]
lemma hdiv_apply {d1 d2 : Dimension}
    (x : Dimensionful d1 ℝ) (y : Dimensionful d2 ℝ) (u : UnitChoices) :
    (x / y) u = x u / y u := rfl

noncomputable instance {d2 : Dimension} :
    HDiv ℝ (Dimensionful d2 ℝ) (Dimensionful (d2⁻¹) ℝ) where
  hDiv x y := ⟨fun u => x / y.1 u, fun u1 u2 => by
    simp only
    rw [y.2 u1 u2]
    change x / (u1.dimScale u2 d2 * y u1) =
      (u1.dimScale u2 d2⁻¹) * (x / y u1)
    rw [UnitChoices.dimScale_inv]
    by_cases h0 : y.1 u1 = 0
    · simp [h0]
    have h0 : toReal (u1.dimScale u2 d2) ≠ 0 := by
      simp [UnitChoices.dimScale_neq_zero]
    field_simp⟩

/-!

### SMul

-/

noncomputable instance {d1 d2 : Dimension} {M : Type} [AddCommGroup M] [Module ℝ M] :
    HSMul (Dimensionful d1 ℝ) (Dimensionful d2 M) (Dimensionful (d1 * d2) M) where
  hSMul x y := ⟨fun u => x.1 u • y.1 u, fun u1 u2 => by
    simp only
    rw [x.2 u1 u2, y.2 u1 u2]
    simp only [smul_assoc, UnitChoices.dimScale_mul]
    erw [smul_smul, smul_smul, smul_smul]
    congr 1
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_toRealHom, NNReal.coe_mul]
    ring⟩

@[simp]
lemma hsmul_apply {d1 d2 : Dimension} {M : Type} [AddCommGroup M] [Module ℝ M]
    (x : Dimensionful d1 ℝ) (y : Dimensionful d2 M) (u : UnitChoices) :
    (x • y) u = x u • y u := rfl

/-!

## Inner product

We define the inner product in SI units.
-/

open InnerProductSpace
open UnitChoices

noncomputable instance {M} {d : Dimension}
    [SeminormedAddCommGroup M] [InnerProductSpace ℝ M]:
    SeminormedAddCommGroup (Dimensionful d M) where
  norm f := ‖f.1 SI‖
  dist_self := by intro x; simp
  dist_comm := by intro x y; simp; exact norm_sub_rev _ _
  dist_triangle := by
    intro x y z
    simp only [sub_apply]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _

noncomputable instance {M} {d : Dimension}
    [SeminormedAddCommGroup M] [InnerProductSpace ℝ M]:
    InnerProductSpace ℝ (Dimensionful d M) where
  inner x y := ⟪x.1 SI, y.1 SI⟫_ℝ
  norm_smul_le r y := norm_smul_le r (y.1 SI)
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (x.1 SI)
  conj_inner_symm x y := conj_inner_symm (x.1 SI) (y.1 SI)
  add_left x y z := add_left (x.1 SI) (y.1 SI) (z.1 SI)
  smul_left x y r := smul_left (x.1 SI) (y.1 SI) r

/-!

### Derivatives

-/

TODO "IY4PB" "The derivative of a dimensionful quantities is only defined for `ℝ`,
  this should be generalized to other types, carrying the relevant structure."

/-- The derivative using dimensionalful quantities. -/
noncomputable def deriv {d1 d2 : Dimension} (f : Dimensionful d1 ℝ → Dimensionful d2 ℝ)
    (atLocation : Dimensionful d1 ℝ) :
    Dimensionful (d2 * d1⁻¹) ℝ where
  val := fun u =>
    /- The derivative of `f` at location `atLocation` in the direction `(ofUnit d1 1 u)`
      in coordinates `u`. -/
    (fderiv ℝ f atLocation (ofUnit d1 1 u)) u
  property := fun u1 u2 => by
    simp only [dimScale_mul]
    let F := (fderiv ℝ f atLocation (ofUnit d1 1 u2))
    change F u2 = _
    rw [F.2 u1]
    dsimp [F]
    have h1 : ofUnit d1 (1 : ℝ) u2 = (UnitChoices.dimScale u2 u1 d1) • ofUnit d1 1 u1 := by
      rw [← ofUnit_eq_mul_dimScale]
    rw [h1]
    simp [smul_smul]
    congr 2
    rw [dimScale_symm]
    exact Eq.symm (dimScale_inv u1 u2 d1)

/-!

### valCast

-/

set_option linter.unusedVariables false in
/-- The casting of a quantity in `Dimensionful 0 M` to its underlying element in `M`. -/
@[nolint unusedArguments]
noncomputable def valCast {d : Dimension} {M : Type} [SMul ℝ≥0 M]
    (f : Dimensionful d M) (hd : d = 0 := by rfl) : M :=
  f.1 UnitChoices.SI

lemma valCast_eq_unitChoices {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    {f : Dimensionful d M} {hd : d = 0} (u : UnitChoices) :
    valCast f hd = f u := by
  simp [valCast, hd]
  rw [f.2 UnitChoices.SI u]
  subst hd
  simp

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

The type `Measured d M` can be seen as a convienent way to work with and keep track of
dimensions. However, working with `Measured d M` does not formally prove anything
about dimensions, which can only be done with `Dimensionful d M`, or other
manifest considerations of `UnitChoices`.

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

/-!

### Basic instances carried from underlying type.

-/

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

noncomputable instance {d : Dimension} {M : Type} [MulAction ℝ≥0 M] :
    HSMul (Measured d M) UnitChoices (Dimensionful d M) where
  hSMul m u := ⟨fun u1 => (u.dimScale u1 d) • m.val, fun u1 u2 => by
    simp [smul_smul, mul_comm, UnitChoices.dimScale_transitive]⟩

@[simp]
lemma smul_unitChoices_apply {d : Dimension} {M : Type} [MulAction ℝ≥0 M]
    (m : Measured d M) (u : UnitChoices) (u1 : UnitChoices) :
    (m • u) u1 = u.dimScale u1 d • m.val := rfl

end Measured
