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

@[ext]
lemma ext {d1 d2 : Dimension}
    (h1 : d1.length = d2.length)
    (h2 : d1.time = d2.time)
    (h3 : d1.mass = d2.mass)
    (h4 : d1.charge = d2.charge)
    (h5 : d1.temperature = d2.temperature) :
    d1 = d2 := by
  cases d1
  cases d2
  congr

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

instance : CommGroup Dimension where
  mul_assoc a b c := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul]
      ring
  one := 0
  one_mul a := by
    change 0 * a = a
    ext
    all_goals
      simp [zero_eq]
  mul_one a := by
    change a * 0 = a
    ext
    all_goals
      simp [zero_eq]
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature⟩
  inv_mul_cancel a := by
    change _ = 0
    ext
    all_goals simp [zero_eq]
  mul_comm a b := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul]
      ring

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
@[ext]
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
lemma dimScale_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u1 d = 1 := by
  rw [dimScale_transitive, dimScale_self]

@[simp]
lemma dimScale_coe_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    (toReal (dimScale u1 u2 d)) * (toReal (dimScale u2 u1 d)) = 1 := by
  trans toReal (dimScale u1 u2 d * dimScale u2 u1 d)
  · rw [NNReal.coe_mul]
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

lemma dimScale_of_inv_eq_swap (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d⁻¹ = dimScale u2 u1 d := by
  rw [dimScale_inv]
  conv_rhs => rw[dimScale_symm]

TODO "LCSAY" "Make SI : UnitChoices computable, probably by
  replacing the axioms defining the units. See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/534914807"
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

## Types carrying dimensions

Dimensions are assigned to types with the following type-classes

- `CarriesDimension` for a type carrying an instance of `MulAction ℝ≥0 M`
- `ModuleCarriesDimension` for a type carrying an instance of `Module ℝ M`.

The latter is need to prevent a typeclass dimond.

-/

/-- A type `M` carries a dimension `d` if every element of `M` is supposed to have
  this dimension. For example, the type `Time` will carry a dimension `T𝓭`. -/
class CarriesDimension (M : Type) extends MulAction ℝ≥0 M where
  /-- The dimension carried by a type `M`. -/
  d : Dimension

/-- A module `M` carries a dimension `d` if every element of `M` is supposed to have
  this dimension.
  This is defined in additon to `CarriesDimension` to prevent a type-casting dimond. -/
class ModuleCarriesDimension (M : Type) [AddCommMonoid M] [Module ℝ M] where
  /-- The dimension carried by a module `M`. -/
  d : Dimension

instance {M : Type} [AddCommMonoid M] [Module ℝ M] [ModuleCarriesDimension M] :
    CarriesDimension M where
  d := ModuleCarriesDimension.d M

/-!

## Terms of the current dimension

Given a type `M` which carries a dimension `d`,
we are intrested in elements of `M` which depend on a choice of units, i.e. functions
`UnitChoices → M`.

We define both a proposition
- `HasDimension f` which says that `f` scales correctly with units,
and a type
- `Dimensionful M` which is the subtype of functions which `HasDimension`.

-/

/-- A quantity of type `M` which depends on a choice of units `UnitChoices` is said to be
  of dimension `d` if it scales by `UnitChoices.dimScale u1 u2 d` under a change in units. -/
def HasDimension {M : Type} [CarriesDimension M] (f : UnitChoices → M) : Prop :=
  ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 (CarriesDimension.d M) • f u1

lemma hasDimension_iff {M : Type} [CarriesDimension M] (f : UnitChoices → M) :
    HasDimension f ↔ ∀ u1 u2 : UnitChoices, f u2 =
    UnitChoices.dimScale u1 u2 (CarriesDimension.d M) • f u1 := by
  rfl

/-- The subtype of functions `UnitChoices → M`, for which `M` carries a dimension,
  which `HasDimension`. -/
def Dimensionful (M : Type) [CarriesDimension M] := Subtype (HasDimension (M := M))

@[ext]
lemma Dimensionful.ext {M : Type} [CarriesDimension M] (f1 f2 : Dimensionful M)
    (h : f1.val = f2.val) : f1 = f2 := by
  cases f1
  cases f2
  simp_all

instance {M : Type} [CarriesDimension M] : MulAction ℝ≥0 (Dimensionful M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2]
    rw [smul_comm]⟩
  one_smul f := by
    ext u
    change (1 : ℝ≥0) • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

@[simp]
lemma Dimensionful.smul_apply {M : Type} [CarriesDimension M]
    (a : ℝ≥0) (f : Dimensionful M) (u : UnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

/-- For `M` carying a dimension `d`, the equivalence between `M` and `Dimension M`,
  given a choice of units. -/
noncomputable def CarriesDimension.toDimensionful {M : Type} [CarriesDimension M]
    (u : UnitChoices) :
    M ≃ Dimensionful M where
  toFun m := {
    val := fun u1 => (u.dimScale u1 (CarriesDimension.d M)) • m
    property := fun u1 u2 => by
      simp [smul_smul]
      rw [mul_comm, UnitChoices.dimScale_transitive]}
  invFun f := f.1 u
  left_inv m := by
    simp
  right_inv f := by
    simp only
    ext u1
    simpa using (f.2 u u1).symm

lemma CarriesDimension.toDimensionful_apply_apply
    {M : Type} [CarriesDimension M] (u1 u2 : UnitChoices) (m : M) :
    (toDimensionful u1 m).1 u2 = (u1.dimScale u2 (CarriesDimension.d M)) • m := by rfl

/-!

## Types which depend on dimensions

In addition to types which carry a dimension, we also have types whose elements
depend on a choice of a units. For example a function
`f : M1 → M2` between two types `M1` and `M2` which carry dimensions does not itself
carry a dimensions, but is dependent on a choice of units.

We define three versions
- `UnitDependent M` having a function `scaleUnit : UnitChoices → UnitChoices → M → M`
  subject to two conditions `scaleUnit_trans` and `scaleUnit_id`
- `LinearUnitDependent M` extends `UnitDependent M` with additional linearity conditions
  on `scaleUnit`.
- `ContinuousLinearUnitDependent M` extends `LinearUnitDependent M` with an additional
  continuity condition on `scaleUnit`.

-/

open CarriesDimension

/-- A type carries the instance `UnitDependent M` if it depends on a choice of units.
  This dependence is manifested in `scaleUnit u1 u2` which describes how elements of `M` change
  under a scaling of units which would take `u1` to `u2`.

  This type is used for functions, and propositions etc.
-/
class UnitDependent (M : Type) where
  /-- `scaleUnit u1 u2` is the map transforming elements of `M` under a
    scaling of units which would take the unit `u1` to the unit `u2`. This is not
    to say that in `scaleUnit u1 u2 m` that `m` should be interpreted as being in the units `u1`,
    although this is often the case.
  -/
  scaleUnit : UnitChoices → UnitChoices → M → M
  scaleUnit_trans : ∀ u1 u2 u3 m, scaleUnit u2 u3 (scaleUnit u1 u2 m) = scaleUnit u1 u3 m
  scaleUnit_trans' : ∀ u1 u2 u3 m, scaleUnit u1 u2 (scaleUnit u2 u3 m) = scaleUnit u1 u3 m
  scaleUnit_id : ∀ u m, scaleUnit u u m = m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `MulAction ℝ≥0 M` instance on `M`.
-/
class MulUnitDependent (M : Type) [MulAction ℝ≥0 M] extends
    UnitDependent M where
  scaleUnit_mul : ∀ u1 u2 (r : ℝ≥0) m,
    scaleUnit u1 u2 (r • m) = r • scaleUnit u1 u2 m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `Module ℝ M` instance on `M`.
-/
class LinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M] extends UnitDependent M where
  scaleUnit_add : ∀ u1 u2 m1 m2,
    scaleUnit u1 u2 (m1 + m2) = scaleUnit u1 u2 m1 + scaleUnit u1 u2 m2
  scaleUnit_smul : ∀ u1 u2 (r : ℝ) m,
    scaleUnit u1 u2 (r • m) = r • scaleUnit u1 u2 m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `Module ℝ M` instance on `M`, and is continuous.
-/
class ContinuousLinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] extends LinearUnitDependent M where
  scaleUnit_cont : ∀ u1 u2, Continuous (scaleUnit u1 u2)

/-!

## Basic properties of scaleUnit

-/

@[simp]
lemma UnitDependent.scaleUnit_symm_apply {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    scaleUnit u2 u1 (scaleUnit u1 u2 m) = m := by
  rw [scaleUnit_trans, scaleUnit_id]

@[simp]
lemma UnitDependent.scaleUnit_injective {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m1 m2 : M) :
    scaleUnit u1 u2 m1 = scaleUnit u1 u2 m2 ↔ m1 = m2 := by
  constructor
  · intro h1
    have h2 : scaleUnit u2 u1 (scaleUnit u1 u2 m1) =
        scaleUnit u2 u1 (scaleUnit u1 u2 m2) := by rw [h1]
    simpa using h2
  · intro h
    subst h
    rfl

/-!

### Variations on the map scaleUnit

-/

open UnitDependent
/-- For an `M` with an instance of `UnitDependent M`, `scaleUnit u1 u2` as an equivalence. -/
def UnitDependent.scaleUnitEquiv {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) : M ≃ M where
  toFun m := scaleUnit u1 u2 m
  invFun m := scaleUnit u2 u1 m
  right_inv m := by simp
  left_inv m := by simp

/-- For an `M` with an instance of `LinearUnitDependent M`, `scaleUnit u1 u2` as a
  linear map. -/
def LinearUnitDependent.scaleUnitLinear
    {M : Type} [AddCommMonoid M] [Module ℝ M] [LinearUnitDependent M]
    (u1 u2 : UnitChoices) :
    M →ₗ[ℝ] M where
  toFun m := scaleUnit u1 u2 m
  map_add' m1 m2 := by simp [LinearUnitDependent.scaleUnit_add]
  map_smul' r m2 := by simp [LinearUnitDependent.scaleUnit_smul]

/-- For an `M` with an instance of `LinearUnitDependent M`, `scaleUnit u1 u2` as a
  linear equivalence. -/
def LinearUnitDependent.scaleUnitLinearEquiv {M : Type} [AddCommMonoid M]
    [Module ℝ M] [LinearUnitDependent M] (u1 u2 : UnitChoices) :
    M ≃ₗ[ℝ] M :=
    LinearEquiv.ofLinear (scaleUnitLinear u1 u2) (scaleUnitLinear u2 u1)
    (by ext u; simp [scaleUnitLinear])
    (by ext u; simp [scaleUnitLinear])

/-- For an `M` with an instance of `ContinuousLinearUnitDependent M`, `scaleUnit u1 u2` as a
  continuous linear map. -/
def ContinuousLinearUnitDependent.scaleUnitContLinear {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M →L[ℝ] M where
  toLinearMap := LinearUnitDependent.scaleUnitLinear u1 u2
  cont := ContinuousLinearUnitDependent.scaleUnit_cont u1 u2

/-- For an `M` with an instance of `ContinuousLinearUnitDependent M`, `scaleUnit u1 u2` as a
  continuous linear equivalence. -/
def ContinuousLinearUnitDependent.scaleUnitContLinearEquiv {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M ≃L[ℝ] M :=
    ContinuousLinearEquiv.mk (LinearUnitDependent.scaleUnitLinearEquiv u1 u2)
    (ContinuousLinearUnitDependent.scaleUnit_cont u1 u2)
    (ContinuousLinearUnitDependent.scaleUnit_cont u2 u1)

@[simp]
lemma ContinuousLinearUnitDependent.scaleUnitContLinearEquiv_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.scaleUnitContLinearEquiv u1 u2) m =
      scaleUnit u1 u2 m := rfl

@[simp]
lemma ContinuousLinearUnitDependent.scaleUnitContLinearEquiv_symm_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.scaleUnitContLinearEquiv u1 u2).symm m =
      scaleUnit u2 u1 m := rfl
/-!

### Instances of the type classes

We construct instance of the `UnitDependent`, `LinearUnitDependent` and
  `ContinuousLinearUnitDependent` type classes based on `CarriesDimension`
  and functions.

-/

open UnitDependent

noncomputable instance : UnitDependent UnitChoices where
  scaleUnit u1 u2 u := ⟨
      LengthUnit.scale (u2.length/u1.length) u.length (by simp),
      TimeUnit.scale (u2.time/u1.time) u.time (by simp),
      MassUnit.scale (u2.mass/u1.mass) u.mass (by simp),
      ChargeUnit.scale (u2.charge/u1.charge) u.charge (by simp),
      TemperatureUnit.scale (u2.temperature/u1.temperature) u.temperature (by simp)⟩
  scaleUnit_trans u1 u2 u3 u := by
    congr 1 <;> simp
  scaleUnit_trans' u1 u2 u3 u := by
    congr 1
    · simp [LengthUnit.div_eq_val]
    · simp [TimeUnit.div_eq_val]
    · simp [MassUnit.div_eq_val]
    · simp [ChargeUnit.div_eq_val]
    · simp [TemperatureUnit.div_eq_val]
  scaleUnit_id u1 u := by simp

@[simp]
lemma UnitChoices.scaleUnit_apply_fst (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 u1) = u2 := by
  simp [scaleUnit]
  apply UnitChoices.ext
  · simp [LengthUnit.scale, LengthUnit.div_eq_val]
  · simp [TimeUnit.scale, TimeUnit.div_eq_val]
  · simp [MassUnit.scale, MassUnit.div_eq_val]
  · simp [ChargeUnit.scale, ChargeUnit.div_eq_val]
  · simp [TemperatureUnit.scale, TemperatureUnit.div_eq_val]

@[simp]
lemma UnitChoices.dimScale_scaleUnit {u1 u2 u : UnitChoices} (d : Dimension) :
    u.dimScale (scaleUnit u1 u2 u) d = u1.dimScale u2 d := by
  simp [dimScale]
  congr 1
  congr 1
  congr 1
  congr 1
  · congr 1
    simp [scaleUnit]
    simp [LengthUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [TimeUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [MassUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [ChargeUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [TemperatureUnit.div_eq_val]

lemma Dimensionful.of_scaleUnit {M : Type} [CarriesDimension M] {u1 u2 u : UnitChoices}
    (c : Dimensionful M) :
    c.1 (scaleUnit u1 u2 u) =
    u1.dimScale u2 (CarriesDimension.d M) • c.1 (u) := by
  rw [c.2 u (scaleUnit u1 u2 u)]
  congr 1
  simp

noncomputable instance {M1 : Type} [CarriesDimension M1] : MulUnitDependent M1 where
  scaleUnit u1 u2 m := (toDimensionful u1 m).1 u2
  scaleUnit_trans u1 u2 u3 m := by
    simp [toDimensionful]
    rw [smul_smul, mul_comm, UnitChoices.dimScale_transitive]
  scaleUnit_trans' u1 u2 u3 m := by
    simp [toDimensionful, smul_smul, UnitChoices.dimScale_transitive]
  scaleUnit_id u m := by
    simp [toDimensionful, UnitChoices.dimScale_self]
  scaleUnit_mul u1 u2 r m := by
    simp [toDimensionful]
    exact smul_comm (u1.dimScale u2 (d M1)) r m

lemma CarriesDimension.scaleUnit_apply {M : Type} [CarriesDimension M]
    (u1 u2 : UnitChoices) (m : M) :
    scaleUnit u1 u2 m = (u1.dimScale u2 (d M)) • m := by
  simp [scaleUnit, toDimensionful_apply_apply]

lemma CarriesDimension.scaleUnit_apply' {M : Type} [AddCommMonoid M] [Module ℝ M]
    [ModuleCarriesDimension M]
    (u1 u2 : UnitChoices) (m : M) :
    scaleUnit u1 u2 m = ((u1.dimScale u2 (d M) : ℝ) • m : M) := by
  simp [scaleUnit, toDimensionful_apply_apply]
  rfl

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M]
    [ModuleCarriesDimension M] : LinearUnitDependent M where
  scaleUnit_add u1 u2 m1 m2 := by
    change (toDimensionful u1 (m1 + m2)).1 u2 = _
    rw [toDimensionful_apply_apply]
    simp
    rfl
  scaleUnit_smul u1 u2 r m := by
    change (toDimensionful u1 (r • m)).1 u2 = _
    rw [toDimensionful_apply_apply]
    rw [smul_comm]
    rfl

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M]
    [ModuleCarriesDimension M] [TopologicalSpace M]
    [ContinuousConstSMul ℝ M] : ContinuousLinearUnitDependent M where
  scaleUnit_cont u1 u2 := by
    change Continuous fun m => (toDimensionful u1 m).1 u2
    conv =>
      enter [1, m]
      rw [toDimensionful_apply_apply]
    change Continuous fun m => (u1.dimScale u2 (d M)).1 • m
    apply Continuous.const_smul
    exact continuous_id'

noncomputable instance {M1 M2 : Type} [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f m1)
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    funext m1
    exact scaleUnit_id u (f m1)

open LinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommMonoid M1] [Module ℝ M1]
    [AddCommMonoid M2] [Module ℝ M2] [LinearUnitDependent M2] :
    LinearUnitDependent (M1 →ₗ[ℝ] M2) where
  scaleUnit u1 u2 f := {
      toFun m1 := scaleUnit u1 u2 (f m1)
      map_add' m1 m2 := by simp [scaleUnit_add]
      map_smul' := by simp [scaleUnit_smul]}
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    ext m1
    exact scaleUnit_id u (f m1)
  scaleUnit_add u1 u2 f1 f2 := by
    ext m
    simp [scaleUnit_add]
  scaleUnit_smul u1 u2 r f := by
    ext m
    simp [scaleUnit_smul]

open LinearUnitDependent ContinuousLinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1]
    [AddCommGroup M2] [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  scaleUnit u1 u2 f :=
    ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ _)
      (scaleUnitContLinearEquiv u1 u2) f
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    ext m1
    exact scaleUnit_id u (f m1)
  scaleUnit_add u1 u2 f1 f2 := by simp
  scaleUnit_smul u1 u2 r f := by simp
  scaleUnit_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((ContinuousLinearEquiv.refl ℝ M1).arrowCongr (scaleUnitContLinearEquiv u1 u2))

noncomputable instance {M1 M2 : Type} [UnitDependent M1] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => f (scaleUnit u2 u1 m1)
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]

noncomputable instance instUnitDependentTwoSided
    {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]

noncomputable instance instUnitDependentTwoSidedMul
    {M1 M2 : Type} [UnitDependent M1] [MulAction ℝ≥0 M2] [MulUnitDependent M2] :
    MulUnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]
  scaleUnit_mul u1 u2 r f := by
    funext m1
    simp [MulUnitDependent.scaleUnit_mul]

open LinearUnitDependent ContinuousLinearUnitDependent in
noncomputable instance instContinuousLinearUnitDependentMap
    {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1] [ContinuousLinearUnitDependent M1]
    [AddCommGroup M2] [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  scaleUnit u1 u2 f :=
    ContinuousLinearEquiv.arrowCongr (scaleUnitContLinearEquiv u1 u2)
      (scaleUnitContLinearEquiv u1 u2) f
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    ext m1
    simp [scaleUnit_id]
  scaleUnit_add u1 u2 f1 f2 := by simp
  scaleUnit_smul u1 u2 r f := by simp
  scaleUnit_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((scaleUnitContLinearEquiv u1 u2).arrowCongr (scaleUnitContLinearEquiv u1 u2))

/-!

### IsDimensionallyInvariant

-/

/-- A term of type `M` carrying an instance of `UnitDependent M` is said to be
  dimensionally invariant if under a change of units it remains the same.

  This corresponds to the statement that term is dimensionally correct.

-/
def IsDimensionallyInvariant {M : Type} [UnitDependent M] (m : M) : Prop :=
  ∀ u1 u2 : UnitChoices, scaleUnit u1 u2 m = m

lemma isDimensionallyInvariant_iff {M : Type} [UnitDependent M] (m : M) :
    IsDimensionallyInvariant m ↔ ∀ u1 u2 : UnitChoices,
      scaleUnit u1 u2 m = m := by rfl

/-!

## Some type classes to help track dimensions

-/

/-- The multiplication of an element of `M1` with an element of `M2` to get an element
  of `M3` in such a way that dimensions are preserved. -/
class DMul (M1 M2 M3 : Type) [CarriesDimension M1] [CarriesDimension M2] [CarriesDimension M3]
    extends HMul M1 M2 M3 where
  mul_dim : ∀ (m1 : Dimensionful M1) (m2 : Dimensionful M2),
    HasDimension (fun u => hMul (m1.1 u) (m2.1 u))

@[simp]
lemma DMul.hMul_scaleUnit {M1 M2 M3 : Type} [CarriesDimension M1] [CarriesDimension M2]
    [CarriesDimension M3]
    [DMul M1 M2 M3] (m1 : M1) (m2 : M2) (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 m1) * (scaleUnit u1 u2 m2) =
    scaleUnit u1 u2 (m1 * m2) := by
  simp [scaleUnit, toDimensionful]
  have h1 := DMul.mul_dim (M3 := M3) (toDimensionful u1 m1) (toDimensionful u1 m2) u2 u1
  simp [toDimensionful_apply_apply] at h1
  conv_rhs =>
    rw [h1]
    rw [smul_smul]
    simp

/-!

## Dim Subtype

-/

/-- Given a type `M` that depends on units, e.g. the function type `M1 → M2` between two types
  carrying a dimension, the subtype of `M` which scales according to the dimension `d`. -/
def DimSet (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) :
    Set M :=
  { m : M | ∀ u1 u2, scaleUnit u1 u2 m = (UnitChoices.dimScale u1 u2 d) • m }

instance (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) :
    MulAction ℝ≥0 (DimSet M d) where
  smul a f := ⟨a • f.1, fun u1 u2 => by
    rw [smul_comm, ← f.2]
    rw [MulUnitDependent.scaleUnit_mul]⟩
  one_smul f := by
    ext
    change (1 : ℝ≥0) • f.1 = f.1
    simp
  mul_smul a b f := by
    ext
    change (a * b) • f.1 = a • (b • f.1)
    rw [smul_smul]

instance (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) :
    CarriesDimension (DimSet M d) where
  d := d

@[simp]
lemma scaleUnit_dimSet_val {M : Type} [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension)
    (m : DimSet M d) (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 m).1 = scaleUnit u1 u2 m.1 := by
  rw [scaleUnit_apply, m.2]
  rfl
