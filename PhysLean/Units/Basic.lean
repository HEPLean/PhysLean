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
lemma dimScale_mul_symm (u1 u2 : UnitChoices) (d : Dimension)  :
    dimScale u1 u2 d * dimScale u2 u1 d = 1 := by
  rw [dimScale_transitive, dimScale_self]

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

## Types carrying dimensions

Dimensions are assigned to types with the following type-classes

- `CarriesDimension` for a type carrying an instance of `MulAction ℝ≥0 M`
- `ModuleCarriesDimension` for a type carrying an instance of `Module ℝ M`.

The latter is need to prevent a typeclass dimond.


-/

class CarriesDimension (M : Type) extends MulAction ℝ≥0 M where
  d : Dimension

-- prevents a typeclass diamond
class ModuleCarriesDimension (M : Type) [AddCommMonoid M] [Module ℝ M] where
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
lemma Dimensionful.smul_apply  {M : Type} [CarriesDimension M]
    (a : ℝ≥0) (f : Dimensionful M) (u : UnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

/-- For `M` carying a dimension `d`, the equivalence between `M` and  `Dimension M`,
  given a choice of units. -/
noncomputable def CarriesDimension.toDimensionful {M : Type} [CarriesDimension M] (u : UnitChoices) :
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
    simp
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
- `UnitDependent M` having a function `changeUnits : UnitChoices → M → UnitChoices → M`
  subject to two conditions `changeUnits_trans` and `changeUnits_id`
- `LinearUnitDependent M` extends `UnitDependent M` with additional linearity conditions
  on `changeUnits`.
- `ContinuousLinearUnitDependent M` extends `LinearUnitDependent M` with an additional
  continuity condition on `changeUnits`.

-/

open CarriesDimension

class UnitDependent (M : Type) where
  changeUnits : UnitChoices → M → UnitChoices → M
  changeUnits_trans : ∀ u1 u2 u3 m, changeUnits u2 (changeUnits u1 m u2) u3 = changeUnits u1 m u3
  changeUnits_trans' : ∀ u1 u2 u3 m, changeUnits u1 (changeUnits u2 m u3) u2 = changeUnits u1 m u3
  changeUnits_id : ∀ u m, changeUnits u m u = m

class LinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M] extends
    UnitDependent M where
  changeUnits_add : ∀ u1 u2 m1 m2,
    changeUnits u1 (m1 + m2) u2 = changeUnits u1 m1 u2 + changeUnits u1 m2 u2
  changeUnits_smul : ∀ u1 u2 (r : ℝ) m,
    changeUnits u1 (r • m) u2 = r • changeUnits u1 m u2

class ContinuousLinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] extends LinearUnitDependent M where
  changeUnits_cont : ∀ u1 u2, Continuous (fun m => changeUnits u1 m u2)


/-!

## Basic properties of changeUnits

-/



@[simp]
lemma UnitDependent.changeUnits_symm_apply {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    changeUnits u2 (changeUnits u1 m u2) u1 = m := by
  rw [changeUnits_trans, changeUnits_id]

@[simp]
lemma UnitDependent.changeUnits_injective {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m1 m2 : M) :
    changeUnits u1 m1 u2 = changeUnits u1 m2 u2 ↔ m1 = m2 := by
  constructor
  · intro h1
    have h2 : changeUnits u2 (changeUnits u1 m1 u2) u1 =
        changeUnits u2 (changeUnits u1 m2 u2 ) u1 := by rw [h1]
    simpa using h2
  · intro h
    subst h
    rfl

/-!

### Variations on the map changeUnits

-/

open UnitDependent
def UnitDependent.changeUnitsEquiv {M : Type} [AddCommMonoid M] [Module ℝ M] [LinearUnitDependent M]
    (u1 u2 : UnitChoices) : M ≃ M where
  toFun m := UnitDependent.changeUnits u1 m u2
  invFun m := UnitDependent.changeUnits u2 m u1
  right_inv m := by simp
  left_inv m := by simp

def LinearUnitDependent.changeUnitsLinear
    {M : Type} [AddCommMonoid M] [Module ℝ M] [LinearUnitDependent M]
    (u1 u2 : UnitChoices) :
    M →ₗ[ℝ] M where
  toFun m := UnitDependent.changeUnits u1 m u2
  map_add' m1 m2 := by simp [LinearUnitDependent.changeUnits_add]
  map_smul' r m2 := by simp [LinearUnitDependent.changeUnits_smul]

def LinearUnitDependent.changeUnitsLinearEquiv {M : Type} [AddCommMonoid M] [Module ℝ M] [LinearUnitDependent M]
    (u1 u2 : UnitChoices) :
    M ≃ₗ[ℝ] M :=
    LinearEquiv.ofLinear (changeUnitsLinear u1 u2) (changeUnitsLinear u2 u1)
    (by ext u; simp [changeUnitsLinear])
    (by ext u; simp [changeUnitsLinear])

def ContinuousLinearUnitDependent.changeUnitsContLinear  {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M →L[ℝ] M where
  toLinearMap := LinearUnitDependent.changeUnitsLinear u1 u2
  cont :=  ContinuousLinearUnitDependent.changeUnits_cont u1 u2

def ContinuousLinearUnitDependent.changeUnitsContLinearEquiv {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M ≃L[ℝ] M :=
    ContinuousLinearEquiv.mk  (LinearUnitDependent.changeUnitsLinearEquiv u1 u2)
    (ContinuousLinearUnitDependent.changeUnits_cont u1 u2)
    (ContinuousLinearUnitDependent.changeUnits_cont u2 u1)

@[simp]
lemma ContinuousLinearUnitDependent.changeUnitsContLinearEquiv_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.changeUnitsContLinearEquiv u1 u2) m =
      UnitDependent.changeUnits u1 m u2 := rfl

@[simp]
lemma ContinuousLinearUnitDependent.changeUnitsContLinearEquiv_symm_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.changeUnitsContLinearEquiv u1 u2).symm m =
      UnitDependent.changeUnits u2 m u1 := rfl
/-!

### Instances of the type classes

We construct instance of the `UnitDependent`, `LinearUnitDependent` and
  `ContinuousLinearUnitDependent` type classes based on `CarriesDimension`
  and functions.

-/

open UnitDependent

noncomputable instance {M1 : Type} [CarriesDimension M1] : UnitDependent M1 where
  changeUnits u1 m u2 := (toDimensionful u1 m).1 u2
  changeUnits_trans u1 u2 u3 m := by
    simp [toDimensionful]
    rw [smul_smul, mul_comm, UnitChoices.dimScale_transitive]
  changeUnits_trans' u1 u2 u3 m := by
    simp [toDimensionful, smul_smul, UnitChoices.dimScale_transitive]
  changeUnits_id u m := by
    simp [toDimensionful, UnitChoices.dimScale_self]

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M]
    [ModuleCarriesDimension M] : LinearUnitDependent M where
  changeUnits_add u1 u2 m1 m2 := by
    change (toDimensionful u1 (m1 + m2)).1 u2 = _
    rw [toDimensionful_apply_apply]
    simp
    rfl
  changeUnits_smul u1 u2 r m := by
    change (toDimensionful u1 (r • m)).1 u2 = _
    rw [toDimensionful_apply_apply]
    rw [smul_comm]
    rfl

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M]
    [ModuleCarriesDimension M] [TopologicalSpace M]
    [ContinuousConstSMul ℝ M] : ContinuousLinearUnitDependent M where
  changeUnits_cont u1 u2 := by
    change Continuous fun m => (toDimensionful u1 m).1 u2
    conv =>
      enter [1, m]
      rw [toDimensionful_apply_apply]
    change Continuous fun m => (u1.dimScale u2 (d M)).1 • m
    apply Continuous.const_smul
    exact continuous_id'

noncomputable instance {M1 M2 : Type} [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  changeUnits u1 f u2 := fun m1 => changeUnits u1 (f m1) u2
  changeUnits_trans u1 u2 u3 f := by
    funext m1
    exact changeUnits_trans u1 u2 u3 (f m1)
  changeUnits_trans' u1 u2 u3 f := by
    funext m1
    exact changeUnits_trans' u1 u2 u3 (f m1)
  changeUnits_id u f := by
    funext m1
    exact changeUnits_id u (f m1)

open LinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommMonoid M1] [Module ℝ M1]
    [AddCommMonoid M2] [Module ℝ M2] [LinearUnitDependent M2] :
    LinearUnitDependent (M1 →ₗ[ℝ] M2) where
  changeUnits u1 f u2 := {
      toFun m1 := changeUnits u1 (f m1) u2
      map_add' m1 m2 := by simp [changeUnits_add]
      map_smul' := by simp [changeUnits_smul]}
  changeUnits_trans u1 u2 u3 f := by
    ext m1
    exact changeUnits_trans u1 u2 u3 (f m1)
  changeUnits_trans' u1 u2 u3 f := by
    ext m1
    exact changeUnits_trans' u1 u2 u3 (f m1)
  changeUnits_id u f := by
    ext m1
    exact changeUnits_id u (f m1)
  changeUnits_add u1 u2 f1 f2 := by
    ext m
    simp [changeUnits_add]
  changeUnits_smul u1 u2 r f := by
    ext m
    simp [changeUnits_smul]

open LinearUnitDependent  ContinuousLinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1]
    [AddCommGroup M2]  [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  changeUnits u1 f u2 :=
    ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl  ℝ _)
      (changeUnitsContLinearEquiv u1 u2) f
  changeUnits_trans u1 u2 u3 f := by
    ext m1
    exact changeUnits_trans u1 u2 u3 (f m1)
  changeUnits_trans' u1 u2 u3 f := by
    ext m1
    exact changeUnits_trans' u1 u2 u3 (f m1)
  changeUnits_id u f := by
    ext m1
    exact changeUnits_id u (f m1)
  changeUnits_add u1 u2 f1 f2 := by simp
  changeUnits_smul u1 u2 r f := by simp
  changeUnits_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((ContinuousLinearEquiv.refl ℝ M1).arrowCongr (changeUnitsContLinearEquiv u1 u2))

noncomputable instance {M1 M2 : Type} [UnitDependent M1] :
    UnitDependent (M1 → M2) where
  changeUnits u1 f u2 := fun m1 => f (changeUnits u2 m1 u1)
  changeUnits_trans u1 u2 u3 f := by
    funext m1
    simp [changeUnits_trans]
  changeUnits_trans' u1 u2 u3 f := by
    funext m1
    simp [changeUnits_trans']
  changeUnits_id u f := by
    funext m1
    simp [changeUnits_id]

noncomputable instance instUnitDependentTwoSided
    {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  changeUnits u1 f u2 := fun m1 => changeUnits u1 (f (changeUnits u2 m1 u1)) u2
  changeUnits_trans u1 u2 u3 f := by
    funext m1
    simp [changeUnits_trans]
  changeUnits_trans' u1 u2 u3 f := by
    funext m1
    simp [changeUnits_trans']
  changeUnits_id u f := by
    funext m1
    simp [changeUnits_id]

open LinearUnitDependent  ContinuousLinearUnitDependent in
noncomputable instance instContinuousLinearUnitDependentMap
    {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1] [ContinuousLinearUnitDependent M1]
    [AddCommGroup M2]  [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  changeUnits u1 f u2 :=
    ContinuousLinearEquiv.arrowCongr (changeUnitsContLinearEquiv u1 u2)
      (changeUnitsContLinearEquiv u1 u2) f
  changeUnits_trans u1 u2 u3 f := by
    ext m1
    simp [changeUnits_trans]
  changeUnits_trans' u1 u2 u3 f := by
    ext m1
    simp [changeUnits_trans']
  changeUnits_id u f := by
    ext m1
    simp [changeUnits_id]
  changeUnits_add u1 u2 f1 f2 := by simp
  changeUnits_smul u1 u2 r f := by simp
  changeUnits_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((changeUnitsContLinearEquiv u1 u2).arrowCongr (changeUnitsContLinearEquiv u1 u2))

/-!

### IsDimensionallyInvariant

-/

/-- A term of type `M` carrying an instance of `UnitDependent M` is said to be
  dimensionally invariant if under a change of units it remains the same.

  This corresponds to the statement that term is dimensionally correct.

-/
def IsDimensionallyInvariant {M : Type} [UnitDependent M] (m : M) : Prop :=
  ∀ u1 u2 : UnitChoices, UnitDependent.changeUnits u1 m u2 = m

lemma isDimensionallyInvariant_iff {M : Type} [UnitDependent M] (m : M) :
    IsDimensionallyInvariant m ↔ ∀ u1 u2 : UnitChoices,
      UnitDependent.changeUnits u1 m u2 = m := by rfl

open ContinuousLinearUnitDependent in
/-- If a function is dimensionally valid then so is it's derivative. -/
lemma fderiv_isDimensionallyInvariant  {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
    [ContinuousConstSMul ℝ M1] [ModuleCarriesDimension M1]
    [NormedAddCommGroup M2]  [NormedSpace ℝ M2]
    [SMulCommClass ℝ ℝ M2]  [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ModuleCarriesDimension M2]
    (f : M1 → M2) (hf : IsDimensionallyInvariant f) (f_diff : Differentiable ℝ f) :
    IsDimensionallyInvariant (fderiv ℝ f) := by
  rw [isDimensionallyInvariant_iff]
  intro u1 u2
  replace hf := hf u2 u1
  ext m m'
  simp [instUnitDependentTwoSided, instContinuousLinearUnitDependentMap]
  change (toDimensionful u1 ((fderiv ℝ f ((toDimensionful u2 m).1 u1))
      ((toDimensionful u2 m').1 u1))).1 u2 = (fderiv ℝ f m) m'
  simp [toDimensionful_apply_apply]
  conv_lhs =>
    rw [← hf]
    simp [instUnitDependentTwoSided]
    enter [2, 2, 1, 2, mx]
    change (toDimensionful u2 (f ((toDimensionful u1 mx).1 u2))).1 u1
    simp [toDimensionful_apply_apply]
    change (u2.dimScale u1 (d M2)).1 • f ((u1.dimScale u2 (d M1)).1 • mx)
  have h1 :  (fderiv ℝ (fun mx => (u2.dimScale u1 (d M2)).1 • f
      ((u1.dimScale u2 (d M1)).1 • mx)) ((u2.dimScale u1 (d M1)).1 • m))
     = u2.dimScale u1 (d M2) • u1.dimScale u2 (d M1) • (fderiv ℝ f m) := by
    change (fderiv ℝ ((u2.dimScale u1 (d M2)).1 • fun mx =>  f
      ((u1.dimScale u2 (d M1)).1 • mx)) ((u2.dimScale u1 (d M1)).1 • m))  = _
    rw [fderiv_const_smul (by fun_prop)]
    rw [fderiv_comp_smul]
    simp
    congr
    rw [smul_smul]
    change ((u1.dimScale u2 (d M1)) * (u2.dimScale u1 (d M1))) • m = m
    simp
  erw [h1]
  simp [smul_smul]
  trans (1 : ℝ≥0) • (fderiv ℝ f m) m'
  · congr
    trans  (u1.dimScale u2 (d M2) * u2.dimScale u1 (d M2) )
      * (u2.dimScale u1 (d M1) *  u1.dimScale u2 (d M1))
    · ring
    simp
  simp

/-!

## Some type classes to help track dimensions

-/


class DMul (M1 M2 M3 : Type) [CarriesDimension M1] [CarriesDimension M2] [CarriesDimension M3]
    extends HMul M1 M2 M3 where
  mul_dim : ∀ (m1  : Dimensionful M1) (m2 : Dimensionful M2),
    HasDimension (fun u => hMul (m1.1 u) (m2.1 u))

@[simp]
lemma DMul.hMul_changeUnits {M1 M2 M3 : Type} [CarriesDimension M1] [CarriesDimension M2]
    [CarriesDimension M3]
    [DMul M1 M2 M3] (m1 : M1) (m2 : M2) (u1 u2 : UnitChoices) :
    (changeUnits u1 m1 u2) * (changeUnits u1 m2 u2) =
    changeUnits u1 (m1 * m2) u2 := by
  simp [UnitDependent.changeUnits, toDimensionful]
  have h1 := DMul.mul_dim (M3 := M3) (toDimensionful u1 m1) (toDimensionful u1 m2) u2 u1
  simp [toDimensionful_apply_apply] at h1
  conv_rhs =>
    rw [h1]
    rw [smul_smul]
    simp
