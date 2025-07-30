/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Units on Temperature

A unit of temperature corresponds to a choice of translationally-invariant
metric on the temperature manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `TemperatureUnit` to be equivalent to the
positive reals.

On `TemperatureUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific temperature units, we first axiomise the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to axiomise the
existence of the temperature unit of kelvin, and construct all other temperature units from that.

-/

/-- The choices of translationally-invariant metrics on the temperature-manifold.
  Such a choice corresponds to a choice of units for temperature. -/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

namespace TemperatureUnit

@[simp]
lemma val_neq_zero (x : TemperatureUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)

lemma val_pos (x : TemperatureUnit) : 0 < x.val := x.property

instance : Inhabited TemperatureUnit where
  default := ⟨1, by norm_num⟩

/-!

## Division of TemperatureUnit

-/

noncomputable instance : HDiv TemperatureUnit TemperatureUnit ℝ where
  hDiv x t := x.val / t.val

lemma div_eq_val (x y : TemperatureUnit) :
    x / y = x.val / y.val := rfl

@[simp]
lemma div_pos (x y : TemperatureUnit) :
    (0 : ℝ) < x / y := by
  simpa [div_eq_val] using _root_.div_pos x.val_pos y.val_pos

@[simp]
lemma div_self (x : TemperatureUnit) :
    x / x = (1 : ℝ) := by
  simp [div_eq_val, x.val_neq_zero]

lemma div_symm (x y : TemperatureUnit) :
    x / y = (y / x)⁻¹ := by
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  simp

/-!

## The scaling of a temperature unit

-/

/-- The scaling of a temperature unit by a positive real. -/
def scale (r : ℝ) (x : TemperatureUnit) (hr : 0 < r := by norm_num) : TemperatureUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (x : TemperatureUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = r := by
  simp [scale, div_eq_val]

@[simp]
lemma scale_one (x : TemperatureUnit) : scale 1 x = x := by
  simp [scale, mul_one]

@[simp]
lemma scale_div_scale (x1 x2 : TemperatureUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = r1 / r2 * (x1 / x2) := by
  simp [scale, div_eq_val]
  field_simp

@[simp]
lemma scale_scale (x : TemperatureUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring

/-!

## Specific choices of temperature units

To define a specific temperature units, we must first axiomise the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to axiomise the existence of the temperature unit of kelvin.

We need an axiom since this relates something to something in the physical world.

-/

/-- The axiom corresponding to the definition of a temperature unit of kelvin. -/
axiom kelvin : TemperatureUnit

/-- The temperature unit of degrees nanokelvin (10^(-9) kelvin). -/
noncomputable def nanokelvin : TemperatureUnit := scale (1e-9) kelvin


/-- The temperature unit of degrees microkelvin (10^(-6) kelvin). -/
noncomputable def microkelvin : TemperatureUnit := scale (1e-6) kelvin

/-- The temperature unit of degrees millikelvin (10^(-3) kelvin). -/
noncomputable def millikelvin : TemperatureUnit := scale (1e-3) kelvin

/-- The temperature unit of degrees fahrenheit ((5/9) of a kelvin).
  Note, this is fahrenheit starting at `0` absolute temperature.  -/
noncomputable def absoluteFahrenheit : TemperatureUnit := scale (5 / 9) kelvin

end TemperatureUnit
