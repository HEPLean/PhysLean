/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.Relativity.SpeedOfLight
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
/-!
# Spacetime

## i. Overview

In this file we define the type `SpaceTime d` which corresponds to `d+1` dimensional
spacetime. This is equipped with an instance of the action of a Lorentz group,
corresponding to Minkowski-spacetime.

It is defined through `Lorentz.Vector d`, and carries the tensorial instance,
allowing it to be used in tensorial expressions.

## ii. Key results

- `SpaceTime d` : The type corresponding to `d+1` dimensional spacetime.
- `toTimeAndSpace` : A continuous linear equivalence between `SpaceTime d`
  and `Time × Space d`.

## iii. Table of contents

- A. The definition of `SpaceTime d`
- B. Maps to and from `Space` and `Time`
  - B.1. Linear map to `Space d`
    - B.1.1. Explicit expansion of map to space
    - B.1.2. Equivariance of the to space under rotations
  - B.2. Linear map to `Time`
    - B.2.1. Explicit expansion of map to time in terms of coordinates
  - B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`
    - B.3.1. Derivative of `toTimeAndSpace`
    - B.3.2. Derivative of the inverse of `toTimeAndSpace`
    - B.3.3. `toTimeAndSpace` acting on spatial basis vectors
    - B.3.4. `toTimeAndSpace` acting on the temporal basis vectors
- C. Continuous linear map to coordinates
- D. Measures on `SpaceTime d`
  - D.1. Instance of a measurable space
  - D.2. Instance of a borel space
  - D.4. Instance of a measure space
  - D.5. Volume measure is positive on non-empty open sets
  - D.6. Volume measure is a finite measure on compact sets
  - D.7. Volume measure is an additive Haar measure

## iv. References

-/

noncomputable section

/-!

## A. The definition of `SpaceTime d`

-/

TODO "6V2DR" "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- `SpaceTime d` corresponds to `d+1` dimensional space-time.
  This is equipped with an instance of the action of a Lorentz group,
  corresponding to Minkowski-spacetime. -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## B. Maps to and from `Space` and `Time`

-/

/-!

### B.1. Linear map to `Space d`

-/

/-- The space part of spacetime. -/
def space {d : ℕ} : SpaceTime d →L[ℝ] Space d where
  toFun x := Lorentz.Vector.spatialPart x
  map_add' x1 x2 := by
    ext i
    simp [Lorentz.Vector.spatialPart]
  map_smul' c x := by
    ext i
    simp [Lorentz.Vector.spatialPart]
  cont := by
    fun_prop

/-!

#### B.1.1. Explicit expansion of map to space

-/

lemma space_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    space f = fun i => f (Sum.inr i) := by
  funext i
  simp [space, Lorentz.Vector.spatialPart]

/-!

#### B.1.2. Equivariance of the to space under rotations

-/

open realLorentzTensor
open Tensor

/-- The function `space` is equivariant with respect to rotations. -/
informal_lemma space_equivariant where
  deps := [``space]
  tag := "7MTYX"

/-!

### B.2. Linear map to `Time`

-/

/-- The time part of spacetime. -/
def time {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x / c⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind

/-!

#### B.2.1. Explicit expansion of map to time in terms of coordinates

-/

@[simp]
lemma time_val_toCoord_symm {d : ℕ} (c : SpeedOfLight) (f : Fin 1 ⊕ Fin d → ℝ) :
    (time c f).val = f (Sum.inl 0) / c := by
  simp [time, Lorentz.Vector.timeComponent]

/-!

### B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`

-/

/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time c, x.space)
    invFun tx := (fun i =>
      match i with
      | Sum.inl _ => c * tx.1.val
      | Sum.inr i => tx.2 i)
    left_inv x := by
      simp only [time, LinearMap.coe_mk, AddHom.coe_mk, space]
      funext i
      match i with
      | Sum.inl 0 =>
        simp [Lorentz.Vector.timeComponent]
        field_simp
      | Sum.inr i => simp [Lorentz.Vector.spatialPart]
    right_inv tx := by
      simp only [time, Lorentz.Vector.timeComponent, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        ne_eq, SpeedOfLight.val_ne_zero, not_false_eq_true, mul_div_cancel_left₀, space,
        ContinuousLinearMap.coe_mk']
    map_add' x y := by
      simp only [space_toCoord_symm, Lorentz.Vector.apply_add, Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext
        simp
      funext i
      simp
    map_smul' := by
      simp
  }

@[simp]
lemma toTimeAndSpace_symm_apply_time_space {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    (toTimeAndSpace c).symm (x.time c, x.space) = x := by
  apply (toTimeAndSpace c).left_inv

@[simp]
lemma space_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).space = s := by
  simp only [space, toTimeAndSpace]
  funext i
  simp

@[simp]
lemma time_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).time c = t := by
  simp only [time, toTimeAndSpace]
  ext
  simp

@[simp]
lemma toTimeAndSpace_symm_apply_inl {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    (toTimeAndSpace c).symm (t, s) (Sum.inl 0) = c * t := by rfl

@[simp]
lemma toTimeAndSpace_symm_apply_inr {d : ℕ} {c : SpeedOfLight} (t : Time) (x : Space d)
    (i : Fin d) :
    (toTimeAndSpace c).symm (t, x) (Sum.inr i) = x i := by rfl
/-!

#### B.3.1. Derivative of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_fderiv {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    fderiv ℝ (toTimeAndSpace c) x = (toTimeAndSpace c).toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.2. Derivative of the inverse of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} {c : SpeedOfLight} (x : Time × Space d) :
    fderiv ℝ (toTimeAndSpace c).symm x = (toTimeAndSpace c).symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.3. `toTimeAndSpace` acting on spatial basis vectors

-/
lemma toTimeAndSpace_basis_inr {d : ℕ} {c : SpeedOfLight} (i : Fin d) :
    toTimeAndSpace c (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inr]
  constructor
  · simp
  funext j
  simp [Space.basis_apply, space]

/-!

#### B.3.4. `toTimeAndSpace` acting on the temporal basis vectors

-/

lemma toTimeAndSpace_basis_inl {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (⟨1/c.val⟩, 0) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inl]
  constructor
  · simp
  funext j
  simp [space]

lemma toTimeAndSpace_basis_inl' {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (1/c.val) • (1, 0) := by
  rw [toTimeAndSpace_basis_inl]
  simp only [one_div, Prod.smul_mk, smul_zero, Prod.mk.injEq, and_true]
  congr
  simp

/-!

## C. Continuous linear map to coordinates

-/

/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun x := x (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp

@[inherit_doc coord]
scoped notation "𝔁" => coord

lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl

/-- The continuous linear map from a point in space time to one of its coordinates. -/
def coordCLM (μ : Fin 1 ⊕ Fin d) : SpaceTime d →L[ℝ] ℝ where
  toFun x := x μ
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp
  cont := by
    fun_prop

/-!

## D. Measures on `SpaceTime d`

-/
open MeasureTheory

/-!

### D.1. Instance of a measurable space

-/

instance {d : ℕ} : MeasurableSpace (SpaceTime d) := borel (SpaceTime d)

/-!

### D.2. Instance of a borel space

-/

instance {d : ℕ} : BorelSpace (SpaceTime d) where
  measurable_eq := by rfl

/-!

### D.4. Instance of a measure space

-/

instance {d : ℕ} : MeasureSpace (SpaceTime d) where
  volume := Lorentz.Vector.basis.addHaar

/-!

### D.5. Volume measure is positive on non-empty open sets

-/

instance {d : ℕ} : (volume (α := SpaceTime d)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)

/-!

### D.6. Volume measure is a finite measure on compact sets

-/

instance {d : ℕ} : IsFiniteMeasureOnCompacts (volume (α := SpaceTime d)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))

/-!

### D.7. Volume measure is an additive Haar measure

-/

instance {d : ℕ} : Measure.IsAddHaarMeasure (volume (α := SpaceTime d)) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Lorentz.Vector.basis.addHaar))

end SpaceTime

end
