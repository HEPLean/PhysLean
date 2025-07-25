/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

noncomputable section

TODO "6V2DR" "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- `SpaceTime d` corresponds to `d+1` dimensional space-time.
  This is equipped with an instaance of the action of a Lorentz group,
  corresponding to Minkowski-spacetime. -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## To space and time

-/

/-- The space part of spacetime. -/
def space {d : ℕ} : SpaceTime d →ₗ[ℝ] Space d where
  toFun x := Lorentz.Vector.spatialPart x
  map_add' x1 x2 := by
    ext i
    simp [Lorentz.Vector.spatialPart]
  map_smul' c x := by
    ext i
    simp [Lorentz.Vector.spatialPart]

@[simp]
lemma space_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    space f = fun i => f (Sum.inr i) := by
  funext i
  simp [space, Lorentz.Vector.spatialPart]

open realLorentzTensor
open Tensor

/-- The function `space` is equivariant with respect to rotations. -/
informal_lemma space_equivariant where
  deps := [``space]
  tag := "7MTYX"

/-- The time part of spacetime. -/
def time {d : ℕ} : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]

@[simp]
lemma time_val_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    (time f).val = f (Sum.inl 0) := by
  simp [time, Lorentz.Vector.timeComponent]

/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time, x.space)
    invFun tx := (fun i =>
      match i with
      | Sum.inl _ => tx.1.val
      | Sum.inr i => tx.2 i)
    left_inv x := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, time, LinearMap.coe_mk,
        AddHom.coe_mk, space, EmbeddingLike.apply_eq_iff_eq]
      funext i
      match i with
      | Sum.inl 0 => simp [Lorentz.Vector.timeComponent]
      | Sum.inr i => simp [Lorentz.Vector.spatialPart]
    right_inv tx := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, time, Lorentz.Vector.timeComponent,
        Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply, space]
    map_add' x y := by
      simp only [time_val_toCoord_symm, Fin.isValue, Lorentz.Vector.apply_add, space_toCoord_symm,
        Prod.mk_add_mk, Prod.mk.injEq, true_and]
      constructor
      · ext
        simp
      funext i
      simp
    map_smul' := by
      simp
  }

lemma toTimeAndSpace_basis_inr {d : ℕ} (i : Fin d) :
    toTimeAndSpace (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inr]
  constructor
  · rfl
  funext j
  simp [Space.basis_apply]

lemma toTimeAndSpace_basis_inl {d : ℕ} :
    toTimeAndSpace (d := d) (Lorentz.Vector.basis (Sum.inl 0)) = (1, 0) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inl]
  constructor
  · rfl
  funext j
  simp [space]

/-!

## Coordinates

-/

/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun x := x (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp [flip]
  map_smul' c x := by
    simp [flip]

@[inherit_doc coord]
scoped notation "𝔁" => coord

lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl

/-!

## Derivatives

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinte. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)

@[inherit_doc deriv]
scoped notation "∂_" => deriv

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
lemma deriv_eq {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    SpaceTime.deriv μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

end SpaceTime

end
