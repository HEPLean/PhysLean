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
      simp only [time, LinearMap.coe_mk, AddHom.coe_mk, space]
      funext i
      match i with
      | Sum.inl 0 => simp [Lorentz.Vector.timeComponent]
      | Sum.inr i => simp [Lorentz.Vector.spatialPart]
    right_inv tx := by
      simp only [time, Lorentz.Vector.timeComponent, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        space]
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
lemma toTimeAndSpace_fderiv {d : ℕ} (x : SpaceTime d) :
    fderiv ℝ toTimeAndSpace x = toTimeAndSpace.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} (x : Time × Space d) :
    fderiv ℝ toTimeAndSpace.symm x = toTimeAndSpace.symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

lemma toTimeAndSpace_basis_inr {d : ℕ} (i : Fin d) :
    toTimeAndSpace (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inr]
  constructor
  · simp
  funext j
  simp [Space.basis_apply]

lemma toTimeAndSpace_basis_inl {d : ℕ} :
    toTimeAndSpace (d := d) (Lorentz.Vector.basis (Sum.inl 0)) = (1, 0) := by
  simp only [toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_sum_inl]
  constructor
  · simp
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
    simp
  map_smul' c x := by
    simp

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
    ∂_ μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

attribute [-simp] Fintype.sum_sum_type

lemma deriv_comp_lorentz_action {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} (μ : Fin 1 ⊕ Fin d)
    (f : SpaceTime d → M) (hf : Differentiable ℝ f) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∂_ μ (fun x => f (Λ • x)) x = ∑ ν, Λ.1 ν μ • ∂_ ν f (Λ • x) := by
  change fderiv ℝ (f ∘ Lorentz.Vector.actionCLM Λ ) x (Lorentz.Vector.basis μ)   = _
  rw [fderiv_comp]
  simp only [Lorentz.Vector.actionCLM_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
    -- Fintype.sum_sum_type
  rw [Lorentz.Vector.smul_basis]
  simp
  rfl
  · fun_prop
  · fun_prop

/-!

## Derivatives

-/

lemma deriv_sum_inr {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) (i : Fin d) :
    ∂_ (Sum.inr i) f x
    = Space.deriv i (fun y => f (toTimeAndSpace.symm ((toTimeAndSpace x).1, y)))
      (toTimeAndSpace x).2 := by
  rw [deriv_eq, Space.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp
  congr 1
  rw [fderiv_comp']
  simp
  change _ = toTimeAndSpace.symm ((fderiv ℝ ((toTimeAndSpace x).1, ·) (toTimeAndSpace x).2) (EuclideanSpace.single i 1))
  rw [DifferentiableAt.fderiv_prodMk]
  simp
  trans toTimeAndSpace.symm (0, Space.basis i)
  · rw [← toTimeAndSpace_basis_inr]
    simp
  · congr
    rw [Space.basis]
    simp
  repeat' fun_prop

lemma deriv_sum_inl {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) :
    ∂_ (Sum.inl 0) f x
    = Time.deriv (fun t => f (toTimeAndSpace.symm (t, (toTimeAndSpace x).2))) (toTimeAndSpace x).1 := by
  rw [deriv_eq, Time.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp
  congr 1
  rw [fderiv_comp']
  simp
  rw [DifferentiableAt.fderiv_prodMk]
  simp
  rw [← toTimeAndSpace_basis_inl]
  simp
  repeat' fun_prop

/-!

## Measure space on SpaceTime

-/
open MeasureTheory

instance : MeasurableSpace SpaceTime := borel SpaceTime

instance : BorelSpace SpaceTime where
  measurable_eq := by rfl

def innerProductSpace (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) :=
  inferInstanceAs (InnerProductSpace ℝ (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

instance : MeasureSpace SpaceTime where
  volume := Lorentz.Vector.basis.addHaar

instance : (volume (α := SpaceTime)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)

instance : IsFiniteMeasureOnCompacts (volume (α := SpaceTime)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))

end SpaceTime

end
