/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.SpaceAndTime.Space.Distributions.Basic
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
- `deriv` : The derivative of a function `SpaceTime d → M` along the `μ` coordinte.
- `deriv_sum_inr` : The derivative along a spatial coordinate in terms of the
  derivative on `Space d`.
- `deriv_sum_inl` : The derivative along the temporal coordinate in terms of the
  derivative on `Time`.
- `innerProductSpace` : The Euclidean inner product structure on `SpaceTime d`.

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
    - B.3.4. `toTimeAndSpace` acting on the temperal basis vectors
- C. Continous linear map to coordinates
- D. Derivatives of functions on `SpaceTime d`
  - D.1. The definition of the derivative
  - D.2. Basic equality lemmas
  - D.3. Derivative of the zero function
  - D.4. The derivative of a function composed with a Lorentz transformation
  - D.5. Spacetime derivatives in terms of time and space derivatives
- E. Measures on `SpaceTime d`
  - E.1. Instance of a measureable space
  - E.2. Instance of a borel space
  - E.3. Definition of an inner product space structure on `SpaceTime d`
  - E.4. Instance of a measure space
  - E.5. Volume measure is positive on non-empty open sets
  - E.6. Volume measure is a finite measure on compact sets
  - E.7. Volume measure is an additive Haar measure

## iv. References

-/

noncomputable section

/-!

## A. The definition of `SpaceTime d`

-/

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

@[simp]
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
def time {d : ℕ} : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]

/-!

#### B.2.1. Explicit expansion of map to time in terms of coordinates

-/

@[simp]
lemma time_val_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    (time f).val = f (Sum.inl 0) := by
  simp [time, Lorentz.Vector.timeComponent]

/-!

### B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`

-/

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
        space, ContinuousLinearMap.coe_mk']
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

lemma toTimeAndSpace_symm_apply_time_space {d : ℕ} (x : SpaceTime d) :
    toTimeAndSpace.symm (x.time, x.space) = x := by
  apply toTimeAndSpace.left_inv

@[simp]
lemma toTimeAndSpace_symm_apply_time_space' {d : ℕ} (x : SpaceTime d) :
    toTimeAndSpace.symm (x.time, fun i => x (Sum.inr i)) = x := by
  apply toTimeAndSpace.left_inv

/-!

#### B.3.1. Derivative of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_fderiv {d : ℕ} (x : SpaceTime d) :
    fderiv ℝ toTimeAndSpace x = toTimeAndSpace.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.2. Derivative of the inverse of `toTimeAndSpace`

-/

@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} (x : Time × Space d) :
    fderiv ℝ toTimeAndSpace.symm x = toTimeAndSpace.symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]

/-!

#### B.3.3. `toTimeAndSpace` acting on spatial basis vectors

-/
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

/-!

#### B.3.4. `toTimeAndSpace` acting on the temperal basis vectors

-/

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

## C. Continous linear map to coordinates

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

## D. Derivatives of functions on `SpaceTime d`

-/

/-!

### D.1. The definition of the derivative

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinte. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)

@[inherit_doc deriv]
scoped notation "∂_" => deriv

/-!

### D.2. Basic equality lemmas

-/

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
lemma deriv_eq {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    ∂_ μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

lemma deriv_apply_eq {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f)
    (y : SpaceTime d) :
    ∂_ μ f y ν = fderiv ℝ (fun x => f x ν) y (Lorentz.Vector.basis μ) := by
  rw [deriv_eq]
  rw [fderiv_pi]
  rfl
  fun_prop

@[simp]
lemma deriv_coord {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => x ν) = if μ = ν then 1 else 0 := by
  change ∂_ μ (coordCLM ν) = _
  funext x
  rw [deriv_eq]
  simp only [ContinuousLinearMap.fderiv]
  simp [coordCLM]
  split_ifs
  rfl
  rfl

/-!

### D.3. Derivative of the zero function

-/

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

attribute [-simp] Fintype.sum_sum_type

/-!

### D.4. The derivative of a function composed with a Lorentz transformation

-/

lemma deriv_comp_lorentz_action {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d)
    (f : SpaceTime d → M) (hf : Differentiable ℝ f) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∂_ μ (fun x => f (Λ • x)) x = ∑ ν, Λ.1 ν μ • ∂_ ν f (Λ • x) := by
  change fderiv ℝ (f ∘ Lorentz.Vector.actionCLM Λ) x (Lorentz.Vector.basis μ) = _
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

### D.5. Spacetime derivatives in terms of time and space derivatives

-/

lemma deriv_sum_inr {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) (i : Fin d) :
    ∂_ (Sum.inr i) f x
    = Space.deriv i (fun y => f (toTimeAndSpace.symm ((toTimeAndSpace x).1, y)))
      (toTimeAndSpace x).2 := by
  rw [deriv_eq, Space.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  congr 1
  rw [fderiv_comp']
  simp only [Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  change _ = toTimeAndSpace.symm ((fderiv ℝ ((toTimeAndSpace x).1, ·) (toTimeAndSpace x).2)
    (EuclideanSpace.single i 1))
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_fun_const, Pi.zero_apply, fderiv_id', ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  trans toTimeAndSpace.symm (0, Space.basis i)
  · rw [← toTimeAndSpace_basis_inr]
    simp
  · congr
    rw [Space.basis]
    simp
  repeat' fun_prop

lemma deriv_sum_inl {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) :
    ∂_ (Sum.inl 0) f x
    = Time.deriv (fun t => f (toTimeAndSpace.symm (t, (toTimeAndSpace x).2)))
      (toTimeAndSpace x).1 := by
  rw [deriv_eq, Time.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Fin.isValue, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  congr 1
  rw [fderiv_comp']
  simp only [Fin.isValue, Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [Fin.isValue, fderiv_id', fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.zero_apply]
  rw [← toTimeAndSpace_basis_inl]
  simp only [Fin.isValue, ContinuousLinearEquiv.symm_apply_apply]
  repeat' fun_prop

/-!

## E. Measures on `SpaceTime d`

-/
open MeasureTheory

/-!

### E.1. Instance of a measureable space

-/

instance {d : ℕ} : MeasurableSpace (SpaceTime d) := borel (SpaceTime d)

/-!

### E.2. Instance of a borel space

-/

instance {d : ℕ} : BorelSpace (SpaceTime d) where
  measurable_eq := by rfl

/-!

### E.3. Definition of an inner product space structure on `SpaceTime d`

-/

/-- The Euclidean inner product structure on `SpaceTime`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) :=
  inferInstanceAs (InnerProductSpace ℝ (EuclideanSpace ℝ (Fin 1 ⊕ Fin d)))

/-!

### E.4. Instance of a measure space

-/

instance {d : ℕ} : MeasureSpace (SpaceTime d) where
  volume := Lorentz.Vector.basis.addHaar

/-!

### E.5. Volume measure is positive on non-empty open sets

-/

instance {d : ℕ} : (volume (α := SpaceTime d)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)

/-!

### E.6. Volume measure is a finite measure on compact sets

-/

instance {d : ℕ} : IsFiniteMeasureOnCompacts (volume (α := SpaceTime d)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))

/-!

### E.7. Volume measure is an additive Haar measure

-/

instance {d : ℕ} : Measure.IsAddHaarMeasure (volume (α := SpaceTime d)) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Lorentz.Vector.basis.addHaar))


/-!

### E.8. Spacetime integrals in terms of time and space integrals

-/
open MeasureTheory

lemma toTimeAndSpace_symm_measurePreserving {d : ℕ} :
    MeasurePreserving toTimeAndSpace.symm (volume.prod (volume (α := Space d))) volume := by
  have h : volume (α := SpaceTime d)  =  Lorentz.Vector.basis.addHaar := rfl
  refine { measurable := ?_, map_eq := ?_ }
  · fun_prop
  have hs : volume (α := Space d) = Space.basis.toBasis.addHaar := by
    exact Space.volume_eq_addHaar
  have ht : volume (α := Time) = Time.basis.toBasis.addHaar := by
    exact Time.volume_eq_basis_addHaar
  rw [hs, ht]
  rw [← Module.Basis.prod_addHaar]
  rw [Module.Basis.map_addHaar]
  rw [h]
  congr
  ext μ
  match μ with
  | Sum.inl 0 =>
    simp
    apply toTimeAndSpace.injective
    simp
    rw [toTimeAndSpace_basis_inl]
  | Sum.inr i =>
    simp
    apply toTimeAndSpace.injective
    simp
    rw [toTimeAndSpace_basis_inr]

lemma spaceTime_integral_eq_time_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ}
    (f : SpaceTime d → M)  :
    ∫ x : SpaceTime d, f x ∂(volume) =
    ∫ tx : Time × Space d, f (toTimeAndSpace.symm tx) ∂(volume.prod volume) := by
  symm
  apply MeasureTheory.MeasurePreserving.integral_comp
  · have h : volume (α := SpaceTime d)  =  Lorentz.Vector.basis.addHaar := rfl
    refine { measurable := ?_, map_eq := ?_ }
    · fun_prop
    have hs : volume (α := Space d) = Space.basis.toBasis.addHaar := by
      exact Space.volume_eq_addHaar
    have ht : volume (α := Time) = Time.basis.toBasis.addHaar := by
      exact Time.volume_eq_basis_addHaar
    rw [hs, ht]
    rw [← Module.Basis.prod_addHaar]
    rw [Module.Basis.map_addHaar]
    rw [h]
    congr
    ext μ
    match μ with
    | Sum.inl 0 =>
      simp
      apply toTimeAndSpace.injective
      simp
      rw [toTimeAndSpace_basis_inl]
    | Sum.inr i =>
      simp
      apply toTimeAndSpace.injective
      simp
      rw [toTimeAndSpace_basis_inr]


  · refine Measurable.measurableEmbedding ?_ ?_
    · fun_prop
    · exact ContinuousLinearEquiv.injective toTimeAndSpace.symm

lemma spaceTime_integrable_iff_space_time_integrable {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ}
    (f : SpaceTime d → M) :
    Integrable f volume ↔ Integrable (f ∘ (toTimeAndSpace.symm)) (volume.prod volume) := by
  symm
  apply MeasureTheory.MeasurePreserving.integrable_comp_emb
  · exact toTimeAndSpace_symm_measurePreserving
  · refine Measurable.measurableEmbedding ?_ ?_
    · fun_prop
    · exact ContinuousLinearEquiv.injective toTimeAndSpace.symm

lemma spaceTime_integral_eq_time_integral_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ}
    (f : SpaceTime d → M)
    (h :  Integrable f volume) :
    ∫ x : SpaceTime d, f x = ∫ t: Time, ∫ x : Space d, f (toTimeAndSpace.symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod]
  rw [spaceTime_integrable_iff_space_time_integrable] at h
  exact h

lemma spaceTime_integral_eq_space_integral_time_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ}
    (f : SpaceTime d → M)
    (h :  Integrable f volume) :
    ∫ x : SpaceTime d, f x = ∫ x : Space d, ∫ t : Time, f (toTimeAndSpace.symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod_symm]
  rw [spaceTime_integrable_iff_space_time_integrable] at h
  exact h

end SpaceTime

end
