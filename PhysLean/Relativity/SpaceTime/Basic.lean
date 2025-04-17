/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.Basic
import PhysLean.ClassicalMechanics.Space.Basic
import PhysLean.ClassicalMechanics.Time.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

noncomputable section

TODO "6V2DR" "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- The space-time -/
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
    space (Lorentz.Vector.toCoord.symm f) = fun i => f (Sum.inr i) := by
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
  toFun x := Lorentz.Vector.timeComponent x
  map_add' x1 x2 := by
    simp [Lorentz.Vector.timeComponent]
  map_smul' c x := by
    simp [Lorentz.Vector.timeComponent]

@[simp]
lemma time_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    time (Lorentz.Vector.toCoord.symm f) =f (Sum.inl 0) := by
  simp [time, Lorentz.Vector.timeComponent]

/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time, x.space)
    invFun tx := Lorentz.Vector.toCoord.symm (fun i =>
      match i with
      | Sum.inl _ => tx.1
      | Sum.inr i => tx.2 i)
    left_inv x := by
      obtain ⟨x, rfl⟩ := Lorentz.Vector.toCoord.symm.surjective x
      simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, time, LinearMap.coe_mk,
        AddHom.coe_mk, space, EmbeddingLike.apply_eq_iff_eq]
      funext i
      match i with
      | Sum.inl 0 => simp [Lorentz.Vector.timeComponent]
      | Sum.inr i => simp [Lorentz.Vector.spatialPart]
    right_inv tx := by
      simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, time, Lorentz.Vector.timeComponent,
        Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply, space]
      obtain ⟨fst, snd⟩ := tx
      simp only [Prod.mk.injEq, true_and]
      funext i
      simp [Lorentz.Vector.spatialPart]
    map_add' x y := by
      simp
    map_smul' := by
      simp
  }

lemma toTimeAndSpace_basis_natAdd {d : ℕ} (i : Fin d) :
    toTimeAndSpace ((Tensor.basis (S := realLorentzTensor d) ![Color.up])
      fun x => Fin.cast (by simp) (Fin.natAdd 1 i))
    = (0, Space.basis i) := by
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, toTimeAndSpace, time, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, Prod.mk.injEq]
  rw [Lorentz.Vector.timeComponent_basis_natAdd]
  simp only [true_and]
  funext j
  simp [space]
  rw [Lorentz.Vector.spatialPart_basis_natAdd]
  simp [Space.basis]
  rw [Finsupp.single_apply]
  simp only [Sum.inr.injEq]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

/-!

## Coordinates

-/

/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun := flip (Lorentz.Vector.toCoord (d := d)) (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp [flip]
  map_smul' c x := by
    simp [flip]

@[inherit_doc coord]
scoped notation "𝔁" => coord

lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl

lemma coord_on_repr {d : ℕ} (μ : Fin (1 + d))
    (y : ComponentIdx (S := realLorentzTensor d) ![Color.up] → ℝ) :
    𝔁 μ ((Tensor.basis (S := realLorentzTensor d)
      ![Color.up]).repr.symm (Finsupp.equivFunOnFinite.symm y)) =
    y (fun _ => Fin.cast (by simp) μ) := by
  change 𝔁 μ (Lorentz.Vector.toCoordFull.symm y) = _
  rw [coord_apply]
  rw [Lorentz.Vector.toCoord_apply_eq_toCoordFull_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply,
    Equiv.piCongrLeft'_apply]
  congr
  funext x
  fin_cases x
  simp [Lorentz.Vector.indexEquiv]

/-!

## Derivatives

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinte. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Tensor.basis _ (fun x => Fin.cast (by simp) μ))

@[inherit_doc deriv]
scoped notation "∂_" => deriv

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
lemma deriv_eq {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → M) (y : SpaceTime d) :
    SpaceTime.deriv μ f y =
    fderiv ℝ f y (Tensor.basis _ (fun x => Fin.cast (by simp) μ)) := by
  rfl

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin (1 + d)) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

lemma deriv_eq_deriv_on_coord {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    SpaceTime.deriv μ f y = fderiv ℝ
      (fun y => (f ((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr.symm
            (Finsupp.equivFunOnFinite.symm y))))
      ⇑((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y)
    ⇑(Finsupp.single (fun x => Fin.cast (by simp) μ) 1) := by
  change _ = fderiv ℝ (f ∘ Lorentz.Vector.fromCoordFullContinuous)
    ⇑((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y)
    ⇑(Finsupp.single (fun x => Fin.cast (by simp) μ) 1)
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rw [deriv_eq]
  congr
  simp [Lorentz.Vector.fromCoordFullContinuous, Lorentz.Vector.toCoordFull]
  exact (LinearEquiv.eq_symm_apply _).mpr rfl

lemma neg_deriv {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) :
    - SpaceTime.deriv μ f = SpaceTime.deriv μ (fun y => - f y) := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp only [Pi.neg_apply, fderiv_neg, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply, neg_inj]
  rfl

lemma neg_deriv_apply {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    - SpaceTime.deriv μ f y = SpaceTime.deriv μ (fun y => - f y) y:= by
  rw [← SpaceTime.neg_deriv]
  rfl

@[fun_prop]
lemma coord_differentiable {d : ℕ} (μ : Fin (1 + d)) :
    Differentiable ℝ (𝔁 μ) := by
  let φ : (Fin 1 ⊕ Fin d) → (SpaceTime d) → ℝ := fun b y => y b
  change Differentiable ℝ (fun y => φ _ _)
  have h : Differentiable ℝ (flip φ) := by
    change Differentiable ℝ Lorentz.Vector.toCoord
    fun_prop
  rw [differentiable_pi] at h
  exact h (finSumFinEquiv.symm μ)

lemma deriv_coord_same {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    SpaceTime.deriv μ (𝔁 μ) y = 1 := by
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  let φ : ((x : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] x)))
    → (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ)
    → ℝ := fun b y => y b
  conv_lhs =>
    enter [1, 2, y]
    rw [coord_on_repr]
    change φ _ y
  have h1 : (fun y => fun i => φ i y) = id := by rfl
  have h2 (x) : fderiv ℝ (fun y => fun i => φ i y) x = ContinuousLinearMap.id _ _ := by
    rw [h1]
    simp
  have h3 (x) : ∀ (i), DifferentiableAt ℝ (φ i) x := by
    have h3' : DifferentiableAt ℝ (flip φ) x := by
      change DifferentiableAt ℝ ((fun y => fun i => φ i y)) x
      rw [h1]
      exact differentiableAt_id
    rw [differentiableAt_pi] at h3'
    intro i
    have h3'' := h3' i
    exact h3''
  conv at h2 =>
    enter [x]
    rw [fderiv_pi (h3 x)]
  have h2' := h2 ((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y)
  change (ContinuousLinearMap.pi fun i =>
    fderiv ℝ (φ i) ⇑((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y))
    ((Finsupp.single (fun x => Fin.cast (by simp) μ) 1)) (fun _ => Fin.cast (by simp) μ) = _
  rw [h2']
  simp

lemma deriv_coord_diff {d : ℕ} (μ ν : Fin (1 + d)) (h : μ ≠ ν) (y : SpaceTime d) :
    SpaceTime.deriv μ (𝔁 ν) y = 0 := by
  rw [SpaceTime.deriv_eq_deriv_on_coord]
  let φ : ((x : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] x)))
    → (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ)
    → ℝ := fun b y => y b
  conv_lhs =>
    enter [1, 2, y]
    rw [coord_on_repr]
    change φ _ y
  have h1 : (fun y => fun i => φ i y) = id := by rfl
  have h2 (x) : fderiv ℝ (fun y => fun i => φ i y) x = ContinuousLinearMap.id _ _ := by
    rw [h1]
    simp
  have h3 (x) : ∀ (i), DifferentiableAt ℝ (φ i) x := by
    have h3' : DifferentiableAt ℝ (flip φ) x := by
      change DifferentiableAt ℝ ((fun y => fun i => φ i y)) x
      rw [h1]
      exact differentiableAt_id
    rw [differentiableAt_pi] at h3'
    intro i
    have h3'' := h3' i
    exact h3''
  conv at h2 =>
    enter [x]
    rw [fderiv_pi (h3 x)]
  have h2' := h2 ((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y)
  change (ContinuousLinearMap.pi fun i => fderiv ℝ (φ i)
    ⇑((Tensor.basis (S := realLorentzTensor d) ![Color.up]).repr y))
    ((Finsupp.single (fun x => Fin.cast (by simp) μ) 1)) (fun _ => Fin.cast (by simp) ν) = _
  rw [h2']
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ContinuousLinearMap.coe_id', id_eq]
  rw [Finsupp.single_apply]
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  intro hn
  have hnx := congrFun hn 0
  simp at hnx
  omega

lemma deriv_coord_eq_if {d : ℕ} (μ ν : Fin (1 + d)) (y : SpaceTime d) :
    SpaceTime.deriv μ (𝔁 ν) y = if μ = ν then 1 else 0 := by
  by_cases h : μ = ν
  · simp only [h, ↓reduceIte]
    exact SpaceTime.deriv_coord_same ν y
  · rw [if_neg h]
    exact SpaceTime.deriv_coord_diff μ ν h y

@[simp]
lemma deriv_toTimeAndSpace {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    SpaceTime.deriv μ (toTimeAndSpace) y = toTimeAndSpace
      ((Tensor.basis _ (fun x => Fin.cast (by simp) μ))) := by
  simp [SpaceTime.deriv]
  rw [ContinuousLinearEquiv.fderiv]
  rfl

lemma deriv_comp_toTimeAndSpace_natAdd {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (i : Fin (d)) (f : Time × Space d → M) (y : SpaceTime d) :
    SpaceTime.deriv (Fin.natAdd 1 i) (f ∘ toTimeAndSpace) y =
    fderiv ℝ f (toTimeAndSpace y) (0, Space.basis i) := by
  rw [SpaceTime.deriv_eq]
  have h1 := toTimeAndSpace.comp_right_fderiv (f := f) (x := y)
  conv_lhs =>
    enter [1]
    rw [h1]
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [toTimeAndSpace_basis_natAdd]

end SpaceTime

end
