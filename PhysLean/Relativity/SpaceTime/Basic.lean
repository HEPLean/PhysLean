/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

noncomputable section

TODO "6V2DR" "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- The space-time -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space part of spacetime. -/
@[simp]
def space (x : SpaceTime d) : EuclideanSpace ℝ (Fin d) :=
  fun i => x (Sum.inr i)

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

open realLorentzTensor

lemma coord_on_repr {d : ℕ} (μ : Fin (1 + d))
    (y : ((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) → ℝ) :
    𝔁 μ (((realLorentzTensor d).tensorBasis ![Color.up]).repr.symm
      (Finsupp.equivFunOnFinite.symm y)) =
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
  fun y => fderiv ℝ f y ((realLorentzTensor d).tensorBasis _ (fun x => Fin.cast (by simp) μ))

@[inherit_doc deriv]
scoped notation "∂_" => deriv

/-- The derivative with respect to time. -/
scoped notation "∂ₜ" => deriv 0

lemma deriv_eq {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    SpaceTime.deriv μ f y =
    fderiv ℝ f y ((realLorentzTensor d).tensorBasis _ (fun x => Fin.cast (by simp) μ)) := by
  rfl

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin (1 + d)) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

lemma deriv_eq_deriv_on_coord {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    SpaceTime.deriv μ f y = fderiv ℝ
      (fun y => (f (((realLorentzTensor d).tensorBasis ![Color.up]).repr.symm
            (Finsupp.equivFunOnFinite.symm y))))
      ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
    ⇑(Finsupp.single (fun x => Fin.cast (by simp) μ) 1) := by
  change _ = fderiv ℝ (f ∘ Lorentz.Vector.fromCoordFullContinuous)
    ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
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
  let φ : (Fin 1 ⊕ Fin d) → (↑(SpaceTime d).V) → ℝ := fun b y => y b
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
  have h2' := h2 (((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
  change (ContinuousLinearMap.pi fun i =>
    fderiv ℝ (φ i) ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y))
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
  have h2' := h2 (((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
  change (ContinuousLinearMap.pi fun i => fderiv ℝ (φ i)
    ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y))
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

/-- The divergence of a function `SpaceTime d → EuclideanSpace ℝ (Fin d)`. -/
noncomputable def spaceDiv {d : ℕ} (f : SpaceTime d → EuclideanSpace ℝ (Fin d)) :
    SpaceTime d → ℝ :=
  ∑ j, SpaceTime.deriv (finSumFinEquiv (Sum.inr j)) (fun y => f y j)

@[inherit_doc spaceDiv]
scoped[SpaceTime] notation "∇⬝" E => spaceDiv E

/-- The curl of a function `SpaceTime → EuclideanSpace ℝ (Fin 3)`. -/
def spaceCurl (f : SpaceTime → EuclideanSpace ℝ (Fin 3)) :
    SpaceTime → EuclideanSpace ℝ (Fin 3) := fun x j =>
  match j with
  | 0 => deriv 1 (fun y => f y 2) x - deriv 2 (fun y => f y 1) x
  | 1 => deriv 2 (fun y => f y 0) x - deriv 0 (fun y => f y 2) x
  | 2 => deriv 0 (fun y => f y 1) x - deriv 1 (fun y => f y 0) x

@[inherit_doc spaceCurl]
scoped[SpaceTime] notation "∇×" => spaceCurl

end SpaceTime

end
