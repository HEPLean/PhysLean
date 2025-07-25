/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!
# Time

In this module we define the type `Time`, corresponding to time in a given
(but arbitary) set of units, with a given (but arbitary) choice of origin (time zero),
and a choice of orientation (i.e. a positive time direction).

We note that this is the version of time most often used in undergraduate and
non-mathematical physics.

The choice of units or origin can be made on a case-by-case basis, as
long as they are done consistently. However, since the choice of units and origin is
left implicit, Lean will not catch inconsistencies in the choice of units or origin when
working with `Time`.

For example, for the classical mechanics system corresponding to the harmonic oscillator,
one can take the origin of time to be the time at which the initial conditions are specified,
and the units can be taken as anything as long as the units chosen for time `t` and
the angular frequency `ω` are consistent.

With this notion of `Time`, becomes a 1d vector space over `ℝ` with an inner product.

Within other modules e.g. `TopTime.Basic`, we define versions of time with less choices made.

-/

/-- The type `Time` represents the time in a given (but arbitary) set of units, and
  with a given (but arbitary) choice of origin. -/
structure Time where
  /-- The underlying real number associated with a point in time. -/
  val : ℝ

namespace Time
open MeasureTheory InnerProductSpace

/-- The map `Time.val` taking an element of `Time` to it's underlying real number
  is injective. -/
lemma val_injective : Function.Injective Time.val := by
  intro t1 t2 h
  cases t1
  cases t2
  simp_all

@[ext]
lemma ext_of {t1 t2 : Time} (h : t1.val = t2.val) :
    t1 = t2 := by
  cases t1; cases t2; simp_all

/-!

## The choice of zero, units and orientation

-/

/-- The zero point in `Time`. -/
instance : Zero Time where
  zero := ⟨0⟩

@[simp]
lemma zero_val : (0 : Time).val = 0 := rfl

@[simp]
lemma val_eq_zero (t : Time) : t.val = 0 ↔ t = 0 := by
  constructor
  · intro h
    ext
    exact h
  · rintro rfl
    rfl

/-- The choice of a norm on `Time`, corresponding to the choice of units. -/
instance : Norm Time where
  norm t := ‖t.val‖

/-- The choice of a one on `Time`, corresponding, with the choice of norm,
  to the choice of units. -/
instance : One Time where
  one := ⟨1⟩

@[simp]
lemma one_val : (1 : Time).val = 1 := rfl

/-- The choice of an orientation on `Time`. -/
instance : LE Time where
  le t1 t2 := t1.val ≤ t2.val

lemma le_def (t1 t2 : Time) :
    t1 ≤ t2 ↔ t1.val ≤ t2.val := Iff.rfl

/-!

## Basic operations on `Time`.

-/

instance : Add Time where
  add t1 t2 := ⟨t1.val + t2.val⟩

@[simp]
lemma add_val (t1 t2 : Time) :
    (t1 + t2).val = t1.val + t2.val := rfl

instance : Neg Time where
  neg t := ⟨-t.val⟩

@[simp]
lemma neg_val (t : Time) :
    (-t).val = -t.val := rfl

instance : Sub Time where
  sub t1 t2 := ⟨t1.val - t2.val⟩

@[simp]
lemma sub_val (t1 t2 : Time) :
    (t1 - t2).val = t1.val - t2.val := rfl

instance : SMul ℝ Time where
  smul k t := ⟨k * t.val⟩

@[simp]
lemma smul_real_val (k : ℝ) (t : Time) :
    (k • t).val = k * t.val := rfl

instance : Dist Time where
  dist t1 t2 := ‖t1 - t2‖

lemma dist_eq_val (t1 t2 : Time) :
    dist t1 t2 = ‖t1.val - t2.val‖ := rfl

lemma dist_eq_real_dist (t1 t2 : Time) :
    dist t1 t2 = dist t1.val t2.val := by rfl

instance : Inner ℝ Time where
  inner := fun t1 t2 => t1.val * t2.val

@[simp]
lemma inner_def (t1 t2 : Time) :
    ⟪t1, t2⟫_ℝ = t1.val * t2.val := rfl

/-!

## Instances on `Time`.

-/

instance : AddGroup Time where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp [zero_add]
  add_zero := by intros; ext; simp [add_zero]
  neg_add_cancel := by intros; ext; simp [neg_add_cancel]
  nsmul n t := ⟨n • t.val⟩
  zsmul n t := ⟨n • t.val⟩

instance : AddCommMonoid Time where
  add_comm := by intros; ext; simp [add_comm]

instance : AddCommGroup Time where

instance : Module ℝ Time where
  one_smul t := by ext; simp [one_smul]
  smul_add k t1 t2 := by ext; simp [mul_add]
  smul_zero k := by ext; simp [mul_zero]
  add_smul k1 k2 t := by ext; simp [add_mul]
  mul_smul k1 k2 t := by ext; simp [mul_assoc]
  zero_smul t := by ext; simp [zero_smul]

instance : SeminormedAddCommGroup Time where
  dist_self := by intros; simp [dist_eq_real_dist]
  dist_comm := by intros; simp [dist_eq_real_dist, dist_comm]
  dist_triangle := by intros; simp [dist_eq_real_dist, dist_triangle]

instance : NormedAddCommGroup Time where
  eq_of_dist_eq_zero := by
    intro a b h
    simp [dist, norm] at h
    rw [Time.ext_of_iff]
    rw [sub_eq_zero] at h
    exact h

instance : NormedSpace ℝ Time where
  norm_smul_le := by intros; simp [abs_mul, norm]

instance : PartialOrder Time where
  le_refl := by intros; simp [le_def]
  le_trans := by intro _ _ _; simp [le_def]; exact le_trans
  le_antisymm := by intro _ _; simp [le_def, Time.ext_of_iff]; exact le_antisymm

lemma lt_def (t1 t2 : Time) :
    t1 < t2 ↔ t1.val < t2.val := by
  constructor
  · intro h
    exact lt_iff_le_not_ge.mpr h
  · intro h
    apply lt_iff_le_not_ge.mpr
    simp_all [le_def]
    apply le_of_lt h

noncomputable instance : DecidableEq Time := fun t1 t2 =>
  decidable_of_iff (t1.val = t2.val) Time.ext_of_iff.symm

instance : MeasurableSpace Time := borel Time

instance : BorelSpace Time where
  measurable_eq := by rfl

instance : FiniteDimensional ℝ Time := by
  refine Module.finite_of_rank_eq_one ?_
  rw [@rank_eq_one_iff]
  use ⟨1⟩
  constructor
  · simp [Time.ext_of_iff]
  · intro v
    use v.val
    ext
    simp

noncomputable instance : InnerProductSpace ℝ Time where
  norm_sq_eq_re_inner := by intros; simp [norm]; ring
  conj_inner_symm := by intros; simp [inner_def]; ring
  add_left := by intros; simp [inner_def, add_mul]
  smul_left := by intros; simp [inner_def]; ring

/-!

## Maps from `Time` to `ℝ`.

-/

open MeasureTheory

/-- The continuous linear map from `Time` to `ℝ`. -/
noncomputable def toRealCLM : Time →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  {
  toFun := Time.val
  map_add' := by simp
  map_smul' := by simp }

/-- The continuous linear equivalence from `Time` to `ℝ`. -/
noncomputable def toRealCLE : Time ≃L[ℝ] ℝ := LinearEquiv.toContinuousLinearEquiv
  {
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  }

/-- The linear isomentry equivalence from `Time` to `ℝ`. -/
noncomputable def toRealLIE : Time ≃ₗᵢ[ℝ] ℝ where
  toFun := Time.val
  invFun := fun x => ⟨x⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' := by simp
  map_smul' := by simp
  norm_map' x := by
    simp
    rfl

instance : Coe Time ℝ where
  coe := Time.val

lemma eq_one_smul (t : Time) :
    t = t.val • 1 := by
  ext
  simp [one_val]

@[fun_prop]
lemma val_measurable : Measurable Time.val := by
  change Measurable toRealCLE
  fun_prop

lemma val_measurableEmbedding : MeasurableEmbedding Time.val where
  injective := val_injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑toRealCLE '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage]
    exact toRealCLE.symm.continuous.measurable hs

lemma val_measurePreserving : MeasurePreserving Time.val volume volume :=
  LinearIsometryEquiv.measurePreserving toRealLIE

/-!

## Derivatives

-/

/-- Given a function `f : Time → M` the derivative of `f`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) : Time → M :=
  (fun t => fderiv ℝ f t 1)

@[inherit_doc deriv]
scoped notation "∂ₜ" => deriv

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) (t : Time) : Time.deriv f t = fderiv ℝ f t 1 := rfl

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv, fderiv_fun_const_smul]
  rfl
  fun_prop

lemma deriv_neg [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) :
    ∂ₜ (-f) t = -∂ₜ f t := by
  rw [deriv, fderiv_neg]
  rfl

@[fun_prop]
lemma val_differentiable : Differentiable ℝ Time.val := by
  change Differentiable ℝ toRealCLM
  fun_prop

@[simp]
lemma fderiv_val (t : Time) : fderiv ℝ Time.val t 1 = 1 := by
  change (fderiv ℝ toRealCLM t 1) = 1
  simp
  rfl

end Time
