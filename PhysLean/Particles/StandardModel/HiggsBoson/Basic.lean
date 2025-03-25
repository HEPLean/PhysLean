/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
/-!

# The Higgs field

This file defines the basic properties for the Higgs field in the standard model.

## References

- We use conventions given in: [Review of Particle Physics, PDG][ParticleDataGroup:2018ovx]

-/

namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime

/-!

## The definition of the Higgs vector space.

In other words, the target space of the Higgs field.
-/

/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2.
  For a given spacetime point a Higgs field gives a value in `HiggsVec`. -/
abbrev HiggsVec := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors. -/
def toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The map `toFin2ℂ` is smooth. -/
lemma smooth_toFin2ℂ : ContMDiff 𝓘(ℝ, HiggsVec) 𝓘(ℝ, Fin 2 → ℂ) ⊤ toFin2ℂ :=
  ContinuousLinearMap.contMDiff toFin2ℂ

/-- An orthonormal basis of `HiggsVec`. -/
def orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-- Generating a Higgs vector from a real number, such that the norm-squared of that Higgs vector
  is the given real number. -/
def ofReal (a : ℝ) : HiggsVec :=
  ![Real.sqrt a, 0]

@[simp]
lemma ofReal_normSq {a : ℝ} (ha : 0 ≤ a) : ‖ofReal a‖ ^ 2 = a := by
  simp only [ofReal]
  rw [PiLp.norm_sq_eq_of_L2]
  rw [@Fin.sum_univ_two]
  simp only [Fin.isValue, cons_val_zero, norm_real, Real.norm_eq_abs, _root_.sq_abs, cons_val_one,
    head_cons, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sq_sqrt ha

end HiggsVec

/-!

## Definition of the Higgs Field

We also define the Higgs bundle.
-/

TODO "Make `HiggsBundle` an associated bundle."

/-- The `HiggsBundle` is defined as the trivial vector bundle with base `SpaceTime` and
  fiber `HiggsVec`. Thus as a manifold it corresponds to `ℝ⁴ × ℂ²`. -/
abbrev HiggsBundle := Bundle.Trivial SpaceTime HiggsVec

/-- The instance of a smooth vector bundle with total space `HiggsBundle` and fiber `HiggsVec`. -/
instance : ContMDiffVectorBundle ⊤ HiggsVec HiggsBundle (Lorentz.Vector.asSmoothManifold 3) :=
  Bundle.Trivial.contMDiffVectorBundle HiggsVec

/-- The type `HiggsField` is defined such that elements are smooth sections of the trivial
  vector bundle `HiggsBundle`. Such elements are Higgs fields. Since `HiggsField` is
  trivial as a vector bundle, a Higgs field is equivalent to a smooth map
  from `SpaceTime` to `HiggsVec`. -/
abbrev HiggsField : Type := ContMDiffSection
  (Lorentz.Vector.asSmoothManifold 3) HiggsVec ⊤ HiggsBundle

/-- Given a vector in `HiggsVec` the constant Higgs field with value equal to that
section. -/
def HiggsVec.toField (φ : HiggsVec) : HiggsField where
  toFun := fun _ ↦ φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact contMDiffAt_const

/-- For all spacetime points, the constant Higgs field defined by a Higgs vector,
  returns that Higgs Vector. -/
@[simp]
lemma HiggsVec.toField_apply (φ : HiggsVec) (x : SpaceTime) : (φ.toField x) = φ := rfl

namespace HiggsField
open HiggsVec

/-!

## Relation to `HiggsVec`

-/

/-- Given a `HiggsField`, the corresponding map from `SpaceTime` to `HiggsVec`. -/
def toHiggsVec (φ : HiggsField) : SpaceTime → HiggsVec := φ

lemma toHiggsVec_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, HiggsVec) ⊤ φ.toHiggsVec := by
  intro x0
  have h1 := φ.contMDiff x0
  rw [Bundle.contMDiffAt_section] at h1
  exact h1

lemma toField_toHiggsVec_apply (φ : HiggsField) (x : SpaceTime) :
    (φ.toHiggsVec x).toField x = φ x := rfl

lemma toFin2ℂ_comp_toHiggsVec (φ : HiggsField) :
    toFin2ℂ ∘ φ.toHiggsVec = φ := rfl

/-!

## Smoothness properties of components

-/

lemma toVec_smooth (φ : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, Fin 2 → ℂ) ⊤ φ :=
  smooth_toFin2ℂ.comp φ.toHiggsVec_smooth

lemma apply_smooth (φ : HiggsField) :
    ∀ i, ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤ (fun (x : SpaceTime) => (φ x i)) :=
  (contMDiff_pi_space).mp (φ.toVec_smooth)

lemma apply_re_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (reCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.contMDiff reCLM).comp (φ.apply_smooth i)

lemma apply_im_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (imCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.contMDiff imCLM).comp (φ.apply_smooth i)

/-!

## Constant Higgs fields

-/

/-- A Higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def IsConst (Φ : HiggsField) : Prop := ∀ x y, Φ x = Φ y

lemma isConst_of_higgsVec (φ : HiggsVec) : φ.toField.IsConst := fun _ => congrFun rfl

lemma isConst_iff_of_higgsVec (Φ : HiggsField) : Φ.IsConst ↔ ∃ (φ : HiggsVec), Φ = φ.toField :=
  Iff.intro (fun h ↦ ⟨Φ 0, by ext x y; rw [← h x 0]; rfl⟩) (fun ⟨φ, hφ⟩ x y ↦ by subst hφ; rfl)

/-- Generating a constant Higgs field from a real number, such that the norm-squared of that Higgs
  vector is the given real number. -/
def ofReal (a : ℝ) : HiggsField := (HiggsVec.ofReal a).toField

/-- The higgs field which is all zero. -/
def zero : HiggsField := ofReal 0

/-- The zero Higgs field is the zero section of the Higgs bundle, i.e., the HiggsField `zero`
defined by `ofReal 0` is the constant zero-section of the bundle `HiggsBundle`.
-/
informal_lemma zero_is_zero_section where
  deps := [`StandardModel.HiggsField.zero]

end HiggsField

end
end StandardModel
