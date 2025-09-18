/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
import PhysLean.Particles.StandardModel.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!

# The Higgs field

## i. Overview

The Higgs field describes is the underlying field of the Higgs boson.
It is a map from SpaceTime to a 2-dimensional complex vector space.
In this module we define the Higgs field and prove some basic properties.

## ii. Important results

## iii. Table of Contents

## iv. References

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

## A. The Higgs vector space

The target space of the Higgs field is a 2-dimensional complex vector space.
In this section we will define this vector space, and the action of the
global gauge group on it.

-/


/-!

### A.1 Definition of the Higgs vector space

-/
/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2.
  For a given spacetime point a Higgs field gives a value in `HiggsVec`. -/
abbrev HiggsVec := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-!

### A.2 Relation to `(Fin 2 → ℂ)`

We define the continuous linear map from `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors, we also show that this map is smooth.

-/

/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors. -/
def toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The map `toFin2ℂ` is smooth. -/
lemma smooth_toFin2ℂ : ContMDiff 𝓘(ℝ, HiggsVec) 𝓘(ℝ, Fin 2 → ℂ) ⊤ toFin2ℂ :=
  ContinuousLinearMap.contMDiff toFin2ℂ


/-!

### A.3 Orthonormal basis

We define an orthonormal basis of `HiggsVec`.

-/

/-- An orthonormal basis of `HiggsVec`. -/
def orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-!

## A.4 Generating Higgs vectors from real numbers

Given a real number `a` we define the Higgs vector corresponding to that real number
as `(√a, 0)`. This has the property that it's norm is equal to `a`.

-/

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
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sq_sqrt ha

/-!

### A.5 Action of the gauge group on `HiggsVec`

The gauge group of the Standard Model acts on `HiggsVec` by matrix multiplication.

-/

/-!

#### A.5.1 Definition of the action

-/

instance : SMul StandardModel.GaugeGroupI HiggsVec where
  smul g φ :=  g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ)

lemma gaugeGroupI_smul_eq (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ) := rfl

lemma gaugeGroupI_smul_eq_U1_mul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ)  := by
  rw [gaugeGroupI_smul_eq, ← mulVec_smul]

instance : MulAction StandardModel.GaugeGroupI HiggsVec where
  one_smul φ := by simp [gaugeGroupI_smul_eq]
  mul_smul g₁ g₂ φ := by
    rw [gaugeGroupI_smul_eq, gaugeGroupI_smul_eq, gaugeGroupI_smul_eq_U1_mul_SU2]
    rw [mulVec_smul, mulVec_smul, smul_smul, mulVec_mulVec]
    congr
    simp [mul_pow]

/-!

#### A.5.2 Unitary nature of the action

The action of `StandardModel.GaugeGroupI` on `HiggsVec` is unitary.

-/
open InnerProductSpace

@[simp]
lemma gaugeGroupI_smul_inner (g : StandardModel.GaugeGroupI) (φ ψ : HiggsVec) :
    ⟪g • φ, g • ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ  := by
  calc ⟪g • φ, g • ψ⟫_ℂ
    _ =   WithLp.ofLp (g • ψ) ⬝ᵥ star (WithLp.ofLp (g • φ)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = (g • ψ) ⬝ᵥ star (g • φ) := by rfl
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ) ) ⬝ᵥ star (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ)) := by
      rw [gaugeGroupI_smul_eq_U1_mul_SU2, gaugeGroupI_smul_eq_U1_mul_SU2]
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ) ) ⬝ᵥ (star ((g.toU1 ^ 3 • φ)) ᵥ*  star (g.toSU2.1)) := by
      rw [star_mulVec]
      rfl
    _ = ((star (g.toSU2.1) * g.toSU2.1) *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm, mulVec_mulVec]
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [mem_unitaryGroup_iff'.mp (GaugeGroupI.toSU2 g).2.1]
      simp
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star (g.toU1 ^ 3) • star (φ.toFin2ℂ) := by
      congr
      ext i
      simp
      change (starRingEnd ℂ) (GaugeGroupI.toU1 g ^ 3 * φ i)  = _
      simp
      rfl
    _ = (ψ ⬝ᵥ star (φ.toFin2ℂ)) := by
      rw [dotProduct_smul, smul_dotProduct, smul_smul, unitary.star_mul_self]
      simp

@[simp]
lemma gaugeGroupI_smul_norm (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    ‖g • φ‖  = ‖φ‖  := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  simp

/-!

### A.6. The Gauge orbit of a Higgs vector

We show that two Higgs vectors are in the same gauge orbit if and only if they have the same norm.

-/

/-!

#### A.6.1 The rotation matrix to ofReal

We define an element of `GaugeGroupI` which takes a given Higgs vector to the
corresponding `ofReal` Higgs vector.

-/

/-- Given a Higgs vector, a rotation matrix which puts the second component of the
  vector to zero, and the first component to a real -/
def toRealGroupElem (φ : HiggsVec) : GaugeGroupI :=
  if hφ : φ = 0 then 1 else by
  have h0 :  (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj,  PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' :  (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  refine ⟨1, ⟨!![conj (φ 0) / ‖φ‖, conj (φ 1) / ‖φ‖; -φ 1 /‖φ‖, φ 0 /‖φ‖ ; ], ?_, ?_⟩, 1⟩
  /- Member of the unitary group. -/
  · simp only [Fin.isValue, SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    simp
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i <;> fin_cases j <;>
    all_goals
    · simp
      field_simp
      rw [h0']
      ring
  /- Determinant equals zeor. -/
  · have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    simp [det_fin_two]
    field_simp
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq,]
    simp only [Fin.isValue, mul_conj,  PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
    rw [← mul_conj, ← mul_conj]
    ring

lemma toRealGroupElem_smul_self (φ : HiggsVec) :
    (toRealGroupElem φ) • φ = ofReal (‖φ‖ ^ 2) := by
  by_cases hφ : φ = 0
  · simp [hφ, toRealGroupElem]
    ext i
    fin_cases i <;> simp [ofReal]
  rw [gaugeGroupI_smul_eq]
  have h0 :  (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj,  PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' :  (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  simp [toRealGroupElem, hφ]
  · simp [GaugeGroupI.toU1, GaugeGroupI.toSU2]
    ext i
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i
    · simp [ofReal]
      field_simp
      rw [h0']
      ring_nf
      rfl
    · simp [ofReal]
      field_simp
      change  -(φ 1 * φ 0) + φ 0 * φ 1= _
      ring

/-!

#### A.6.2 Members of orbits

Members of the orbit of a Higgs vector under the action of `GaugeGroupI` are exactly those
Higgs vectors with the same norm.

-/

lemma mem_orbit_gaugeGroupI_iff (φ : HiggsVec) (ψ : HiggsVec) :
    ψ ∈ MulAction.orbit GaugeGroupI φ ↔ ‖ψ‖ = ‖φ‖ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := h
    simp
  · intro h
    use (toRealGroupElem ψ)⁻¹ * toRealGroupElem (φ)
    simp only
    rw [← smul_smul, toRealGroupElem_smul_self φ, ← h, ← toRealGroupElem_smul_self ψ, smul_smul]
    simp

end HiggsVec

/-!

## B. The Higgs bundle

We define the Higgs bundle as the trivial vector bundle with base `SpaceTime` and fiber `HiggsVec`.
The Higgs field will then be defined as smooth sections of this bundle.
-/

/-!

### B.1 Definition of the Higgs bundle

We define the Higgs bundle.

-/

TODO "6V2IS" "Make `HiggsBundle` an associated bundle."

/-- The `HiggsBundle` is defined as the trivial vector bundle with base `SpaceTime` and
  fiber `HiggsVec`. Thus as a manifold it corresponds to `ℝ⁴ × ℂ²`. -/
abbrev HiggsBundle := Bundle.Trivial SpaceTime HiggsVec

/-!

### B.2 Instance of a vector bundle

We given the Higgs bundle an instance of a smooth vector bundle.

-/

/-- The instance of a smooth vector bundle with total space `HiggsBundle` and fiber `HiggsVec`. -/
instance : ContMDiffVectorBundle ⊤ HiggsVec HiggsBundle (Lorentz.Vector.asSmoothManifold 3) :=
  Bundle.Trivial.contMDiffVectorBundle HiggsVec


/-!

## C. The Higgs fields

Higgs fields are smooth sections of the Higgs bundle.
This corresponds to smooth maps from `SpaceTime` to `HiggsVec`.
We here define the type of Higgs fields and create an API around them.

-/

/-- The type `HiggsField` is defined such that elements are smooth sections of the trivial
  vector bundle `HiggsBundle`. Such elements are Higgs fields. Since `HiggsField` is
  trivial as a vector bundle, a Higgs field is equivalent to a smooth map
  from `SpaceTime` to `HiggsVec`. -/
abbrev HiggsField : Type := ContMDiffSection
  (Lorentz.Vector.asSmoothManifold 3) HiggsVec ⊤ HiggsBundle



namespace HiggsField
open HiggsVec

/-!

### C.1 Relations between `HiggsField` and `HiggsVec`

-/

/-!

#### C.1.1 The constant Higgs field

We define the constant Higgs field associated to a given Higgs vector.

-/


/-- Given a vector in `HiggsVec` the constant Higgs field with value equal to that
section. -/
def const : HiggsVec →ₗ[ℝ] HiggsField where
  toFun  φ := {
    toFun := fun _ ↦ φ,
    contMDiff_toFun := by
      intro x
      rw [Bundle.contMDiffAt_section]
      exact contMDiffAt_const}
  map_add' φ ψ := by
    ext1 x
    simp
  map_smul' a φ := by
    ext1 x
    simp

/-- For all spacetime points, the constant Higgs field defined by a Higgs vector,
  returns that Higgs Vector. -/
@[simp]
lemma const_apply (φ : HiggsVec) (x : SpaceTime) : const φ x = φ := rfl

/-!

### C.1.2 The map from `HiggsField` to `SpaceTime → HiggsVec`

-/

/-- Given a `HiggsField`, the corresponding map from `SpaceTime` to `HiggsVec`. -/
def toHiggsVec (φ : HiggsField) : SpaceTime → HiggsVec := φ

lemma toHiggsVec_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, HiggsVec) ⊤ φ.toHiggsVec := by
  intro x0
  have h1 := φ.contMDiff x0
  rw [Bundle.contMDiffAt_section] at h1
  exact h1

lemma const_toHiggsVec_apply (φ : HiggsField) (x : SpaceTime) :
    const (φ.toHiggsVec x) x = φ x := rfl

lemma toFin2ℂ_comp_toHiggsVec (φ : HiggsField) :
    toFin2ℂ ∘ φ.toHiggsVec = φ := rfl

/-!

### C.2 Smoothness properties of components

We prove some smoothness properties of the components of a Higgs field.

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

### C.3 The pointwise inner product

The pointwise inner product on the Higgs field.

-/

open InnerProductSpace

instance : Inner (SpaceTime → ℂ) (HiggsField) where
  inner φ1 φ2 := fun x => ⟪φ1 x, φ2 x⟫_ℂ

/-!

#### C.3.1 Basic equaltities

-/

lemma inner_apply (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) x = ⟪φ1 x, φ2 x⟫_ℂ := rfl

lemma inner_eq_expand (φ1 φ2 : HiggsField) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) = fun x => equivRealProdCLM.symm (((φ1 x 0).re * (φ2 x 0).re
    + (φ1 x 1).re * (φ2 x 1).re+ (φ1 x 0).im * (φ2 x 0).im + (φ1 x 1).im * (φ2 x 1).im),
    ((φ1 x 0).re * (φ2 x 0).im + (φ1 x 1).re * (φ2 x 1).im
    - (φ1 x 0).im * (φ2 x 0).re - (φ1 x 1).im * (φ2 x 1).re)) := by
  funext x
  simp only [inner_apply, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    equivRealProdCLM_symm_apply, ofReal_add, ofReal_mul, ofReal_sub]
  rw [RCLike.conj_eq_re_sub_im, RCLike.conj_eq_re_sub_im]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 0)]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 1)]
  ring_nf
  simp only [Fin.isValue, RCLike.re_to_complex, coe_algebraMap, RCLike.I_to_complex,
    RCLike.im_to_complex, I_sq, mul_neg, mul_one, neg_mul, sub_neg_eq_add, one_mul]
  ring


/-- Expands the inner product on Higgs fields in terms of complex components of the
  Higgs fields. -/
lemma inner_expand_conj (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) x = conj (φ1 x 0) * φ2 x 0 + conj (φ1 x 1) * φ2 x 1 := by
  simp [inner_apply, PiLp.inner_apply]
  ring

/-!

#### C.3.2 Symmetry properties

-/

lemma inner_symm (φ1 φ2 : HiggsField) :
    conj ⟪φ2, φ1⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ)  := by
  funext x
  simp only [inner_apply, Pi.conj_apply, inner_conj_symm]

/-!

#### C.3.3 Linearity conditions

-/

lemma inner_add_left (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1 + φ2, φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ3⟫_(SpaceTime → ℂ) + ⟪φ2, φ3⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]
  rw [_root_.inner_add_left]

lemma inner_add_right (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1, φ2 + φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ) + ⟪φ1, φ3⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]
  rw [_root_.inner_add_right]

end HiggsField

end
end StandardModel
