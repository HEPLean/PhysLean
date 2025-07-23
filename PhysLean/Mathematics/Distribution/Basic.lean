/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Distributions

This file defines distributions `E →d[𝕜] F`, which is a way to generalise functions `E → F`.
Mathematically, a distribution `u : E →d[𝕜] F` takes in a test function `η : E → 𝕜` that is smooth
with rapidly decreasing iterated derivatives, and outputs a value in `F`. This operation is required
to be linear and continuous. Note that the space of test functions is called the Schwartz space and
is denoted `𝓢(E, 𝕜)`.

`E` is required to be a normed vector space over `ℝ`, and `F` can be a normed vector space over `ℝ`
or `ℂ` (which is the field denoted `𝕜`).

## Important Results
- `Distribution.derivative` and `Distribution.fourierTransform` allow us to make sense of these
  operations that might not make sense a priori on general functions.

## Examples
- `Distribution.diracDelta`: Dirac delta distribution at a point `a : E` is a distribution
  that takes in a test function `η : 𝓢(E, 𝕜)` and outputs `η a`.

## TODO
- In the future, any function of polynomial growth can be interpreted as a distribution. This will
  be helpful for defining the distributions that correspond to `H` (Heaviside step function), or
  `cos(x)`.
- Generalise `derivative` to higher dimensional domain.

-/

open SchwartzMap NNReal
noncomputable section

/-- An `F`-valued distribution on `E` (where `E` is a normed vector space over `ℝ` and `F` is a
normed vector space over `𝕜`) is a continuous linear map `𝓢(E, 𝕜) →L[𝕜] F` where `𝒮(E, 𝕜)` is
the Schwartz space of smooth functions `E → 𝕜` with rapidly decreasing iterated derivatives. This
is notated as `E →d[𝕜] F`.

This should be seen as a generalisation of functions `E → F`. -/
abbrev Distribution (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] : Type :=
  𝓢(E, 𝕜) →L[𝕜] F

@[inherit_doc] notation:25 E:arg "→d[" 𝕜:25 "] " F:0 => Distribution 𝕜 E F

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace Distribution

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace 𝕜 F]

/-- The construction of a distribution from the following data:
1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
2. We take a linear map `u` that evaluates the given Schwartz function `η`. At this stage we don't
  need `u` to be continuous.
3. Recall that a Schwartz function `η` satisfies a bound
  `‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
4. This step is where `s` is used: for each test function `η`, the norm `‖u η‖` is required to be
  bounded by `C * (‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖)` for some `x : ℝ` and for some `(k, n) ∈ s`, where
  `C ≥ 0` is a global scalar.
-/
def ofLinear (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖)) : E →d[𝕜] F :=
  mkCLMtoNormedSpace u (by simp) (by simp) <| by
    obtain ⟨C, hC, hu⟩ := hu
    refine ⟨s, C, hC, fun η ↦ ?_⟩
    obtain ⟨k, n, x, hkn, hη⟩ := hu η
    have hs : s.Nonempty := ⟨(k, n), hkn⟩
    refine hη.trans <| mul_le_mul_of_nonneg_left ((le_seminorm 𝕜 k n η x).trans ?_) hC
    rw [Seminorm.finset_sup_apply]
    refine (NNReal.coe_le_coe (r₁ := ⟨SchwartzMap.seminorm 𝕜 k n η, apply_nonneg _ _⟩)).2 ?_
    convert s.le_sup hkn
      (f := fun kn : ℕ × ℕ ↦ (⟨SchwartzMap.seminorm 𝕜 kn.1 kn.2 η, apply_nonneg _ _⟩ : ℝ≥0))

@[simp] lemma ofLinear_apply (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖))
    (η : 𝓢(E, 𝕜)) :
    ofLinear 𝕜 s u hu η = u η :=
  rfl

/-- Dirac delta distribution `diracDelta 𝕜 a : E →d[𝕜] 𝕜` takes in a test function `η : 𝓢(E, 𝕜)`
and outputs `η a`. Intuitively this is an infinite density at a single point `a`. -/
def diracDelta (a : E) : E →d[𝕜] 𝕜 :=
  delta 𝕜 𝕜 a

@[simp] lemma diracDelta_apply (a : E) (η : 𝓢(E, 𝕜)) :
    diracDelta 𝕜 a η = η a :=
  rfl

/-- Dirac delta in a given direction `v : F`. `diracDelta' 𝕜 a v` takesn in a test function
`η : 𝓢(E, 𝕜)` and outputs `η a • v`. Intuitively this is an infinitely intense vector field
at a single point `a` pointing at the direction `v`. -/
def diracDelta' (a : E) (v : F) : E →d[𝕜] F :=
  ContinuousLinearMap.smulRight (diracDelta 𝕜 a) v

@[simp] lemma diracDelta'_apply (a : E) (v : F) (η : 𝓢(E, 𝕜)) :
    diracDelta' 𝕜 a v η = η a • v :=
  rfl

end NormedSpace

section RCLike

/-- Definition of derivative of distribution: Let `u` be a distribution. Then its derivative is
`u'` where given a test function `η`, `u' η := -u(η')`. This agrees with the distribution generated
by the derivative of a differentiable function (with suitable conditions) (to be defined later),
because of integral by parts (where the boundary conditions are `0` by the test functions being
rapidly decreasing). -/
def derivative : (ℝ →d[𝕜] 𝕜) →ₗ[𝕜] (ℝ →d[𝕜] 𝕜) where
  toFun u := (ContinuousLinearEquiv.neg 𝕜).toContinuousLinearMap.comp <| u.comp <|
    SchwartzMap.derivCLM 𝕜
  map_add' u₁ u₂ := by simp
  map_smul' c u := by simp

@[simp] lemma derivative_apply (u : ℝ→d[𝕜] 𝕜) (η : 𝓢(ℝ, 𝕜)) :
    u.derivative 𝕜 η = -u (derivCLM 𝕜 η) :=
  rfl

end RCLike

section fderiv

variable [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [RCLike 𝕜]
  [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Fréchet derivative of a distribution.

Informally, for a distribution `u : E →d[𝕜] F`,
the Fréchet derivative `fderiv u x v` corresponds to the dervative of `u` at the
point `x` in the direction `v`. For example, if `F = ℝ³`
then `fderiv u x v` is a vector in `ℝ³` corrsponding to
`(v₁ ∂u₁/∂x₁ + v₂ ∂u₁/∂x₂ + v₃ ∂u₁/∂x₃, v₁ ∂u₂/∂x₁ + v₂ ∂u₂/∂x₂ + v₃ ∂u₂/∂x₃,...)`.

Formally, for a distribution `u : E →d[𝕜] F`, this is actually defined
the distribution which takes test function `η : E → 𝕜` to
`- u (SchwartzMap.evalCLM v (SchwartzMap.fderivCLM 𝕜 η))`.

Note that, unlike for functions, the Fréchet derivative of a distribution always exists.
-/
def fderivD [FiniteDimensional ℝ E] : (E →d[𝕜] F) →ₗ[𝕜] (E →d[𝕜] (E →L[ℝ] F)) where
  toFun u := {
    toFun η := LinearMap.toContinuousLinearMap {
      toFun v := ContinuousLinearEquiv.neg 𝕜 <| u <|
        SchwartzMap.evalCLM (𝕜 := 𝕜) v <|
        SchwartzMap.fderivCLM 𝕜 (E := E) (F := 𝕜) η
      map_add' v1 v2 := by
        simp only [ContinuousLinearEquiv.neg_apply]
        trans -u ((SchwartzMap.evalCLM (𝕜 := 𝕜) v1) ((fderivCLM 𝕜) η) +
          (SchwartzMap.evalCLM (𝕜 := 𝕜) v2) ((fderivCLM 𝕜) η))
        swap
        · simp only [map_add, neg_add_rev]
          abel
        congr
        ext x
        simp only [SchwartzMap.evalCLM, mkCLM, mkLM, map_add, ContinuousLinearMap.coe_mk',
          LinearMap.coe_mk, AddHom.coe_mk, fderivCLM_apply, add_apply]
        rfl
      map_smul' a v1 := by
        simp only [ContinuousLinearEquiv.neg_apply, RingHom.id_apply, smul_neg, neg_inj]
        trans u (a • (SchwartzMap.evalCLM (𝕜 := 𝕜) v1) ((fderivCLM 𝕜) η))
        swap
        · simp
        congr
        ext x
        simp only [SchwartzMap.evalCLM, mkCLM, mkLM, map_smul, ContinuousLinearMap.coe_mk',
          LinearMap.coe_mk, AddHom.coe_mk, fderivCLM_apply, smul_apply]
        rfl}
    map_add' η1 η2 := by
      ext x
      simp only [map_add, ContinuousLinearEquiv.neg_apply, neg_add_rev,
        LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.add_apply]
    map_smul' a η := by
      ext x
      simp
    cont := by
      refine continuous_clm_apply.mpr ?_
      intro y
      simp only [ContinuousLinearEquiv.neg_apply, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_mk, AddHom.coe_mk]
      fun_prop
  }
  map_add' u₁ u₂ := by
    ext η
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearEquiv.neg_apply, neg_add_rev,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_toContinuousLinearMap']
    abel
  map_smul' c u := by
    ext
    simp

set_option linter.unusedSectionVars false in
lemma fderivD_apply [FiniteDimensional ℝ E] (u : E →d[𝕜] F) (η : 𝓢(E, 𝕜)) (v : E) :
    fderivD 𝕜 u η v = - u (SchwartzMap.evalCLM (𝕜 := 𝕜) v (SchwartzMap.fderivCLM 𝕜 η)) := by
  rfl

end fderiv


section constant
/-!

## The constant distribution

-/
open MeasureTheory
section
variable (E : Type) [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [RCLike 𝕜]
  [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]

def const [hμ : Measure.HasTemperateGrowth (volume (α := E))] (c : F) : E →d[𝕜] F := by
  refine mkCLMtoNormedSpace
    (fun η => ∫ x, η x • c ∂MeasureTheory.volume) ?_
    ?_ ?_
  · intro η1 η2
    simp [add_smul]
    by_cases hc : c = 0
    · subst hc
      simp
    rw [MeasureTheory.integral_add]
    · refine (integrable_smul_const hc).mpr ?_
      exact integrable η1
    · refine (integrable_smul_const hc).mpr ?_
      exact integrable η2
  · intro a η
    simp only [Fin.isValue, smul_apply, RingHom.id_apply, smul_assoc]
    rw [MeasureTheory.integral_smul]
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, ‖c‖ * (2 ^ n * ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(volume (α := E)))
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
    (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm 𝕜 m'.1 m'.2) η)) := by
    intro x
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
  conv_lhs =>
    enter [2, x]
    rw [norm_smul, mul_comm]
  conv_lhs =>
    rw [MeasureTheory.integral_const_mul]
  rw [mul_assoc]
  by_cases hc : c = 0
  · subst hc
    simp
  refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
  · positivity
  apply (integral_mono (by simpa using η.integrable_pow_mul ((volume)) 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

set_option linter.unusedSectionVars false in
lemma const_apply [hμ : Measure.HasTemperateGrowth (volume (α := E))] (c : F)
    (η : 𝓢(E, 𝕜)) :
    const 𝕜 E c η = ∫ x, η x • c ∂MeasureTheory.volume := by rfl
end
section

variable [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option linter.unusedSectionVars false in
@[simp]
lemma fderivD_const [hμ : Measure.IsAddHaarMeasure (volume (α := E))]
    [FiniteDimensional ℝ E] (c : F) :
    fderivD ℝ (const ℝ E c) = 0 := by
  ext η v
  rw [fderivD_apply, const_apply]
  simp
  trans -∫ (x : E), η x • (fderiv ℝ (fun y => c) x) v ∂volume
  swap
  · simp
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]
  simp
  rfl
  · have hs := η.smooth'
    apply MeasureTheory.Integrable.smul_const
    have h0 : (fun x => (fderiv ℝ (⇑η) x) v) = fun x => SchwartzMap.fderivCLM ℝ η x v := by
      funext x
      simp
    change Integrable (SchwartzMap.evalCLM (𝕜 := ℝ) v (SchwartzMap.fderivCLM ℝ η)) volume
    exact integrable ((SchwartzMap.evalCLM v) ((fderivCLM ℝ) η))
  · simp
  · apply MeasureTheory.Integrable.smul_const
    exact integrable η
  · exact SchwartzMap.differentiable η
  · simp

end
end constant

section Complex

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F]

variable (E F) in
/-- Definition of Fourier transform of distribution: Let `u` be a distribution. Then its Fourier
transform is `F{u}` where given a test function `η`, `F{u}(η) := u(F{η})`. -/
def fourierTransform : (E →d[ℂ] F) →ₗ[ℂ] (E →d[ℂ] F) where
  toFun u := u.comp <| fourierTransformCLM ℂ (E := ℂ) (V := E)
  map_add' u₁ u₂ := by simp
  map_smul' c u := by simp

@[simp] lemma fourierTransform_apply (u : E →d[ℂ] F) (η : 𝓢(E, ℂ)) :
    u.fourierTransform E F η = u (fourierTransformCLM ℂ η) :=
  rfl


end Complex

/-!

## Heaviside step function

-/
open MeasureTheory

def heavisideStep (d : ℕ) : (EuclideanSpace ℝ (Fin d.succ)) →d[ℝ] ℝ := by
  refine mkCLMtoNormedSpace
    (fun η => ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x (Fin.last d)}, η x ∂MeasureTheory.volume) ?_
    ?_ ?_
  · intro η1 η2
    simp
    rw [MeasureTheory.integral_add]
    · apply MeasureTheory.Integrable.restrict
      exact integrable η1
    · apply MeasureTheory.Integrable.restrict
      exact integrable η2
  · intro a η
    simp only [Fin.isValue, smul_apply, RingHom.id_apply]
    rw [MeasureTheory.integral_smul]
  haveI hμ : (volume (α := EuclideanSpace ℝ (Fin d.succ))).HasTemperateGrowth := by
    infer_instance
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(volume (α := EuclideanSpace ℝ (Fin d.succ)))
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  trans ∫ x, ‖η x‖ ∂(volume (α := EuclideanSpace ℝ (Fin d.succ)))
  · refine setIntegral_le_integral ?_ ?_
    · have hi := integrable η  (μ := volume)
      fun_prop
    · filter_upwards with x
      simp
  · have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) η)) := by
      intro x
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
        le_div_iff₀' (by positivity), Real.rpow_natCast]
      simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
    apply (integral_mono (by simpa using η.integrable_pow_mul ((volume)) 0) _ h').trans
    · unfold schwartzSeminormFamily
      rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
    apply h.mul_const

lemma heavisideStep_apply (d : ℕ) (η : 𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ)) :
    heavisideStep d η = ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x (Fin.last d)}, η x ∂MeasureTheory.volume := by
  rfl

end Distribution
