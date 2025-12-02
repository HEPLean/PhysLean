/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.IsExtrema
import PhysLean.SpaceAndTime.Space.Norm
import PhysLean.SpaceAndTime.Space.Translations
import PhysLean.SpaceAndTime.Space.ConstantSliceDist
import PhysLean.SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!

# The magnetic field around a infinite wire
-/

namespace Electromagnetism
open Distribution SchwartzMap
open Space MeasureTheory
namespace DistElectromagneticPotential

/-!

## A. The current density

-/

/-- The current density associated with an infinite wire carrying a current `I`
  along the `x`-axis. -/
noncomputable def wireCurrentDensity (c : SpeedOfLight) :
    ℝ →ₗ[ℝ] DistLorentzCurrentDensity 3 where
  toFun I := (SpaceTime.distTimeSlice c).symm <|
    constantTime <|
    constantSliceDist 0
    (I • diracDelta' ℝ 0 (Lorentz.Vector.basis (Sum.inr 0)))
  map_add' I1 I2 := by simp [add_smul]
  map_smul' r I := by simp [smul_smul]

@[simp]
lemma wireCurrentDensity_chargeDesnity (c : SpeedOfLight) (I : ℝ) :
    (wireCurrentDensity c I).chargeDensity c = 0 := by
  ext η
  simp [DistLorentzCurrentDensity.chargeDensity, wireCurrentDensity, constantTime_apply,
  constantSliceDist_apply]

lemma wireCurrentDensity_currentDensity_fst (c : SpeedOfLight) (I : ℝ)
    (η : 𝓢(Time × Space 3, ℝ)) :
    (wireCurrentDensity c I).currentDensity c η 0 =
    (constantTime <|
    constantSliceDist 0 <|
    I • diracDelta ℝ 0) η := by
  simp [wireCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    constantTime_apply, constantSliceDist_apply, diracDelta'_apply]

@[simp]
lemma wireCurrentDensity_currentDensity_snd (c : SpeedOfLight) (I : ℝ)
    (ε : 𝓢(Time × Space 3, ℝ)) :
    (wireCurrentDensity c I).currentDensity c ε 1 = 0 := by
  simp [wireCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    constantTime_apply, constantSliceDist_apply]

@[simp]
lemma wireCurrentDensity_currentDensity_thrd (c : SpeedOfLight) (I : ℝ)
    (ε : 𝓢(Time × Space 3, ℝ)) :
    (wireCurrentDensity c I).currentDensity c ε 2 = 0 := by
  simp [wireCurrentDensity, DistLorentzCurrentDensity.currentDensity,
    constantTime_apply, constantSliceDist_apply, diracDelta'_apply]

/-- The electromagnetic potential of an infinite wire along the x-axis carrying a current `I`. -/
noncomputable def infiniteWire (𝓕 : FreeSpace) (I : ℝ) :
    DistElectromagneticPotential 3 :=
  (SpaceTime.distTimeSlice 𝓕.c).symm <|
  constantTime <|
  constantSliceDist 0
  ((- I * 𝓕.μ₀ / (2 * Real.pi)) • distOfFunction (fun (x : Space 2) =>
    Real.log ‖x‖ • Lorentz.Vector.basis (Sum.inr 0))
  (IsDistBounded.log_norm.smul_const _))

@[simp]
lemma infiniteWire_scalarPotential (𝓕 : FreeSpace) (I : ℝ) :
    (infiniteWire 𝓕 I).scalarPotential 𝓕.c = 0 := by
  ext η
  simp [scalarPotential, Lorentz.Vector.temporalCLM,
  infiniteWire, constantTime_apply, constantSliceDist_apply, distOfFunction_vector_eval]

lemma infiniteWire_vectorPotential (𝓕 : FreeSpace) (I : ℝ) :
    (infiniteWire 𝓕 I).vectorPotential 𝓕.c =
    (constantTime <|
    constantSliceDist 0
    ((- I * 𝓕.μ₀ / (2 * Real.pi)) • distOfFunction (fun (x : Space 2) =>
      Real.log ‖x‖ • EuclideanSpace.single 0 (1 : ℝ))
    (IsDistBounded.log_norm.smul_const _))) := by
  ext η i
  simp [vectorPotential, infiniteWire, constantTime_apply,
  constantSliceDist_apply, Lorentz.Vector.spatialCLM, distOfFunction_vector_eval,
  distOfFunction_eculid_eval]
  left
  congr
  funext x
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

lemma infiniteWire_vectorPotential_fst (𝓕 : FreeSpace) (I : ℝ)(η : 𝓢(Time × Space 3, ℝ)) :
    (infiniteWire 𝓕 I).vectorPotential 𝓕.c η 0 =
    (constantTime <|
    constantSliceDist 0 <|
    (- I * 𝓕.μ₀ / (2 * Real.pi)) • distOfFunction (fun (x : Space 2) => Real.log ‖x‖)
    (IsDistBounded.log_norm)) η := by
  simp [infiniteWire_vectorPotential 𝓕 I, constantTime_apply,
    constantSliceDist_apply, distOfFunction_eculid_eval]

@[simp]
lemma infiniteWire_vectorPotential_snd (𝓕 : FreeSpace) (I : ℝ) :
    (infiniteWire 𝓕 I).vectorPotential 𝓕.c η 1 = 0 := by
  simp [infiniteWire_vectorPotential 𝓕 I, constantTime_apply,
    constantSliceDist_apply, distOfFunction_eculid_eval]

@[simp]
lemma infiniteWire_vectorPotential_thrd (𝓕 : FreeSpace) (I : ℝ) :
    (infiniteWire 𝓕 I).vectorPotential 𝓕.c η 2 = 0 := by
  simp [infiniteWire_vectorPotential 𝓕 I, constantTime_apply,
    constantSliceDist_apply, distOfFunction_eculid_eval]

@[simp]
lemma infiniteWire_vectorPotential_distTimeDeriv (𝓕 : FreeSpace) (I : ℝ) :
    distTimeDeriv ((infiniteWire 𝓕 I).vectorPotential 𝓕.c) = 0 := by
  ext1 η
  ext i
  simp [infiniteWire_vectorPotential _ I]

@[simp]
lemma infiniteWire_vectorPotential_distSpaceDeriv_0 (𝓕 : FreeSpace) (I : ℝ) :
    distSpaceDeriv 0 ((infiniteWire 𝓕 I).vectorPotential 𝓕.c) = 0 := by
  ext1 η
  simp [infiniteWire_vectorPotential _ I]
  right
  rw [constantTime_distSpaceDeriv, distDeriv_constantSliceDist_same]
  simp

@[simp]
lemma infiniteWire_electricField (𝓕 : FreeSpace) (I : ℝ) :
    (infiniteWire 𝓕 I).electricField 𝓕.c = 0 := by
  ext1 η
  ext i
  simp [electricField]

lemma infiniteWire_isExterma {𝓕 : FreeSpace} {I : ℝ} :
    IsExtrema 𝓕 (infiniteWire 𝓕 I) (wireCurrentDensity 𝓕.c I) := by
  simp [isExtrema_iff_components, gradLagrangian_sum_inl_0]
  intro η i
  rw [gradLagrangian_sum_inr_i]
  simp [SpaceTime.distTimeSlice_symm_apply]
  generalize ((compCLMOfContinuousLinearEquiv ℝ (SpaceTime.toTimeAndSpace 𝓕.c).symm) η) = ε at *
  field_simp
  simp
  have h1 (a b : ℝ) : -a + b = 0 ↔ a = b := by grind
  rw [h1]
  trans ∑ x, -(distSpaceDeriv x (distSpaceDeriv x ((infiniteWire 𝓕 I).vectorPotential 𝓕.c)) ε i
    - distSpaceDeriv x (distSpaceDeriv i ((infiniteWire 𝓕 I).vectorPotential 𝓕.c)) ε x)
  · congr
    funext j
    rw [magneticFieldMatrix_distSpaceDeriv_basis_repr_eq_vector_potential]
    ring
  fin_cases i
  · simp [Fin.sum_univ_three]
    simp [distSpaceDeriv_apply', infiniteWire_vectorPotential_fst]
    simp [apply_fderiv_eq_distSpaceDeriv, wireCurrentDensity_currentDensity_fst]
    field_simp
    simp only [constantTime_distSpaceDeriv, mul_assoc]
    congr
    rw [← ContinuousLinearMap.add_apply, ← map_add constantTime]
    trans (constantTime ((constantSliceDist 0) ((2 * Real.pi) • diracDelta ℝ 0))) ε;swap
    · simp
      ring
    congr
    rw [show (2 : Fin 3) = Fin.succAbove (0 : Fin 3) 1 by simp,
      show (1 : Fin 3) = Fin.succAbove (0 : Fin 3) 0 by simp]
    repeat rw [distDeriv_constantSliceDist_succAbove, distDeriv_constantSliceDist_succAbove]
    rw [← map_add (constantSliceDist 0)]
    congr
    trans distDiv (distGrad (distOfFunction (fun (x : Space 2) => Real.log ‖x‖)
      (IsDistBounded.log_norm)))
    · ext ε
      simp [distDiv_apply_eq_sum_distDeriv]
      rw [add_comm]
      congr
      · rw [distDeriv_apply, fderivD_apply]
        conv_rhs => rw [distDeriv_apply, fderivD_apply]
        simp [distGrad_apply]
      · rw [distDeriv_apply, fderivD_apply]
        conv_rhs => rw [distDeriv_apply, fderivD_apply]
        simp [distGrad_apply]
    rw [distGrad_distOfFunction_log_norm]
    have h1 := distDiv_inv_pow_eq_dim (d := 1)
    simp at h1
    simp [h1]
  · simp only [Fin.mk_one, Fin.isValue, neg_sub, Finset.sum_sub_distrib, Fin.sum_univ_three,
    infiniteWire_vectorPotential_distSpaceDeriv_0, map_zero, ContinuousLinearMap.zero_apply,
    PiLp.zero_apply, zero_add, wireCurrentDensity_currentDensity_snd, mul_zero]
    ring_nf
    rw [distSpaceDeriv_commute]
    simp [distSpaceDeriv_apply']
  · simp only [Fin.reduceFinMk, Fin.isValue, neg_sub, Finset.sum_sub_distrib, Fin.sum_univ_three,
    infiniteWire_vectorPotential_distSpaceDeriv_0, map_zero, ContinuousLinearMap.zero_apply,
    PiLp.zero_apply, zero_add, add_sub_add_right_eq_sub, wireCurrentDensity_currentDensity_thrd,
    mul_zero]
    ring_nf
    rw [distSpaceDeriv_commute]
    simp [distSpaceDeriv_apply']

end DistElectromagneticPotential
end Electromagnetism
