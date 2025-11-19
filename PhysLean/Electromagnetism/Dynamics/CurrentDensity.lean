/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

The current density is given in terms of the charge density `ρ` and the current density
` \vec j` as `J = (c ρ, \vec j)`.

## ii. Key results

- `LorentzCurrentDensity` : The type of Lorentz current densities.
- `LorentzCurrentDensity.chargeDensity` : The charge density associated with a
  Lorentz current density.
- `LorentzCurrentDensity.currentDensity` : The current density associated with a
  Lorentz current density.

## iii. Table of contents

- A. The Lorentz Current Density
- B. The underlying charge
  - B.1. Charge density of zero Lorentz current density
  - B.2. Differentiability of the charge density
  - B.3. Smoothness of the charge density
- C. The underlying current density
  - C.1. current density of zero Lorentz current density
  - C.2. Differentiability of the current density
  - C.3. Smoothness of the current density

## iv. References

-/

namespace Electromagnetism
open TensorSpecies
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The Lorentz Current Density

The Lorentz current density is a Lorentz Vector field on spacetime.

-/

/-- The Lorentz current density, also called four-current. -/
abbrev LorentzCurrentDensity (d : ℕ := 3) := SpaceTime d → Lorentz.Vector d

namespace LorentzCurrentDensity

/-!

## B. The underlying charge

-/

/-- The underlying charge density associated with a Lorentz current density. -/
noncomputable def chargeDensity (c : SpeedOfLight := 1)
    (J : LorentzCurrentDensity d) : Time → Space d → ℝ :=
  fun t x => (1 / (c : ℝ)) * J ((toTimeAndSpace c).symm (t, x)) (Sum.inl 0)

lemma chargeDensity_eq_timeSlice {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d} :
    J.chargeDensity c = timeSlice c (fun x => (1 / (c : ℝ)) • J x (Sum.inl 0)) := by rfl

/-!

### B.1. Charge density of zero Lorentz current density

-/

@[simp]
lemma chargeDensity_zero {d : ℕ} {c : SpeedOfLight}:
    chargeDensity c (0 : LorentzCurrentDensity d) = 0 := by
  simp [chargeDensity_eq_timeSlice, timeSlice]
  rfl

/-!

### B.2. Differentiability of the charge density
-/

lemma chargeDensity_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.chargeDensity c) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hJ
  apply Differentiable.fun_const_smul
  exact h1 (Sum.inl 0)

lemma chargeDensity_differentiable_space {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) :
    Differentiable ℝ (fun x => J.chargeDensity c t x) := by
  change Differentiable ℝ (↿(J.chargeDensity c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact chargeDensity_differentiable hJ
  · fun_prop

/-!

### B.3. Smoothness of the charge density

-/

lemma chargeDensity_contDiff {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.chargeDensity c) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hJ
  apply ContDiff.const_smul
  exact h1 (Sum.inl 0)

/-!

## C. The underlying current density

-/

/-- The underlying (non-Lorentz) current density associated with a Lorentz current density. -/
noncomputable def currentDensity (c : SpeedOfLight := 1) (J : LorentzCurrentDensity d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x => WithLp.toLp 2 fun i => J ((toTimeAndSpace c).symm (t, x)) (Sum.inr i)

lemma currentDensity_eq_timeSlice {d : ℕ} {J : LorentzCurrentDensity d} :
    J.currentDensity c = timeSlice c (fun x => WithLp.toLp 2
      fun i => J x (Sum.inr i)) := by rfl

/-!

### C.1. current density of zero Lorentz current density

-/

@[simp]
lemma currentDensity_zero {d : ℕ} {c : SpeedOfLight}:
    currentDensity c (0 : LorentzCurrentDensity d) = 0 := by
  simp [currentDensity_eq_timeSlice, timeSlice]
  rfl
/-!

### C.2. Differentiability of the current density

-/

lemma currentDensity_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.currentDensity c) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hJ
  exact differentiable_euclidean.mpr fun i => h1 (Sum.inr i)

lemma currentDensity_apply_differentiable {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (i : Fin d) :
    Differentiable ℝ ↿(fun t x => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ ↿(J.currentDensity c))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)
  · exact currentDensity_differentiable hJ

lemma currentDensity_differentiable_space {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) :
    Differentiable ℝ (fun x => J.currentDensity c t x) := by
  change Differentiable ℝ (↿(J.currentDensity c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop

lemma currentDensity_apply_differentiable_space {d : ℕ} {c : SpeedOfLight}
    {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity c) ∘ fun x => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop

lemma currentDensity_differentiable_time {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) :
    Differentiable ℝ (fun t => J.currentDensity c t x) := by
  change Differentiable ℝ (↿(J.currentDensity c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop

lemma currentDensity_apply_differentiable_time {d : ℕ} {c : SpeedOfLight}
    {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) (i : Fin d) :
    Differentiable ℝ (fun t => J.currentDensity c t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity c) ∘ fun t => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop

/-!

### C.3. Smoothness of the current density

-/

lemma currentDensity_ContDiff {d : ℕ} {c : SpeedOfLight} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.currentDensity c) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hJ
  exact contDiff_euclidean.mpr fun i => h1 (Sum.inr i)

end LorentzCurrentDensity

end Electromagnetism
