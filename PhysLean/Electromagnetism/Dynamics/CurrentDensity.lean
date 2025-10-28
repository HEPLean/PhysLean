/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Dynamics.KineticTerm
import PhysLean.ClassicalMechanics.VectorFields
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

## ii. Key results

- `LorentzCurrentDensity` : The type of Lorentz current densities.
- `LorentzCurrentDensity.chargeDensity` : The charge density associated with a
  Lorentz current density.
- `LorentzCurrentDensity.currentDensity` : The current density associated with a
  Lorentz current density.

## iii. Table of contents

- A. The Lorentz Current Density
- B. The underlying charge
- C. The underlying current density

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
noncomputable def chargeDensity (J : LorentzCurrentDensity d) : Time → Space d → ℝ :=
  fun t x => J (toTimeAndSpace.symm (t, x)) (Sum.inl 0)

lemma chargeDensity_eq_timeSlice {d : ℕ} {J : LorentzCurrentDensity d} :
    J.chargeDensity = timeSlice (fun x => J x (Sum.inl 0)) := by rfl
/-!

### B.1. Differentiability of the charge density
-/

lemma chargeDensity_differentiable {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.chargeDensity) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [← differentiable_euclidean]
    exact hJ
  exact h1 (Sum.inl 0)

lemma chargeDensity_contDiff {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.chargeDensity) := by
  rw [chargeDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [← contDiff_euclidean]
    exact hJ
  exact h1 (Sum.inl 0)

/-!

## C. The underlying current density

-/

/-- The underlying (non-Lorentz) current density associated with a Lorentz current density. -/
noncomputable def currentDensity (J : LorentzCurrentDensity d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x i => J (toTimeAndSpace.symm (t, x)) (Sum.inr i)

lemma currentDensity_eq_timeSlice {d : ℕ} {J : LorentzCurrentDensity d} :
    J.currentDensity = timeSlice (fun x i => J x (Sum.inr i)) := by rfl
/-!

### C.1. Differentiability of the current density

-/

lemma currentDensity_differentiable {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) : Differentiable ℝ ↿(J.currentDensity) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => J x i) := by
    rw [← differentiable_euclidean]
    exact hJ
  exact differentiable_euclidean.mpr fun i => h1 (Sum.inr i)

lemma currentDensity_apply_differentiable {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (i : Fin d) :
    Differentiable ℝ ↿(fun t x => J.currentDensity t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ ↿(J.currentDensity))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)
  · exact currentDensity_differentiable hJ

lemma currentDensity_differentiable_space {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) :
    Differentiable ℝ (fun x => J.currentDensity t x) := by
  change Differentiable ℝ (↿(J.currentDensity) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop

lemma currentDensity_apply_differentiable_space {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => J.currentDensity t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity) ∘ fun x => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop

lemma currentDensity_differentiable_time {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) :
    Differentiable ℝ (fun t => J.currentDensity t x) := by
  change Differentiable ℝ (↿(J.currentDensity) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact currentDensity_differentiable hJ
  · fun_prop

lemma currentDensity_apply_differentiable_time {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : Differentiable ℝ J) (x : Space d) (i : Fin d) :
    Differentiable ℝ (fun t => J.currentDensity t x i) := by
  change Differentiable ℝ (EuclideanSpace.proj i ∘ (↿(J.currentDensity) ∘ fun t => (t, x)))
  refine Differentiable.comp ?_ ?_
  · exact ContinuousLinearMap.differentiable (𝕜 := ℝ) _
  · apply Differentiable.comp ?_ ?_
    · exact currentDensity_differentiable hJ
    · fun_prop

lemma currentDensity_ContDiff {d : ℕ} {J : LorentzCurrentDensity d}
    (hJ : ContDiff ℝ n J) : ContDiff ℝ n ↿(J.currentDensity) := by
  rw [currentDensity_eq_timeSlice]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => J x i) := by
    rw [← contDiff_euclidean]
    exact hJ
  exact contDiff_euclidean.mpr fun i => h1 (Sum.inr i)

end LorentzCurrentDensity

end Electromagnetism
