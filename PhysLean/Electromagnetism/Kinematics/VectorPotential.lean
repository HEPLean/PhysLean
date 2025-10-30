/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.EMPotential
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# The vector Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the vector potential, and prove lemmas about it.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the vector potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Vector Potential
- B. Smoothness of the vector potential
- C. Differentiablity of the vector potential

## iv. References

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. Definition of the Vector Potential

-/

/-- The vector potential from the electromagnetic potential. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) := timeSlice c <|
  fun x i => A x (Sum.inr i)

/-!

## B. Smoothness of the vector potential

We prove various lemmas about the smoothness of the vector potential from
the smoothness of the electromagnetic potential.

-/

lemma vectorPotential_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_contDiff
  refine contDiff_euclidean.mpr ?_
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [← contDiff_euclidean]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_apply_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

lemma vectorPotential_comp_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

lemma vectorPotential_contDiff_space {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.vectorPotential c t) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

lemma vectorPotential_apply_contDiff_space {n} {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) (i : Fin d) :
    ContDiff ℝ n (fun x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿(A.vectorPotential c) ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff_space A hA t

lemma vectorPotential_contDiff_time {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.vectorPotential c · x) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

/-!

## C. Differentiablity of the vector potential

We prove various lemmas about the differentiablity of the vector potential from
the differentiablity of the electromagnetic potential.

-/

lemma vectorPotential_differentiable {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_differentiable
  refine differentiable_euclidean.mpr ?_
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [← differentiable_euclidean]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_differentiable_time {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.vectorPotential c · x) := by
  change Differentiable ℝ (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact vectorPotential_differentiable A hA
  · fun_prop

end ElectromagneticPotential

end Electromagnetism
