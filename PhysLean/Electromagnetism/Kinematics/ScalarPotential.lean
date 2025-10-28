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

# The Scalar Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the scalar potential, and prove lemmas about it.
In our current implementation `c = 1` so the scalar potential is simply given
by the time component of the electromagnetic potential.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the scalar potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.scalarPotential` : The scalar potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Scalar Potential
- B. Smoothness of the Scalar Potential
- C. Differentiability of the Scalar Potential

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

## A. Definition of the Scalar Potential

-/

/-- The scalar potential from the electromagnetic potential. -/
noncomputable def scalarPotential {d} (A : ElectromagneticPotential d) :
    Time → Space d → ℝ := timeSlice <|
  fun x => A x (Sum.inl 0)

/-!

## B. Smoothness of the Scalar Potential

We prove various lemmas about the smoothness of the scalar potential.

-/

lemma scalarPotential_contDiff {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿A.scalarPotential := by
  simp [scalarPotential]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [← contDiff_euclidean]
    exact hA
  exact h1 (Sum.inl 0)

lemma scalarPotential_contDiff_space {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.scalarPotential t) := by
  change ContDiff ℝ n (↿A.scalarPotential ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact scalarPotential_contDiff A hA
  · fun_prop

lemma scalarPotential_contDiff_time {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.scalarPotential · x) := by
  change ContDiff ℝ n (↿A.scalarPotential ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact scalarPotential_contDiff A hA
  · fun_prop

/-!

## C. Differentiability of the Scalar Potential

We prove various lemmas about the differentiability of the scalar potential.

-/

lemma scalarPotential_differentiable {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿A.scalarPotential := by
  simp [scalarPotential]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [← differentiable_euclidean]
    exact hA
  exact h1 (Sum.inl 0)

lemma scalarPotential_differentiable_space {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (t : Time) : Differentiable ℝ (A.scalarPotential t) := by
  change Differentiable ℝ (↿A.scalarPotential ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact scalarPotential_differentiable A hA
  · fun_prop

lemma scalarPotential_differentiable_time {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.scalarPotential · x) := by
  change Differentiable ℝ (↿A.scalarPotential ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact scalarPotential_differentiable A hA
  · fun_prop

end ElectromagneticPotential

end Electromagnetism
