/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Kinematics.EMPotential
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient

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


/-- The vector potential from the electromagnetic potential. -/
noncomputable def vectorPotential {d} (A : ElectromagneticPotential d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) := timeSlice <|
  fun x i => A x (Sum.inr i)

/-!

## B. Smoothness of the vector potential

-/

lemma vectorPotential_contDiff {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿A.vectorPotential := by
  simp [vectorPotential]
  apply timeSlice_contDiff
  refine contDiff_euclidean.mpr ?_
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [← contDiff_euclidean]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_apply_contDiff {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d): ContDiff ℝ n ↿(fun t x => A.vectorPotential t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿A.vectorPotential)
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA


lemma vectorPotential_comp_contDiff {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d): ContDiff ℝ n ↿(fun t x => A.vectorPotential t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿A.vectorPotential)
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

lemma vectorPotential_contDiff_space  {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.vectorPotential t) := by
  change ContDiff ℝ n (↿A.vectorPotential ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

lemma vectorPotential_apply_contDiff_space {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) (i : Fin d): ContDiff ℝ n (fun x => A.vectorPotential t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿A.vectorPotential ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff_space A hA t

lemma vectorPotential_contDiff_time  {n} {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.vectorPotential · x) := by
  change ContDiff ℝ n (↿A.vectorPotential ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

/-!

## C. Differentiablity of the vector potential

-/

lemma vectorPotential_differentiable {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ  A) : Differentiable ℝ ↿A.vectorPotential := by
  simp [vectorPotential]
  apply timeSlice_differentiable
  refine differentiable_euclidean.mpr ?_
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [← differentiable_euclidean]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_differentiable_time {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ  A) (x : Space d) : Differentiable ℝ (A.vectorPotential · x)  := by
  change Differentiable ℝ (↿A.vectorPotential ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact vectorPotential_differentiable A hA
  · fun_prop

end ElectromagneticPotential

end Electromagnetism
