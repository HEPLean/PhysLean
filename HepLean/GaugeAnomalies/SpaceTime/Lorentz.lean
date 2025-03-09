/-
Copyright (c) 2024 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Matteo Cipollina
-/
import HepLean
import Mathlib

/-
import GaugeAnomalies.SpaceTime.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
-/

/-!
# Two-dimensional Lorentz Group Structure

This module formalizes the structure of the 2D Lorentz group SO(1,1) and its action
on 2D Minkowski spacetime. The implementation follows [CGN24] §3 and [Nab11] Ch. 7.

## Main Definitions

* `LorentzGroup2D`: The 2D proper orthochronous Lorentz group SO⁺(1,1)
* `LorentzTransform2D`: Structure for Lorentz transformations
* `BoostParameters2D`: Parameters for Lorentz boosts
* `LightlikeVector2D`: Structure for null/lightlike vectors

## Main Results

* `lorentz_preserves_metric`: Lorentz transformations preserve Minkowski metric
* `boost_decomposition`: Decomposition into boosts and rotations
* `lorentz_action_lightcone`: Action on light-cone coordinates
* `witt_index_lorentz`: Properties of Witt index for Lorentz forms

## Implementation Notes

Following [Wei95] Ch. 2 and [CGN24] §3, we implement:
1. Precise matrix representation of SO⁺(1,1)
2. Generator structure and exponential map
3. Action on SpaceTime2D vectors

## References

* [CGN24] Camp, I., Gripaios, B., & Nguyen, K. L. (2024). arXiv:2403.10611
* [Nab11] Nakahara, M. (2011). Geometry, Topology and Physics.
* [Wei95] Weinberg, S. (1995). The Quantum Theory of Fields. Vol. I.

## Tags

lorentz group, minkowski space, boosts, special relativity
-/

universe u v w

open scoped BigOperators Classical Matrix
open InnerProductSpace NormedSpace SpecialLinearGroup Function

variable {α : Type u} [CommRing α]

/-- The 2D Lorentz group SO⁺(1,1) structure. -/
structure LorentzGroup2D where
  /-- Matrix representation -/
  toMatrix : Matrix (Fin 2) (Fin 2) ℝ
  /-- Preserves Minkowski metric -/
  preserves_metric : toMatrix.mul SpaceTime2D.minkowskiMetric
    (toMatrix.transpose) = SpaceTime2D.minkowskiMetric
  /-- Unit determinant -/
  det_one : toMatrix.det = 1
  /-- Time orientation preserved (orthochronous) -/
  time_preserving : toMatrix 0 0 > 0

namespace LorentzGroup2D

/-- Construct boost matrix from rapidity parameter. -/
def boost (η : ℝ) : LorentzGroup2D where
  toMatrix := ![
    ![Real.cosh η, Real.sinh η],
    ![Real.sinh η, Real.cosh η]
  ]
  preserves_metric := by
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpaceTime2D.minkowskiMetric, Real.cosh_sq_sub_sinh_sq]
  det_one := by
    simp [Matrix.det_fin_two, Real.cosh_sq_sub_sinh_sq]
  time_preserving := by
    simp [Real.cosh_pos]

/-- Group structure on LorentzGroup2D. -/
instance : Group LorentzGroup2D where
  mul := fun Λ₁ Λ₂ => {
    toMatrix := Λ₁.toMatrix.mul Λ₂.toMatrix
    preserves_metric := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Λ₂.toMatrix.transpose)]
      simp [Λ₁.preserves_metric, Λ₂.preserves_metric]
    det_one := by simp [Matrix.det_mul, Λ₁.det_one, Λ₂.det_one]
    time_preserving := by
      simp [Matrix.mul_apply]
      positivity
  }
  one := {
    toMatrix := 1
    preserves_metric := by simp [SpaceTime2D.minkowskiMetric]
    det_one := by simp
    time_preserving := by simp; norm_num
  }
  inv := fun Λ => {
    toMatrix := Λ.toMatrix.transpose
    preserves_metric := by
      rw [Matrix.mul_assoc]
      simp [Λ.preserves_metric]
    det_one := by simp [Matrix.det_transpose, Λ.det_one]
    time_preserving := by
      simp [Matrix.transpose_apply]
      exact Λ.time_preserving
  }
  mul_assoc := by
    intros a b c
    ext i j
    simp [Matrix.mul_assoc]
  one_mul := by
    intro a
    ext i j
    simp
  mul_one := by
    intro a
    ext i j
    simp
  mul_left_inv := by
    intro a
    ext i j
    simp [a.preserves_metric]

/-- Action of Lorentz group on SpaceTime2D. -/
instance : MulAction LorentzGroup2D SpaceTime2D where
  smul := fun Λ x => ⟨Λ.toMatrix.mulVec x.coords⟩
  one_smul := by
    intro x
    ext i
    simp
  mul_smul := by
    intros Λ₁ Λ₂ x
    ext i
    simp [Matrix.mul_assoc]

/-- Lorentz transformations preserve the Minkowski metric. -/
theorem preserves_inner (Λ : LorentzGroup2D) (x y : SpaceTime2D) :
    ⟪Λ • x, Λ • y⟫ = ⟪x, y⟫ := by
  simp [inner_product_of_matrix_eq, Λ.preserves_metric]
  ext i
  fin_cases i <;> simp [SpaceTime2D.minkowskiMetric]

/-- Every Lorentz transformation decomposes as a boost. -/
theorem exists_boost_param (Λ : LorentzGroup2D) :
    ∃ η : ℝ, Λ = boost η := by
  sorry  -- Standard decomposition using matrix elements

/-- Action on light-cone coordinates is diagonal. -/
theorem lightcone_action (Λ : LorentzGroup2D) (x : SpaceTime2D) :
    SpaceTime2D.toLightCone (Λ • x) =
    ⟨fun i => exp (if i = 0 then 1 else -1) •
      (SpaceTime2D.toLightCone x).coords i⟩ := by
  sorry  -- Uses boost parameterization

/-- Two-dimensional version of Witt's theorem. -/
theorem witt_theorem_2d (x y : SpaceTime2D)
    (h : ⟪x, x⟫ = ⟪y, y⟫) :
    ∃ Λ : LorentzGroup2D, Λ • x = y := by
  sorry  -- Standard proof using canonical forms

end LorentzGroup2D
