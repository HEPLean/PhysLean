/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.CurrentDensity
import PhysLean.ClassicalMechanics.VectorFields
/-!

# The Lagrangian in electromagnetism

## i. Overview

In this module we define the Lagrangian density for the electromagnetic field in
presence of a current density. We prover properties of this lagrangian density,
and find it's variational gradient.

## ii. Key results

- `lagrangian` : The lagrangian density for the electromagnetic field in presence of a
  Lorentz current density.
- `gradLagrangian` : The variational gradient of the lagrangian density.
- `gradLagrangian_eq_electricField_magneticField` : The variational gradient of the lagrangian
  density expressed in Gauss's and Ampère laws.

## iii. Table of contents

- A. The Lagrangian density
  - A.1. Shifts in the lagrangian under shifts in the potential
- B. The variational gradient of the lagrangian density
  - B.1. The lagrangian density has a variational gradient
  - B.2. The definition of, `gradLagrangian`, the variational gradient of the lagrangian density
  - B.3. The variational gradient in terms of the gradient of the kinetic term
  - B.4. The lagrangian density has the variational gradient equal to `gradLagrangian`
  - B.5. The variational gradient in terms of the field strength tensor
  - B.6. The lagrangian gradient recovering Gauss's and Ampère laws

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html

-/

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor ContDiff

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
open Lorentz.Vector
open Time Space
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A. The Lagrangian density

The lagrangian density for the electromagnetic field in presence of a current density `J` is
`L = 1/4 F_{μν} F^{μν} - A_μ J^μ`

-/

lemma time_deriv_magneticFieldMatrix {d : ℕ} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix · x (i, j)) t =
    ∂[i] (A.electricField t · j) x - ∂[j] (A.electricField t · i) x := by
  calc _
    _ = ∂ₜ (fun t => ∂[j] (fun x => A.vectorPotential t x i) x) t
        - ∂ₜ (fun t => ∂[i] (fun x => A.vectorPotential t x j) x) t := by
      conv_lhs =>
        enter [1, t]
        rw [magneticFieldMatrix_eq_vectorPotential _ (hA.differentiable (by simp))]
      rw [Time.deriv, fderiv_fun_sub]
      rfl
      all_goals
      · apply Differentiable.differentiableAt
        apply ClassicalMechanics.space_deriv_differentiable_time
        apply vectorPotential_comp_contDiff _ hA
    _ = ∂[j] (fun x =>  ∂ₜ (fun t => A.vectorPotential t x i) t) x
        - ∂[i] (fun x => ∂ₜ (fun t => A.vectorPotential t x j) t) x := by
      rw [ClassicalMechanics.time_deriv_comm_space_deriv _]
      rw [ClassicalMechanics.time_deriv_comm_space_deriv _]
      all_goals
      · apply vectorPotential_comp_contDiff _ hA
    _ = ∂[i] (A.electricField t · j) x - ∂[j] (A.electricField t · i) x := by
      conv_lhs =>
        enter [1, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      conv_lhs =>
        enter [2, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space A hA t), fderiv_fun_neg ]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub
        (by apply (electricField_apply_differentiable_space hA _ _).neg.differentiableAt)
        (by
          apply Differentiable.differentiableAt
          apply Space.deriv_differentiable
          exact scalarPotential_contDiff_space A hA t), fderiv_fun_neg ]
      conv_lhs =>
        enter [1]
        simp
        enter [2]
        rw [← Space.deriv_eq_fderiv_basis, Space.deriv_commute _
          (scalarPotential_contDiff_space A hA t)]
      simp [← Space.deriv_eq_fderiv_basis]
      ring


end ElectromagneticPotential

end Electromagnetism
