/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
import PhysLean.Relativity.Tensors.Contraction.Basis
import PhysLean.Relativity.Tensors.Elab
/-!

## Lemmas related to complex Lorentz tensors.

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
noncomputable section

namespace complexLorentzTensor
open TensorSpecies
open Tensor

lemma antiSymm_contr_symm {A : ℂT[.up, .up]} {S : ℂT[.down, .down]}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {A | μ ν ⊗ S | μ ν = - A | μ ν ⊗ S | μ ν}ᵀ := by
  conv_lhs =>
    rw [hA, hs, prodT_permT_left, prodT_permT_right, permT_permT, contrT_comm, contrT_congr 0 1,
      contrT_congr 0 3, contrT_permT,contrT_permT]
    enter [2, 2, 2, 2]
    rw [contrT_congr 0 1]
    enter [2, 2]
    rw [contrT_congr 1 3]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [contrT_permT, permT_permT]
    enter [2, 2]
  rw [permT_permT, permT_permT, permT_permT, permT_permT]
  apply permT_congr
  · decide
  · simp

end complexLorentzTensor

end
