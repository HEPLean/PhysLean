/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.PauliMatrices.Basic
/-!

## Bispinors

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
open TensorTree
open OverColor.Discrete
open Fermion
noncomputable section
namespace complexLorentzTensor
open Lorentz
open PauliMatrix
/-!

## Definitions

-/

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : ℂT[.up]) :=
  {pauliCo | μ α β ⊗ p | μ}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : ℂT[.up]) :=
  {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ.tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : ℂT[.down]) :=
  {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : ℂT[.down]) :=
  {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ.tensor

/-!

## Tensor nodes

-/

/-- The definitional tensor node relation for `contrBispinorUp`. -/
lemma tensorNode_contrBispinorUp (p : ℂT[.up]) :
    {contrBispinorUp p | α β}ᵀ.tensor = {pauliCo | μ α β ⊗ p | μ}ᵀ.tensor := by
  rw [contrBispinorUp, tensorNode_tensor]

/-- The definitional tensor node relation for `contrBispinorDown`. -/
lemma tensorNode_contrBispinorDown (p : ℂT[.up]) :
    {contrBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ.tensor := by
  rw [contrBispinorDown, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorUp`. -/
lemma tensorNode_coBispinorUp (p : ℂT[.down]) :
    {coBispinorUp p | α β}ᵀ.tensor = {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor := by
  rw [coBispinorUp, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorDown`. -/
lemma tensorNode_coBispinorDown (p : ℂT[.down]) :
    {coBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ.tensor := by
  rw [coBispinorDown, tensorNode_tensor]

/-!

## Basic equalities.

-/

/-- `{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ contrBispinorDown p | α' β' }ᵀ`.

Proof: expand `contrBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma contrBispinorUp_eq_metric_contr_contrBispinorDown where
  deps := [``contrBispinorUp, ``contrBispinorDown, ``leftMetric, ``rightMetric]

/-- `{coBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ coBispinorDown p | α' β' }ᵀ`.

proof: expand `coBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma coBispinorUp_eq_metric_contr_coBispinorDown where
  deps := [``coBispinorUp, ``coBispinorDown, ``leftMetric, ``rightMetric]

lemma contrBispinorDown_expand (p : ℂT[.up]) :
    {contrBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗
    (pauliCo | μ α β ⊗ p | μ)}ᵀ.tensor := by
  rw [tensorNode_contrBispinorDown p]
  rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_contrBispinorUp p]

lemma coBispinorDown_expand (p : ℂT[.down]) :
    {coBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗ (pauliContr | μ α β ⊗ p | μ)}ᵀ.tensor := by
  rw [tensorNode_coBispinorDown p]
  rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_coBispinorUp p]

end complexLorentzTensor
end
