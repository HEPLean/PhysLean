/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.ComplexTensor.Metrics.Lemmas
import PhysLean.Relativity.Tensors.Tree.Elab
import PhysLean.Relativity.Lorentz.PauliMatrices.AsTensor
/-!

## Pauli matrices as complex Lorentz tensors

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
noncomputable section

namespace PauliMatrix
open Fermion
open complexLorentzTensor
/-!

## Definitions.

-/
open TensorSpecies
open Tensor

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ^α^{dot β}`. -/
abbrev pauliContr : ℂT[.up, .upL, .upR] := fromConstTriple PauliMatrix.asConsTensor

@[inherit_doc pauliContr]
scoped[PauliMatrix] notation "σ^^^" => PauliMatrix.pauliContr

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
abbrev pauliCo : ℂT[.down, .upL, .upR] :=
  permT id (PermCond.auto) {η' | μ ν ⊗ σ^^^ | ν α β}ᵀ

@[inherit_doc pauliCo]
scoped[PauliMatrix] notation "σ_^^" => PauliMatrix.pauliCo

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_{dot β}_α`. -/
abbrev pauliCoDown : ℂT[.down, .downR, .downL] :=
  permT id (PermCond.auto) {σ_^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ

@[inherit_doc pauliCoDown]
scoped[PauliMatrix] notation "σ___" => PauliMatrix.pauliCoDown

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_{dot β}_α`. -/
abbrev pauliContrDown : ℂT[.up, .downR, .downL] :=
    permT id (PermCond.auto) {pauliContr | μ α β ⊗ εR' | β β' ⊗ εL' | α α'}ᵀ

@[inherit_doc pauliContrDown]
scoped[PauliMatrix] notation "σ^__" => PauliMatrix.pauliContrDown

/-!

## Different forms
-/
open Lorentz
lemma pauliContr_eq_fromConstTriple : σ^^^ = fromConstTriple PauliMatrix.asConsTensor := by
  rfl

lemma pauliContr_eq_fromTripleT : σ^^^ = fromTripleT PauliMatrix.asTensor := by
  rw [pauliContr_eq_fromConstTriple, fromConstTriple]
  erw [PauliMatrix.asConsTensor_apply_one]


lemma pauliContr_eq_basis : pauliContr =
    Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [pauliContr_eq_fromTripleT]
  rw [PauliMatrix.asTensor_expand]
  simp

/-!

## Group actions

-/

/-- The tensor `pauliContr` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliContr (g : SL(2,ℂ)) : g • pauliContr = pauliContr := by
  rw [pauliContr_eq_fromConstTriple]
  rw [actionT_fromConstTriple]

/-- The tensor `pauliCo` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliCo (g : SL(2,ℂ)) : g • pauliCo = pauliCo := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliContr, actionT_coMetric]

/-- The tensor `pauliCoDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliCoDown (g : SL(2,ℂ)) : g • pauliCoDown = pauliCoDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliCo, actionT_altLeftMetric, actionT_altRightMetric]

/-- The tensor `pauliContrDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_pauliContrDown (g : SL(2,ℂ)) : g • pauliContrDown = pauliContrDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [actionT_pauliContr, actionT_altLeftMetric, actionT_altRightMetric]

end PauliMatrix
