/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Mathematics.SO3.Basic
/-!
# Rotations

This file describes the embedding of `SO(3)` into `LorentzGroup 3`.

-/
TODO "6VZIS" "Generalize the inclusion of rotations into LorentzGroup to arbitrary dimension."
noncomputable section

namespace LorentzGroup
open GroupTheory

/-- Given a element of `SO(3)` the matrix corresponding to a space-time rotation. -/
@[simp]
def SO3ToMatrix (A : SO(3)) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  (Matrix.fromBlocks 1 0 0 A.1)

lemma SO3ToMatrix_in_LorentzGroup (A : SO(3)) : SO3ToMatrix A ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_dual_mul_self]
  simp only [minkowskiMatrix.dual, minkowskiMatrix.as_block, SO3ToMatrix,
    Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.mul_one,
    neg_mul, one_mul, zero_add, Matrix.mul_neg, neg_zero, mul_neg, neg_neg,
    Matrix.mul_eq_one_comm.mpr A.2.2, Matrix.fromBlocks_one]

lemma SO3ToMatrix_injective : Function.Injective SO3ToMatrix := fun _ _ h =>
  Subtype.eq (congrArg (Matrix.toBlocks₂₂ : _ → Matrix (Fin 3) (Fin 3) ℝ) h)

/-- Given a element of `SO(3)` the element of the Lorentz group corresponding to a
space-time rotation. -/
def SO3ToLorentz : SO(3) →* LorentzGroup 3 where
  toFun A := ⟨SO3ToMatrix A, SO3ToMatrix_in_LorentzGroup A⟩
  map_one' := Subtype.eq <| by
    simp only [SO3ToMatrix, SO3Group_one_coe, Matrix.fromBlocks_one, lorentzGroupIsGroup_one_coe]
  map_mul' A B := Subtype.eq <| by
    simp only [SO3ToMatrix, SO3Group_mul_coe, lorentzGroupIsGroup_mul_coe,
      Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul,
      Matrix.mul_one, zero_add]

end LorentzGroup

end
