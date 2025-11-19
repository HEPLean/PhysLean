/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Matrix.Normed
import PhysLean.Particles.StandardModel.HiggsBoson.Basic
import Mathlib.Analysis.Matrix.Order
/-!

# Gauge orbits for the 2HDM

The main reference for material in this section is https://arxiv.org/pdf/hep-ph/0605184.

-/

namespace TwoHDM

open StandardModel
open ComplexConjugate
open HiggsField
open Manifold
open Matrix
open Complex
open SpaceTime

noncomputable section
open InnerProductSpace

/-- For two Higgs fields `Φ₁` and `Φ₂`, the map from space time to 2 x 2 complex matrices
  defined by `((Φ₁^†Φ₁, Φ₂^†Φ₁), (Φ₁^†Φ₂, Φ₂^†Φ₂))`. -/
def prodMatrix (Φ1 Φ2 : HiggsField) (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪Φ1, Φ1⟫_(SpaceTime → ℂ) x, ⟪Φ2, Φ1⟫_(SpaceTime → ℂ) x;
    ⟪Φ1, Φ2⟫_(SpaceTime → ℂ) x, ⟪Φ2, Φ2⟫_(SpaceTime → ℂ) x]

/-- The 2 x 2 complex matrices made up of components of the two Higgs fields. -/
def fieldCompMatrix (Φ1 Φ2 : HiggsField) (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Φ1 x 0, Φ1 x 1; Φ2 x 0, Φ2 x 1]

/-- The matrix `prodMatrix Φ1 Φ2 x` is equal to the square of `fieldCompMatrix Φ1 Φ2 x`. -/
lemma prodMatrix_eq_fieldCompMatrix_sq (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    prodMatrix Φ1 Φ2 x = fieldCompMatrix Φ1 Φ2 x * (fieldCompMatrix Φ1 Φ2 x).conjTranspose := by
  rw [fieldCompMatrix]
  trans !![Φ1 x 0, Φ1 x 1; Φ2 x 0, Φ2 x 1] *
    !![conj (Φ1 x 0), conj (Φ2 x 0); conj (Φ1 x 1), conj (Φ2 x 1)]
  · rw [Matrix.mul_fin_two, prodMatrix, inner_expand_conj, inner_expand_conj, inner_expand_conj,
      inner_expand_conj]
    funext i j
    fin_cases i <;> fin_cases j <;> ring_nf
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- An instance of `PartialOrder` on `ℂ` defined through `Complex.partialOrder`. -/
local instance : PartialOrder ℂ := Complex.partialOrder

/-- An instance of `NormedAddCommGroup` on `Matrix (Fin 2) (Fin 2) ℂ` defined through
  `Matrix.normedAddCommGroup`. -/
local instance : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.normedAddCommGroup

/-- An instance of `NormedSpace` on `Matrix (Fin 2) (Fin 2) ℂ` defined through
  `Matrix.normedSpace`. -/
local instance : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace

open Matrix
open MatrixOrder

/-- The matrix `prodMatrix` is positive semi-definite. -/
lemma prodMatrix_posSemiDef (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    (prodMatrix Φ1 Φ2 x).PosSemidef := by
  rw [prodMatrix_eq_fieldCompMatrix_sq Φ1 Φ2 x, ← nonneg_iff_posSemidef]
  apply (CStarAlgebra.nonneg_iff_eq_mul_star_self (A := Matrix (Fin 2) (Fin 2) ℂ)).mpr
  use (fieldCompMatrix Φ1 Φ2 x)
  rfl

/-- The matrix `prodMatrix` is hermitian. -/
lemma prodMatrix_hermitian (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    (prodMatrix Φ1 Φ2 x).IsHermitian := (prodMatrix_posSemiDef Φ1 Φ2 x).isHermitian

/-- The map `prodMatrix` is a smooth function on spacetime. -/
lemma prodMatrix_smooth (Φ1 Φ2 : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) ⊤ (prodMatrix Φ1 Φ2) := by
  rw [show 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) = modelWithCornersSelf ℝ (Fin 2 → Fin 2 → ℂ) from rfl,
    contMDiff_pi_space]
  intro i
  rw [contMDiff_pi_space]
  intro j
  fin_cases i <;> fin_cases j <;>
    simpa only [prodMatrix, Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero,
      empty_val', cons_val_fin_one] using inner_smooth _ _

/-- The map `prodMatrix` is invariant under the simultaneous action of `gaugeAction` on the two
Higgs fields. -/
informal_lemma prodMatrix_invariant where
  deps := [``prodMatrix, ``gaugeAction]
  tag := "6V2VS"

/-- Given any smooth map `f` from spacetime to 2-by-2 complex matrices landing on positive
semi-definite matrices, there exist smooth Higgs fields `Φ1` and `Φ2` such that `f` is equal to
`prodMatrix Φ1 Φ2`.

See https://arxiv.org/pdf/hep-ph/0605184
-/
informal_lemma prodMatrix_to_higgsField where
  deps := [``prodMatrix, ``HiggsField, ``prodMatrix_smooth]
  tag := "6V2V2"

end
end TwoHDM
