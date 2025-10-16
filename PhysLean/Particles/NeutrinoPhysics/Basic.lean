/-
Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prabhoda Chandra Sarjapur
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Polyrith

/-!
# The PMNS matrix

The definition the PMNS matrix, which describes neutrino oscillations as part of U(3).

-/
open Matrix Complex

noncomputable section

/-- diagonal phase matrix from a real-valued function on indices -/
@[simp]
def diagPhase (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  λ i j => if i = j then cexp (I * θ i) else 0

/-- lemma stating that the diagonal phase matrix with all zeros is the identity matrix -/
lemma diagPhase_zero:
    diagPhase (fun _ : Fin 3 => 0) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp []

/-- lemma stating that the Hermitian conjugate of diagPhase diag(+iθ_i)
is just diagPhase with entries diag(-iθ_i) -/
lemma diagPhase_star (θ : Fin 3 → ℝ) :
    (diagPhase θ )ᴴ = diagPhase (- θ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [diagPhase, Matrix.conjTranspose_apply, ← exp_conj]

/-- lemma stating that multiplying two phase matrices is equivalent to adding the phases -/
lemma diagPhase_mul (θ φ : Fin 3 → ℝ) :
    diagPhase θ * diagPhase φ = diagPhase (θ + φ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [diagPhase, Matrix.mul_apply, ← exp_add, mul_add]

/-- diagonal phase matrix diag(iθ_i) is part of the unitary group -/
@[simp]
def diagPhase_unitary (θ : Fin 3 → ℝ) : unitaryGroup (Fin 3) ℂ :=
    ⟨diagPhase θ,
    by
    rw[Matrix.mem_unitaryGroup_iff]
    change _ * (diagPhase θ)ᴴ = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagPhase,
    Matrix.mul_apply,
    Matrix.conjTranspose_apply,
    ← exp_conj,
    ← exp_add]
    ⟩

/-- The Lepton phase shift matrix as a `3×3` complex matrix, given three reals `a b c`.
This dictates the phase shift freedom of the charged lepton sector.
-/
def leptonPhaseShift (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then a else if i = 1 then b else c)

/-- The neutrino phase shift matrix as a `3×3` complex matrix, given three reals `d e f`.
This dictates the phase shift freedom of the neutrino sector (If neutrinos are Dirac).
-/
def neutrinoPhaseShift (d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then d else if i = 1 then e else f)

/-- If neutrinos are Majorana particles, then the neutrino phase shift matrix is physical,
and cannot be absorbed into the definition of the neutrino fields.
-/
def majoranaPhaseMatrix (α1 α2 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then 0 else if i = 1 then α1/2 else α2/2)
