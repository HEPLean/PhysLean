/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
import PhysLean.SpaceAndTime.SpaceTime.Distributions
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
import PhysLean.SpaceAndTime.Space.Distributions
namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/

/-- The electricomagnetic potential is a tensor `A^μ`. -/
noncomputable abbrev ElectromagneticPotentialD (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace ElectromagneticPotentialD

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open PiTensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one


noncomputable def toComponents {d : ℕ} :
    ElectromagneticPotentialD d ≃ₗ[ℝ] ((Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ) where
  toFun A := fun μ => {
    toFun := fun ε => A ε μ
    map_add' := by
      intro ε1 ε2
      simp
    map_smul' := by
      intro c ε
      simp
    cont := by fun_prop}
  invFun A := {
    toFun := fun ε μ => A μ ε
    map_add' := by
      intro ε1 ε2
      funext μ
      simp
    map_smul' := by
      intro c ε
      funext μ
      simp
    cont := by fun_prop}
  left_inv := by
    intro A
    ext ε
    simp
  right_inv := by
    intro A
    ext μ ε
    simp
  map_add' := by
    intro A1 A2
    ext μ ε
    simp
  map_smul' := by
    intro c A
    ext μ ε
    simp

noncomputable def fieldStrengthMatrix {d : ℕ} (A : ElectromagneticPotentialD d) :
   (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ :=
  fun (μ, ν) => η μ μ • SpaceTime.derivD μ (A.toComponents ν) -
    η ν ν • SpaceTime.derivD ν (A.toComponents μ)

@[simp]
lemma fieldStrengthMatrix_same_same {d : ℕ} (A : ElectromagneticPotentialD d) (μ : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix (μ, μ) = 0 := by
  ext ε
  simp [fieldStrengthMatrix]

lemma fieldStrengthMatrix_antisymm {d : ℕ} (A : ElectromagneticPotentialD d)
    (μ ν : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix (μ, ν) = - A.fieldStrengthMatrix (ν, μ) := by
  ext ε
  simp [fieldStrengthMatrix]

/-- The scalar potential from an electromagnetic potential which is a
  distribution. -/
noncomputable def scalarPotential {d} (A : ElectromagneticPotentialD d) :
  (Time × Space d) →d[ℝ] ℝ := timeSliceD <| A.toComponents (Sum.inl 0)

/-- The vector potential from an electromagnetic potential which is a
  distribution. -/
noncomputable def vectorPotential {d} (A : ElectromagneticPotentialD d) :
    (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun := fun κ i => (timeSliceD <| A.toComponents (Sum.inr i)) κ
  map_add' := by
    intro κ1 κ2
    funext i
    simp
  map_smul' := by
    intro c κ
    funext i
    simp
  cont := by fun_prop



noncomputable def toComponentsEuclidean {d : ℕ} :
    ((Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ]
    (Fin d→  (Time × Space d) →d[ℝ] ℝ) where
  toFun J := fun μ => {
    toFun := fun ε => J ε μ
    map_add' := by
      intro ε1 ε2
      simp
    map_smul' := by
      intro c ε
      simp
    cont := by fun_prop}
  invFun J := {
    toFun := fun ε μ => J μ ε
    map_add' := by
      intro ε1 ε2
      funext μ
      simp
    map_smul' := by
      intro c ε
      funext μ
      simp
    cont := by fun_prop}
  left_inv := by
    intro J
    ext ε
    simp
  right_inv := by
    intro J
    ext μ ε
    simp
  map_add' := by
    intro J1 J2
    ext μ ε
    simp
  map_smul' := by
    intro c J
    ext μ ε
    simp
open SchwartzMap
@[simp]
lemma toComponentsEuclidean_apply  {d : ℕ}  (E : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin d) (ε : 𝓢(Time × Space d, ℝ)) :
    (toComponentsEuclidean E i) ε = E ε i := by rfl

noncomputable def electricField {d} (A : ElectromagneticPotentialD d) :
    (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) :=
  - Space.spaceGradD (A.scalarPotential) - Space.timeDerivD (A.vectorPotential)

lemma electricField_fieldStrengthMatrix {d} {A : ElectromagneticPotentialD d} (i : Fin d) :
    toComponentsEuclidean A.electricField i =
    timeSliceD (A.fieldStrengthMatrix (Sum.inr i, Sum.inl 0))  := by
  rw [electricField]
  simp [fieldStrengthMatrix]
  ext ε
  simp [timeSliceD_derivD_inl, timeSliceD_derivD_inr, Space.spaceGradD_apply]
  ring_nf
  rfl

lemma fieldStrengthMatrix_col_eq_electricField {d} {A : ElectromagneticPotentialD d}
    (i : Fin d) :
    (A.fieldStrengthMatrix (Sum.inr i, Sum.inl 0)) =
    timeSliceD.symm (toComponentsEuclidean A.electricField i) := by
  rw [electricField_fieldStrengthMatrix]
  simp

lemma fieldStrengthMatrix_row_eq_electricField {d} {A : ElectromagneticPotentialD d}
    (i : Fin d) :
    (A.fieldStrengthMatrix (Sum.inl 0, Sum.inr i)) =
    - timeSliceD.symm (toComponentsEuclidean A.electricField i) := by
  rw [fieldStrengthMatrix_antisymm, electricField_fieldStrengthMatrix]
  simp

noncomputable def magneticField (A : ElectromagneticPotentialD 3) :
    (Time × Space 3) →d[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Space.spaceCurlD A.vectorPotential


end ElectromagneticPotentialD

abbrev LorentzCurrentDensityD (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace LorentzCurrentDensityD

noncomputable def toComponents {d : ℕ} :
    LorentzCurrentDensityD d ≃ₗ[ℝ] ((Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ) where
  toFun J := fun μ => {
    toFun := fun ε => J ε μ
    map_add' := by
      intro ε1 ε2
      simp
    map_smul' := by
      intro c ε
      simp
    cont := by fun_prop}
  invFun J := {
    toFun := fun ε μ => J μ ε
    map_add' := by
      intro ε1 ε2
      funext μ
      simp
    map_smul' := by
      intro c ε
      funext μ
      simp
    cont := by fun_prop}
  left_inv := by
    intro J
    ext ε
    simp
  right_inv := by
    intro J
    ext μ ε
    simp
  map_add' := by
    intro J1 J2
    ext μ ε
    simp
  map_smul' := by
    intro c J
    ext μ ε
    simp

end LorentzCurrentDensityD

namespace ElectromagneticPotentialD


open minkowskiMatrix
/-
fun x => ∑ ν,
      (η ν ν • (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)
      • Lorentz.Vector.basis ν)
-/

noncomputable def gradLagrangian {d : ℕ} (A : ElectromagneticPotentialD d)
    (J : LorentzCurrentDensityD d) :
    (Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ := fun ν =>
  η ν ν • (∑ μ, SpaceTime.derivD μ (A.fieldStrengthMatrix (μ, ν)) - J.toComponents ν)

lemma gradLagrangian_one_dimension_electricField (A : ElectromagneticPotentialD 1)
    (J : LorentzCurrentDensityD 1) :
    A.gradLagrangian J = fun μ =>
      match μ with
      | Sum.inl 0 => SpaceTime.timeSliceD.symm
          (Space.spaceDivD A.electricField) - J.toComponents (Sum.inl 0)
      | Sum.inr 0 => J.toComponents (Sum.inr 0) +
        SpaceTime.timeSliceD.symm
        (toComponentsEuclidean (Space.timeDerivD A.electricField) 0) := by
  funext μ
  match μ with
  | Sum.inl 0 =>
    simp [gradLagrangian]
    rw [fieldStrengthMatrix_col_eq_electricField]
    simp [SpaceTime.timeSliceD_symm_derivD_inr]
    have h1 : ((Space.spaceDerivD 0) (toComponentsEuclidean A.electricField 0)) =
      Space.spaceDivD (A.electricField) := by
      ext ε
      rw [Space.spaceDivD_apply_eq_sum_spaceDerivD]
      simp
      rw [Space.spaceDerivD_apply, Space.spaceDerivD_apply, Distribution.fderivD_apply,
        Distribution.fderivD_apply]
      simp
    rw [h1]
  | Sum.inr 0 =>
    simp [gradLagrangian]
    rw [fieldStrengthMatrix_row_eq_electricField]
    simp
    rw [SpaceTime.timeSliceD_symm_derivD_inl]
    have h1 : (Space.timeDerivD (toComponentsEuclidean A.electricField 0))
      = toComponentsEuclidean (Space.timeDerivD (A.electricField)) 0:= by
      ext ε
      simp [Space.timeDerivD_apply,  Distribution.fderivD_apply,
        Distribution.fderivD_apply]
    rw [h1]

end ElectromagneticPotentialD

end Electromagnetism
