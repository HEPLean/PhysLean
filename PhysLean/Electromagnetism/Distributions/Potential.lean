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
/-!

# The electromagnetic potential for distributions

## i. Overview

In this file we make the basic definitions of the electromagnetic potential,
the field strength tensor, the electric and magnetic fields, and the
Lagrangian gradient in the context of distributions.

Note that all of these quantities depend linearly on the electromagnetic potential,
allowing them to be defined in the context of distributions.

Unlike in the function case, many of the properties here can be defined as linear maps,
due to the no need to check things like differentiability.

## ii. Key results

- `ElectromagneticPotentialD` : The type of electromagnetic potentials as distributions.
- `ElectromagneticPotentialD.scalarPotential` : The scalar potential as a distribution.
- `ElectromagneticPotentialD.vectorPotential` : The vector potential as a distribution.
- `ElectromagneticPotentialD.electricField` : The electric field as a distribution.
- `ElectromagneticPotentialD.magneticField` : The magnetic field as a distribution.
- `LorentzCurrentDensityD` : The type of Lorentz current densities as distributions.
- `ElectromagneticPotentialD.gradLagrangian` : The variational gradient of the
  electromagnetic Lagrangian as a distribution.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. The components of the electromagnetic potential
- B. The field strength tensor matrix
  - B.1. Diagonal of the field strength matrix
  - B.2. Antisymmetry of the field strength matrix
- C. The scalar and vector potentials
  - C.1. The scalar potential
  - C.2. The vector potential
- D. The electric and magnetic fields
  - D.1. Linear map to components
  - D.2. The electric field in d-dimensions
    - D.2.1. The electric field in terms of the field strength matrix
    - D.2.2. The first column of the field strength matrix in terms of the electric field
    - D.2.3. The first row of the field strength matrix in terms of the electric field
  - D.3. The magnetic field in 3-dimensions
- E. The Lorentz current density
  - E.1. The components of the Lorentz current density
- F. The Lagrangian variational gradient
  - F.1. The variational gradient in 1-dimension

## iv. References

-/
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

/-!

### A.1. The components of the electromagnetic potential
-/

/-- The linear map from an electromagnetic potential to its componenets. -/
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

open SchwartzMap

lemma toComponents_symm_apply {d : ℕ} (A : ((Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ))
    (μ : Fin 1 ⊕ Fin d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (toComponents.symm A) ε μ = A μ ε := by rfl
/-!

## B. The field strength tensor matrix

-/

/-- The field strength matrix with indices `F^μ^ν`. -/
noncomputable def fieldStrengthMatrix {d : ℕ} :
    ElectromagneticPotentialD d →ₗ[ℝ]
    ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ) where
  toFun A := fun (μ, ν) => η μ μ • SpaceTime.derivD μ (A.toComponents ν) -
    η ν ν • SpaceTime.derivD ν (A.toComponents μ)
  map_add' A1 A2 := by
    ext μν
    match μν with
    | (μ, ν) =>
    simp only [map_add, Pi.add_apply, smul_add, ContinuousLinearMap.coe_sub', Pi.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' a A := by
    ext μν
    match μν with
    | (μ, ν) =>
    simp only [map_smul, Pi.smul_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
      Pi.sub_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-!

### B.1. Diagonal of the field strength matrix

-/

@[simp]
lemma fieldStrengthMatrix_same_same {d : ℕ} (A : ElectromagneticPotentialD d) (μ : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix (μ, μ) = 0 := by
  ext ε
  simp [fieldStrengthMatrix]

/-!

### B.2. Antisymmetry of the field strength matrix

-/

lemma fieldStrengthMatrix_antisymm {d : ℕ} (A : ElectromagneticPotentialD d)
    (μ ν : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix (μ, ν) = - A.fieldStrengthMatrix (ν, μ) := by
  ext ε
  simp [fieldStrengthMatrix]
/-!

## C. The scalar and vector potentials

-/

/-!

### C.1. The scalar potential

-/

/-- The scalar potential from an electromagnetic potential which is a
  distribution. -/
noncomputable def scalarPotential {d} :
    ElectromagneticPotentialD d →ₗ[ℝ] (Time × Space d) →d[ℝ] ℝ where
  toFun A := timeSliceD <| A.toComponents (Sum.inl 0)
  map_add' A1 A2 := by
    ext ε
    simp
  map_smul' a A := by
    ext ε
    simp

/-!

### C.2. The vector potential

-/

/-- The vector potential from an electromagnetic potential which is a
  distribution. -/
noncomputable def vectorPotential {d}:
    ElectromagneticPotentialD d →ₗ[ℝ] (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun A := {
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
    }
  map_add' A1 A2 := by
    ext κ i
    simp
  map_smul' a A := by
    ext κ i
    simp

/-!

## D. The electric and magnetic fields

-/

/-!

### D.1. Linear map to components

-/

/-- The linear map taking a distribution on Euclidean space to its componenets. -/
noncomputable def toComponentsEuclidean {d : ℕ} :
    ((Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ]
    (Fin d → (Time × Space d) →d[ℝ] ℝ) where
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
lemma toComponentsEuclidean_apply {d : ℕ} (E : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin d) (ε : 𝓢(Time × Space d, ℝ)) :
    (toComponentsEuclidean E i) ε = E ε i := by rfl

/-!

### D.2. The electric field in d-dimensions

-/

/-- The electric field associated with a electromagnetic potential which is a distribution. -/
noncomputable def electricField {d} :
    ElectromagneticPotentialD d →ₗ[ℝ] (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun A :=
    - Space.spaceGradD (A.scalarPotential) - Space.timeDerivD (A.vectorPotential)
  map_add' A1 A2 := by
    ext κ i
    simp only [map_add, neg_add_rev, ContinuousLinearMap.coe_sub', Pi.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, PiLp.sub_apply, PiLp.add_apply,
      PiLp.neg_apply]
    ring
  map_smul' a A := by
    ext κ i
    simp only [map_smul, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul', Pi.sub_apply,
      ContinuousLinearMap.neg_apply, Pi.smul_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-!

#### D.2.1. The electric field in terms of the field strength matrix

-/

lemma electricField_fieldStrengthMatrix {d} {A : ElectromagneticPotentialD d} (i : Fin d) :
    toComponentsEuclidean A.electricField i =
    timeSliceD (A.fieldStrengthMatrix (Sum.inr i, Sum.inl 0)) := by
  rw [electricField]
  simp [fieldStrengthMatrix]
  ext ε
  simp [timeSliceD_derivD_inl, timeSliceD_derivD_inr, Space.spaceGradD_apply]
  ring_nf
  rfl

/-!

#### D.2.2. The first column of the field strength matrix in terms of the electric field

-/

lemma fieldStrengthMatrix_col_eq_electricField {d} {A : ElectromagneticPotentialD d}
    (i : Fin d) :
    (A.fieldStrengthMatrix (Sum.inr i, Sum.inl 0)) =
    timeSliceD.symm (toComponentsEuclidean A.electricField i) := by
  rw [electricField_fieldStrengthMatrix]
  simp

/-!

#### D.2.3. The first row of the field strength matrix in terms of the electric field

-/

lemma fieldStrengthMatrix_row_eq_electricField {d} {A : ElectromagneticPotentialD d}
    (i : Fin d) :
    (A.fieldStrengthMatrix (Sum.inl 0, Sum.inr i)) =
    - timeSliceD.symm (toComponentsEuclidean A.electricField i) := by
  rw [fieldStrengthMatrix_antisymm, electricField_fieldStrengthMatrix]
  simp

/-!

### D.3. The magnetic field in 3-dimensions

-/

/-- The magnetic field associated with a electromagnetic potential in 3 dimensions. -/
noncomputable def magneticField :
    ElectromagneticPotentialD 3 →ₗ[ℝ] (Time × Space 3) →d[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun A := Space.spaceCurlD A.vectorPotential
  map_add' A1 A2 := by
    ext κ i
    simp
  map_smul' a A := by
    ext κ i
    simp

end ElectromagneticPotentialD

/-!

## E. The Lorentz current density

-/

/-- The Lorentz current density (aka four-current) as a distribution. -/
abbrev LorentzCurrentDensityD (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace LorentzCurrentDensityD

/-!

### E.1. The components of the Lorentz current density

-/

/-- The linear map taking a Lorentz current density to its componenets. -/
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
open SchwartzMap

lemma toComponents_symm_apply {d : ℕ} (J : ((Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ))
    (μ : Fin 1 ⊕ Fin d) (ε : 𝓢(SpaceTime d, ℝ)) :
    (toComponents.symm J) ε μ = J μ ε := by rfl

end LorentzCurrentDensityD

namespace ElectromagneticPotentialD

open minkowskiMatrix

/-!

## F. The Lagrangian variational gradient

The variational gradient of the Lagrangian density with respect to the electromagnetic potential
which is a distribution. We do not prove this is correct, the proof
is done for the function case.

We take the definition to be:

```
∑ ν, (η ν ν • (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)
  • Lorentz.Vector.basis ν)
```

which matches the result of the calcultation from the function case.
-/

/-- The variational gradient of the lagrangian for an electromagnetic potential
  which is a distribution. This is defined nor proved for distributions. -/
noncomputable def gradLagrangian {d : ℕ} (A : ElectromagneticPotentialD d)
    (J : LorentzCurrentDensityD d) :
    (Fin 1 ⊕ Fin d) → (SpaceTime d) →d[ℝ] ℝ := fun ν =>
  η ν ν • (∑ μ, SpaceTime.derivD μ (A.fieldStrengthMatrix (μ, ν)) - J.toComponents ν)

/-!

### F.1. Gauss's law


-/

lemma gradLagrangian_gauss_law {d} (A : ElectromagneticPotentialD d)
    (J : LorentzCurrentDensityD d) :
    A.gradLagrangian J (Sum.inl 0) = SpaceTime.timeSliceD.symm
      (Space.spaceDivD A.electricField) - J.toComponents (Sum.inl 0) := by
  simp only [gradLagrangian, Fin.isValue, inl_0_inl_0, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, fieldStrengthMatrix_same_same, map_zero, zero_add,
    one_smul, sub_left_inj]
  ext ε
  simp only [Fin.isValue, fieldStrengthMatrix_col_eq_electricField,
    SpaceTime.timeSliceD_symm_derivD_inr, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    SpaceTime.timeSliceD_symm_apply, Space.spaceDivD_apply_eq_sum_spaceDerivD]
  rfl

/-!

### F.2. The variational gradient in 1-dimension

We simplify the variational gradient in 1-dimension.

-/

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
    rw [gradLagrangian_gauss_law]
  | Sum.inr 0 =>
    simp [gradLagrangian]
    rw [fieldStrengthMatrix_row_eq_electricField]
    simp only [Fin.isValue, map_neg, sub_neg_eq_add, add_right_inj]
    rw [SpaceTime.timeSliceD_symm_derivD_inl]
    have h1 : (Space.timeDerivD (toComponentsEuclidean A.electricField 0))
      = toComponentsEuclidean (Space.timeDerivD (A.electricField)) 0:= by
      ext ε
      simp [Space.timeDerivD_apply, Distribution.fderivD_apply,
        Distribution.fderivD_apply]
    rw [h1]

end ElectromagneticPotentialD

end Electromagnetism
