/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Potential
import PhysLean.Relativity.LorentzGroup.Boosts.Basic
import PhysLean.SpaceAndTime.SpaceTime.Boosts
/-!

# The Lorentz action on the electric and magnetic fields.

## i. Overview

We find the transformations of the electric and magnetic fields under a Lorentz boost
in the `x` direction.

## ii. Key results

- `electricField_apply_x_boost` : The transformation of the electric field under a
  boost in the `x` direction.
- `magneticField_apply_x_boost` : The transformation of the magnetic field under a
  boost in the `x` direction.

## iii. Table of contents

- A. Boost of the electric field
- B. Boost of the magnetic field

## iv. References

See e.g.
- https://en.wikipedia.org/wiki/Classical_electromagnetism_and_special_relativity

-/

namespace Electromagnetism

namespace ElectromagneticPotential
open LorentzGroup

/-!

## A. Boost of the electric field

The electric field `E` in a frame `F` following a boost in the `x` direction with speed `β`
with `|β| < 1` compared to a frame `F'` at a point `x := (t, x, y, z)` is related to the
electric `E'` and magnetic fields `B'` in `F'` at the point
`x' := (γ (t + β x), γ (x + β t), y, z)`
(corresponding to the same space-time point) by:

- `E_x x = E'_x x'`,
- `E_y x = γ (E'_y x' - β B_z x')`,
- `E_z x = γ (E'_z x' + β B_y x')`.

-/

lemma electricField_apply_x_boost (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential) (hA : Differentiable ℝ A) (t : Time) (x : Space) :
    let Λ := LorentzGroup.boost (d := 3) 0 β hβ
    let t' : Time := γ β * (t.val + β * x 0)
    let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
    electricField (fun x => Λ • A (Λ⁻¹ • x)) t x =
    fun | 0 => A.electricField t' x' 0
        | 1 => γ β * (A.electricField t' x' 1 - β * A.magneticField t' x' 2)
        | 2 =>  γ β * (A.electricField t' x' 2 + β * A.magneticField t' x' 1) := by
  dsimp
  let t' : Time := γ β * (t.val + β * x 0)
  let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
  have t_trans : (SpaceTime.toTimeAndSpace ((boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).1
      = t' := by
    rw [boost_inverse, SpaceTime.boost_x_smul]
    simp [SpaceTime.toTimeAndSpace, SpaceTime.time, Lorentz.Vector.timeComponent]
    rfl
  have x_trans : (SpaceTime.toTimeAndSpace ((boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).2
      = x' := by
    rw [boost_inverse, SpaceTime.boost_x_smul]
    simp [SpaceTime.toTimeAndSpace, SpaceTime.time, Lorentz.Vector.timeComponent]
    funext j
    fin_cases j <;> simp <;> rfl
  let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
  funext i
  rw [electricField_eq_fieldStrengthMatrix, fieldStrengthMatrix_equivariant]
  fin_cases i
  · simp [Fin.sum_univ_three]
    rw [LorentzGroup.boost_inl_0_inr_other _ (by decide)]
    simp only [Fin.isValue, zero_mul, neg_zero, add_zero, zero_add]
    rw [LorentzGroup.boost_inl_0_inr_other _ (by decide)]
    simp only [Fin.isValue, zero_mul, neg_zero, add_zero, zero_add]
    rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, zero_mul, zero_add, neg_zero]
    rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime,
      fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
    simp
    trans ((LorentzGroup.γ β) ^ 2 * (1- β^2)) * A.electricField
          (SpaceTime.toTimeAndSpace ((LorentzGroup.boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).1
          (SpaceTime.toTimeAndSpace ((LorentzGroup.boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).2 0
    · ring
    have h1 : ((LorentzGroup.γ β) ^ 2 * (1- β^2)) = 1 := by
      rw [LorentzGroup.γ_sq β hβ]
      field_simp
    rw [h1]
    simp
    rw [x_trans, t_trans]
    · exact hA
    · exact hA
  · simp [Fin.sum_univ_three]
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inl_0_inr_other _ (by decide),]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime,
      fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
    simp
    trans -(γ β * β *A.magneticField t' x' 2) +
      γ β * A.electricField t' x' 1
    · rw [x_trans, t_trans]
    · ring
    · exact hA
    · exact hA
  · simp [Fin.sum_univ_three]
    rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide),
      LorentzGroup.boost_inr_other_inr _ (by decide)]
    simp
    rw [ LorentzGroup.boost_inl_0_inr_other _ (by decide)]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime,
      fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
    simp
    trans γ β * β *
      A.magneticField t' x' 1 +
      γ β *
      A.electricField t' x' 2
    · rw [x_trans, t_trans]
    · ring
    · exact hA
    · exact hA
  · exact hA
  · apply Differentiable.comp
    · change  Differentiable ℝ (Lorentz.Vector.actionCLM (boost 0 β hβ))
      exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM (boost 0 β hβ))
    · apply Differentiable.comp
      · exact hA
      · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM (boost 0 β hβ)⁻¹)

/-!

## B. Boost of the magnetic field

The magnetic field `B` in a frame `F` following a boost in the `x` direction with speed `β`
with `|β| < 1` compared to a frame `F'` at a point `x := (t, x, y, z)` is related to the
electric `E'` and magnetic fields `B'` in `F'` at the point
`x' := (γ (t + β x), γ (x + β t), y, z)`
(corresponding to the same space-time point) by:

- `B_x x = B'_x x'`,
- `B_y x = γ (B'_y x' + β E_z x')`,
- `B_z x = γ (B'_z x' - β E_y x')`.

-/

lemma magneticField_apply_x_boost (β : ℝ) (hβ : |β| < 1)
    (A : ElectromagneticPotential) (hA : Differentiable ℝ A) (t : Time) (x : Space) :
    let Λ := LorentzGroup.boost (d := 3) 0 β hβ
    let t' : Time := γ β * (t.val + β * x 0)
    let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
    magneticField (fun x => Λ • A (Λ⁻¹ • x)) t x =
    fun | 0 => A.magneticField t' x' 0
        | 1 => γ β * (A.magneticField t' x' 1 + β * A.electricField t' x' 2)
        | 2 =>  γ β * (A.magneticField t' x' 2 - β * A.electricField t' x' 1) := by
  dsimp
  let t' : Time := γ β * (t.val + β * x 0)
  let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
  have t_trans : (SpaceTime.toTimeAndSpace ((boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).1
      = t' := by
    rw [boost_inverse, SpaceTime.boost_x_smul]
    simp [SpaceTime.toTimeAndSpace, SpaceTime.time, Lorentz.Vector.timeComponent]
    rfl
  have x_trans : (SpaceTime.toTimeAndSpace ((boost (d := 3) 0 β hβ)⁻¹ • SpaceTime.toTimeAndSpace.symm (t, x))).2
      = x' := by
    rw [boost_inverse, SpaceTime.boost_x_smul]
    simp [SpaceTime.toTimeAndSpace, SpaceTime.time, Lorentz.Vector.timeComponent]
    funext j
    fin_cases j <;> simp <;> rfl
  have h_diff : Differentiable ℝ fun x =>
      boost (d := 3) 0 β hβ • A ((boost (d := 3) 0 β hβ)⁻¹ • x) := by
    apply Differentiable.comp
    · change  Differentiable ℝ (Lorentz.Vector.actionCLM (boost 0 β hβ))
      exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM (boost 0 β hβ))
    · apply Differentiable.comp
      · exact hA
      · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM (boost 0 β hβ)⁻¹)
  let x' : Space := fun | 0 => γ β * (x 0 + β * t.val) | 1 => x 1 | 2 => x 2
  funext i
  fin_cases i
  · dsimp
    conv_lhs => rw [magneticField_fst_eq_fieldStrengthMatrix _ _ _ h_diff,
      fieldStrengthMatrix_equivariant _ _ hA]
    simp [Fin.sum_univ_three]
    rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    repeat rw [LorentzGroup.boost_inr_other_inr_self _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide)]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
    simp
    rw [t_trans, x_trans]
    · exact hA
  · dsimp
    conv_lhs => rw [magneticField_snd_eq_fieldStrengthMatrix _ _ _ h_diff,
      fieldStrengthMatrix_equivariant _ _ hA]
    simp [Fin.sum_univ_three]
    repeat rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_other_inr_self _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_other_inr _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_self_inr_other _ (by decide)]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime _ _ hA,
      fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime _ _ hA]
    simp
    trans (γ β * β * A.electricField t' x' 2) + γ β * A.magneticField t' x' 1
    · rw [x_trans, t_trans]
    · ring
  · dsimp
    conv_lhs => rw [magneticField_thd_eq_fieldStrengthMatrix _ _ _ h_diff,
      fieldStrengthMatrix_equivariant _ _ hA]
    simp [Fin.sum_univ_three]
    repeat rw [LorentzGroup.boost_inr_other_inl_0 _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_other_inr_self _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_self_inr_other _ (by decide)]
    repeat rw [LorentzGroup.boost_inr_inr_other _ (by decide)]
    simp
    rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime _ _ hA,
      fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime _ _ hA]
    simp
    trans γ β * A.magneticField t' x' 2 - γ β * β * A.electricField t' x' 1
    · rw [x_trans, t_trans]
      ring
    · ring

end ElectromagneticPotential
end Electromagnetism
