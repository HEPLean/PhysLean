/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Lagrangian
import PhysLean.Electromagnetism.FaradayLaw
import PhysLean.ClassicalMechanics.WaveEquation.Basic
import PhysLean.SpaceAndTime.Space.VectorIdentities

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
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

def IsVacuumExtrema (A : ElectromagneticPotential) : Prop :=
  gradLagrangian A 0 = 0

namespace IsVacuumSolution
open ClassicalMechanics


/-- The electromagnetic wave equation for electric field. -/
theorem electricField_waveEquation {t x} {A : ElectromagneticPotential} :
    WaveEquation A.electricField t x 1 := by
  rw [WaveEquation]
  ext i
  simp [Space.laplacianVec, Space.coord_apply]


  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    · simp [← smul_assoc, mul_assoc, OM.mu_ge_zero, ne_of_gt, OM.eps_ge_zero]
    · exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => E t x) t) t =
      ∂ₜ (fun t => (μ • ε)⁻¹ • (∇ × B t) x) t := by aesop
  rw [hdt2]
  have hd0 : (∇ ⬝ (E t)) = 0 := by
    ext x
    simp [OM.gaussLawElectric_of_free E B, h]
  have hlpE : Δ (E t) = - ((fun x => ∇ (∇ ⬝ (E t)) - Δ (E t)) x) := by simp [hd0]
  rw [hlpE, ← curl_of_curl]
  have hcE : curl (E t) = fun x => - ∂ₜ (fun t => B t x) t := by
    funext x
    simp [OM.faradayLaw_of_free E B, h]
  rw [hcE]
  have hcn : curl (fun x => -∂ₜ (fun t => B t x) t) =
      - curl (fun x => ∂ₜ (fun t => B t x) t) := by
    trans - (1:ℝ) • curl (fun x => ∂ₜ (fun t => B t x) t)
    rw [← curl_smul, neg_smul, one_smul]
    rfl
    · exact fun x ↦ fderiv_curry_differentiableAt_fst_comp_snd (hf := hB) ..
    · exact neg_one_smul ..
  simp only [smul_eq_mul, _root_.mul_inv_rev, hcn, Pi.neg_apply, neg_neg]
  rw [← time_deriv_curl_commute]
  have hdt_smul : ∂ₜ (fun t => (OM.ε⁻¹ * OM.μ⁻¹) • curl (B t) x) t =
      (OM.ε⁻¹ * OM.μ⁻¹) • ∂ₜ (fun t => curl (B t) x) t := by
    rw [deriv_smul]
    unfold curl Space.deriv coord basis
    simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
      EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply differentiable_pi''
    intro i
    fin_cases i <;> fun_prop
  rw [hdt_smul, sub_self]
  · exact hB
  · exact hE.uncurry ..
  · rw [inv_nonneg]
    exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)


end IsVacuumSolution

end ElectromagneticPotential

end Electromagnetism
