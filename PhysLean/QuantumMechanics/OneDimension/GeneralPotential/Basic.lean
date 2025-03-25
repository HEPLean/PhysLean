/-
Copyright (c) 2025 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Analysis.Calculus.Deriv.Add
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Parity
import PhysLean.Meta.TODO.Basic
/-!

# The 1d QM system with general potential

-/

namespace QuantumMechanics

namespace OneDimension

open PhysLean HilbertSpace
open MeasureTheory

/-- The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `- i ℏ ψ'`.

  The notation `Pᵒᵖ` can be used for the momentum operator. -/
noncomputable def momentumOperator (ℏ : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => - Complex.I * ℏ * deriv ψ x

lemma fun_add {α : Type*} (f g : α → ℂ):
  (fun x => f x) + (fun x => g x) = fun x => f x + g x := by
  rfl

lemma fun_smul (a1: ℂ) (f : ℝ → ℂ): (a1 • fun x => f x) = (fun x => a1*(f x)) := by
    rfl

lemma momentum_linear (ℏ : ℝ) (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
  (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2) :
  momentumOperator ℏ ((a1 • ψ1) + (a2 • ψ2)) = a1 • momentumOperator ℏ ψ1 + a2 • momentumOperator ℏ ψ2 := by
    unfold momentumOperator
    have h1: (a1 • fun x => -Complex.I * ↑ℏ * deriv ψ1 x) = (fun x => a1*(-Complex.I * ↑ℏ * deriv ψ1 x)) := by
      rfl
    have h2: (a2 • fun x => -Complex.I * ↑ℏ * deriv ψ2 x) = (fun x => a2*(-Complex.I * ↑ℏ * deriv ψ2 x)) := by
      rfl
    rw [h1,h2]
    rw [fun_add ((fun x => a1 * (-Complex.I * ↑ℏ * deriv ψ1 x))) _]
    ext x
    have ha1ψ1_x: Differentiable ℝ (a1 •ψ1) := by
      exact (hψ1_x).const_smul a1
    have ha2ψ2_x: Differentiable ℝ (a2 •ψ2) := by
      exact (hψ2_x).const_smul a2
    have h: deriv ((a1 •ψ1) + (a2 •ψ2)) x = deriv (fun y => ((a1 •ψ1) y) + ((a2 •ψ2) y)) x := by
      rfl
    rw [h]
    rw [deriv_add]
    have ht1: deriv (a1 •ψ1) x = deriv (fun y => (a1 •ψ1 y)) x := by
      rfl
    have ht2: deriv (a2 •ψ2) x = deriv (fun y => (a2 •ψ2 y)) x := by
      rfl
    rw [ht1,ht2]
    rw [deriv_const_smul, deriv_const_smul]
    rw [mul_add]
    simp only [mul_comm, mul_assoc]
    rw [← mul_assoc,← mul_assoc]
    rw [← mul_assoc a1 _ _]
    rw [← mul_assoc a2 _ _]
    rw [mul_assoc]
    rw [mul_assoc]
    rfl
    exact hψ2_x x
    exact hψ1_x x
    exact (hψ1_x x).const_smul a1
    exact (hψ2_x x).const_smul a2

lemma momentum2_linear (ℏ : ℝ) (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
  (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2)
  (hψ1_xx: Differentiable ℝ (momentumOperator ℏ ψ1)) (hψ2_xx: Differentiable ℝ (momentumOperator ℏ ψ2)):
  momentumOperator ℏ (momentumOperator ℏ ((a1 • ψ1) + (a2 • ψ2))) = a1 • (momentumOperator ℏ (momentumOperator ℏ ψ1)) + a2 • (momentumOperator ℏ (momentumOperator ℏ ψ2)) := by
  rw [momentum_linear, momentum_linear]
  exact hψ1_xx
  exact hψ2_xx
  exact hψ1_x
  exact hψ2_x

/-- The position operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `x ψ'`. -/
noncomputable def positionOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => x * ψ x

/-- The potential operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `V(x) ψ`. -/
noncomputable def V_operator (V : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => V x * ψ x

lemma V_linear (V: ℝ → ℝ) (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ):
  V_operator V ((a1 • ψ1) + (a2 • ψ2)) = a1 • V_operator V ψ1 + a2 • V_operator V ψ2 := by
  unfold V_operator
  have h1: (a1 • fun x => V x * ψ1 x) = (fun x => a1*(V x * ψ1 x)) := by
    rfl
  have h2: (a2 • fun x => V x * ψ2 x) = (fun x => a2*(V x * ψ2 x)) := by
    rfl
  rw [h1,h2]
  rw [fun_add (fun x => a1*(V x * ψ1 x)) _]
  ext x
  have h: (a1 • ψ1 + a2 • ψ2) x = a1 *ψ1 x + a2 * ψ2 x := by
    rfl
  rw [h]
  rw [mul_add]
  simp only [mul_assoc, mul_comm, add_comm]
  rw [mul_comm,mul_assoc]
  rw [<-mul_assoc _ a2 _]
  rw [mul_comm _ a2]
  rw [mul_assoc a2 _ _]
  rw [mul_comm (ψ2 x) _]

/-- A quantum mechanical system in 1D is specified by a three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and
  a potential function `V` -/
structure GeneralPotential where
  /-- The mass of the particle. -/
  m : ℝ
  /-- Reduced Planck's constant. -/
  ℏ : ℝ
  V : ℝ → ℝ
  hℏ : 0 < ℏ
  hm : 0 < m

namespace GeneralPotential

variable (Q : GeneralPotential)

/-- For a 1D quantum mechanical system in potential `V`, the Schrodinger Operator corresponding to it
  is defined as the function from `ℝ → ℂ` to `ℝ → ℂ` taking

  `ψ ↦ - ℏ^2 / (2 * m) * ψ'' + V(x) * ψ`. -/
noncomputable def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => 1 / (2 * Q.m) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ) x) + (Q.V x) *  ψ x

lemma eval_add (f g : ℝ → ℂ):
  (f + g) x = f x + g x := by
  rfl

lemma schrodinger_linear (a1 a2 : ℂ) (ψ1 ψ2 : ℝ → ℂ)
  (hψ1_x: Differentiable ℝ ψ1) (hψ2_x: Differentiable ℝ ψ2)
  (hψ1_xx: Differentiable ℝ (momentumOperator Q.ℏ ψ1)) (hψ2_xx: Differentiable ℝ (momentumOperator Q.ℏ ψ2)):
  schrodingerOperator Q ((a1 • ψ1) + (a2 • ψ2)) = a1 • schrodingerOperator Q ψ1 + a2 • schrodingerOperator Q ψ2 := by
  unfold schrodingerOperator
  rw [momentum2_linear]
  rw [fun_smul a1 (fun x => 1 / (2 * Q.m) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1) x) + (Q.V x) *  ψ1 x)]
  rw [fun_smul a2 (fun x => 1 / (2 * Q.m) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2) x) + (Q.V x) *  ψ2 x)]
  rw [fun_add (fun x => a1*(1 / (2 * Q.m) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1) x) + (Q.V x) *  ψ1 x)) _]
  ext x
  rw [eval_add, mul_add]
  rw [eval_add, mul_add]
  rw [mul_add,mul_add]
  have h1: (a1 • ψ1) x = a1*ψ1 x := by rfl
  have h2: (a2 • ψ2) x = a2*ψ2 x := by rfl
  rw [h1,h2]
  simp only [mul_comm,mul_assoc,add_comm,add_assoc]
  rw [add_comm _ (a2 * (ψ2 x * ↑(Q.V x)))]
  rw [<-add_assoc _ _ (a2 * (1 / (↑Q.m * 2) * momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2) x))]
  rw [<-add_assoc _ (a1 * (ψ1 x * ↑(Q.V x)) + a2 * (ψ2 x * ↑(Q.V x))) _]
  rw [add_comm _ (a1 * (ψ1 x * ↑(Q.V x)) + a2 * (ψ2 x * ↑(Q.V x)))]
  rw [add_assoc,add_assoc]
  have ht1: 1 / (↑Q.m * 2) * (a1 • momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1)) x = a1 * ((1 / (↑Q.m * 2)) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1)) x) := by
    have ht1_t: (a1 • momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1)) x = a1*((momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ1)) x) := by
      rfl
    rw [ht1_t]
    rw [<-mul_assoc]
    rw [mul_comm _ a1]
    rw [mul_assoc]
  have ht2: 1 / (↑Q.m * 2) * (a2 • momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2)) x = a2 * ((1 / (↑Q.m * 2)) * (momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2)) x) := by
    have ht2_t: (a2 • momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2)) x = a2*((momentumOperator Q.ℏ (momentumOperator Q.ℏ ψ2)) x) := by
      rfl
    rw [ht2_t]
    rw [<-mul_assoc]
    rw [mul_comm _ a2]
    rw [mul_assoc]
  rw [ht1,ht2]
  exact hψ1_x
  exact hψ2_x
  exact hψ1_xx
  exact hψ2_xx

structure BoundedPotential where
  boundless: GeneralPotential
  hbound_left: ∀E,∃ R,∀z < -R, boundless.V z > E
  hbound_right: ∀E,∃ R,∀z > R, boundless.V z > E

namespace BoundedPotential
