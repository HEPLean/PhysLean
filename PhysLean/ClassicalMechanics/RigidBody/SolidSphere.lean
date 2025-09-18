/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.RigidBody.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
/-!

# The solid sphere as a rigid body

In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.

-/

open Manifold
open MeasureTheory
namespace RigidBody
open NNReal

/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩

lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere]
  simp only [Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · rw [EuclideanSpace.volume_closedBall]
      simp
      exact not_eq_of_beq_eq_false rfl
    · rw [EuclideanSpace.volume_closedBall]
      simp only [ENNReal.ofReal_coe_nnreal, Nat.succ_eq_add_one, Fintype.card_fin, Nat.cast_add,
        Nat.cast_one, ne_eq, mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, pow_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.ofReal_eq_zero, not_or,
        not_le]
      apply And.intro
      · exact hr
      · positivity
  field_simp

/-- The center of mass of a solid sphere located at the origin is `0`. -/
@[sorryful]
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere d.succ m R).centerOfMass = 0 := by
  sorry

/-- The moment of inertia tensor of a solid sphere through its center of mass is
  `2/5 m R^2 * I`. -/
@[sorryful]
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _) := by
  sorry

end RigidBody
