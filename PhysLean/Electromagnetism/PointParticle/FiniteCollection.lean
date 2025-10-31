/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.PointParticle.ThreeDimension
/-!

# Finite collection of point particles in 3d

This module contains the electrostatics of a finite collection of point particles.
Since Gauss' law and Faraday's law are linear, the electrostatic potential and electric field
of a finite collection of point particles is just the sum of the potentials and fields of the
individual particles.

-/

namespace Electromagnetism
open Distribution SchwartzMap

namespace ThreeDimDiscreteCollection
open Space StaticElectricField MeasureTheory Real InnerProductSpace
noncomputable section

/-- The charge distribution for a finite collection of point particles. -/
def chargeDistribution {n : ℕ} (q : Fin n → ℝ) (r₀ : Fin n → Space) : ChargeDistribution 3 :=
    ∑ i, (q i) • diracDelta ℝ (r₀ i)

/-- The electrostatic potential of a finite collection of point particles. -/
def electricPotential {n : ℕ} (q : Fin n → ℝ) (ε : ℝ) (r₀ : Fin n → Space) :
    StaticElectricPotential 3 :=
  ∑ i, ThreeDimPointParticle.electricPotential (q i) ε (r₀ i)

/-- The electric field of a finite collection of point particles. -/
def electricField {n : ℕ} (q : Fin n → ℝ) (ε : ℝ) (r₀ : Fin n → Space) : StaticElectricField 3 :=
    ∑ i, ThreeDimPointParticle.electricField (q i) ε (r₀ i)

lemma electricField_eq_neg_distGrad_electricPotential {n : ℕ} (q : Fin n → ℝ) (ε : ℝ)
    (r₀ : Fin n → Space) :
    electricField q ε r₀ = - Space.distGrad (electricPotential q ε r₀) := by
  simp [electricField, electricPotential,
    ThreeDimPointParticle.electricField_eq_neg_distGrad_electricPotential]

lemma electricField_eq_ofPotential_electricPotential {n : ℕ} (q : Fin n → ℝ) (ε : ℝ)
    (r₀ : Fin n → Space) :
    electricField q ε r₀ = ofPotential (electricPotential q ε r₀) :=
  electricField_eq_neg_distGrad_electricPotential q ε r₀

/-- Gauss's law for a finite collection of point particles. -/
lemma gaussLaw {n : ℕ} (q : Fin n → ℝ) (ε : ℝ)
    (r₀ : Fin n → Space) :
    (electricField q ε r₀).GaussLaw ε (chargeDistribution q r₀) := by
  simp [electricField, chargeDistribution, GaussLaw, Finset.smul_sum]
  congr
  funext i
  simpa [GaussLaw] using ThreeDimPointParticle.gaussLaw (q i) ε (r₀ i)

/-- Faraday's law for a finite collection of point particles. -/
lemma faradaysLaw {n : ℕ} (q : Fin n → ℝ) (ε : ℝ)
    (r₀ : Fin n → Space) :
    (electricField q ε r₀).FaradaysLaw := by
  simp [electricField, FaradaysLaw]
  apply Finset.sum_eq_zero
  intro i _
  simpa [FaradaysLaw] using ThreeDimPointParticle.faradaysLaw (q i) ε (r₀ i)
