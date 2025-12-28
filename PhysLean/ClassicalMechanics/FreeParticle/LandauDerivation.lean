/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.EulerLagrange
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!

# Landau's Derivation of the Free Particle Lagrangian

## i. Overview

This module formalizes Landau's argument from "Mechanics" (§4) for why the Lagrangian
of a free particle in classical mechanics must be proportional to v², i.e., L = ½mv².

The argument proceeds from fundamental symmetry principles:
1. **Homogeneity of space**: L cannot depend on position
2. **Homogeneity of time**: L cannot depend explicitly on time
3. **Isotropy of space**: L can only depend on |v|² (not direction)
4. **Galilean invariance**: Physics must be the same in all inertial frames

Combined with these symmetries, the argument crucially relies on **gauge equivalence**:
two Lagrangians that differ by a total time derivative d/dt F(q, t) yield identical
equations of motion. Under a Galilean boost v → v + ε, the Lagrangian changes by some
δL(v). For the physics to be invariant, we don't require δL = 0, but only that δL is
a total time derivative (gauge equivalent to zero). This weaker requirement, combined
with the constraint that δL depends only on velocity, forces L to be quadratic in v.

## ii. Key results

- `IsGalileanInvariant`: Physical definition — boost changes must be total time derivatives
- `IsGalileanInvariantLagrangian`: Mathematical consequence — dL/d(v²) is constant
- `galileanInvariant_implies_const_deriv`: Physical definition implies the mathematical one
- `landau_free_particle_lagrangian'`: Main theorem — Galilean invariance forces L = ½mv²

## iii. References

- Landau & Lifshitz, "Mechanics", 3rd edition, §4 "The Lagrangian for a free particle"

-/

namespace ClassicalMechanics

open Real
open InnerProductSpace
open MeasureTheory
open Filter

/-!

## A. Setup

By homogeneity and isotropy of space, and homogeneity of time, the free particle
Lagrangian can only depend on |v|². We represent this as a function `L : ℝ → ℝ`
where L(v²) is the Lagrangian evaluated at speed squared v².

-/

namespace FreeParticle

/-!

## B. Galilean Invariance: Mathematical Consequence

The physical requirement (Section C) will imply that dL/d(v²) must be constant.
We first state this mathematical condition, then derive it from the physics.

-/

/-- The mathematical consequence of Galilean invariance: dL/d(v²) is constant on [0, ∞).
See `IsGalileanInvariant` for the physical definition and `galileanInvariant_implies_const_deriv`
for the proof that the physical definition implies this one. -/
def IsGalileanInvariantLagrangian (L : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → deriv L x = c

/-!

## C. Galilean Invariance: Physical Definition

Landau's argument:
1. Under a Galilean boost v → v + ε, the Lagrangian L(|v|²) changes by some δL
2. By gauge equivalence, physics is invariant if δL = d/dt F(r, t) for some F
3. Since δL depends only on v (not r or t), we need δL(v) = ⟨g, v⟩ for constant g
4. This forces dL/d(v²) to be constant

Step 3 is the key: if δL = d/dt F where F = F(r, t), then δL = ∂F/∂t + ⟨∇F, v⟩.
For δL to be r-independent, ∇F must be r-independent (constant in r, possibly t-dependent).
Writing F = ⟨g(t), r⟩ + k(t), we get ∂F/∂t = ⟨g'(t), r⟩ + k'(t), which is r-independent
only if g'(t) = 0, i.e., g is constant. Then δL = k'(t) + ⟨g, v⟩. For δL to be
t-independent, k'(t) must be constant, say a. Finally, δL(0) = 0 forces a = 0.
Thus δL(v) = ⟨g, v⟩ for constant g.

-/

/-- A velocity-dependent function δL can be expressed as a total time derivative d/dt F(r,t)
(with F independent of velocity) iff δL(v) = ⟨g, v⟩ for some constant g. -/
def IsTotalTimeDerivative {n : ℕ} (δL : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n), ∀ v, δL v = ⟪g, v⟫_ℝ

/-- First-order change in L(|v|²) under boost v → v + ε:
L(|v+ε|²) - L(|v|²) ≈ 2·(dL/d(v²))·⟨v,ε⟩ + O(ε²). -/
noncomputable def boostChange (L : ℝ → ℝ) {n : ℕ}
    (ε : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun v => 2 * deriv L ⟪v, v⟫_ℝ * ⟪v, ε⟫_ℝ

/-- Physical Galilean invariance: for every boost ε, the first-order Lagrangian change
is gauge equivalent to zero (i.e., is a total time derivative). -/
def IsGalileanInvariant {n : ℕ} (L : ℝ → ℝ) : Prop :=
  ∀ ε : EuclideanSpace ℝ (Fin n), IsTotalTimeDerivative (boostChange L ε)

/-!

## D. Key Lemma: Total Derivative Condition Forces Constant Derivative

The mathematical core: if 2·φ(|v|²)·⟨v,ε⟩ = ⟨g,v⟩ for all v and ε ≠ 0, then φ is constant.

Proof: The equation holds for all v, so substitute v = t·ε for t > 0:
  2·φ(t²|ε|²)·t·|ε|² = t·⟨g,ε⟩
Dividing by t: φ(t²|ε|²) = ⟨g,ε⟩/(2|ε|²) for all t > 0.
As t varies, t²|ε|² covers all of (0,∞), so φ is constant on (0,∞).

-/

/-- If ⟨a, v⟩ = ⟨b, v⟩ for all v, then a = b. -/
lemma eq_of_inner_eq_all {n : ℕ} (a b : EuclideanSpace ℝ (Fin n))
    (h : ∀ v, ⟪a, v⟫_ℝ = ⟪b, v⟫_ℝ) : a = b := by
  have h' : ∀ v, ⟪a - b, v⟫_ℝ = 0 := fun v => by
    rw [inner_sub_left, h v, sub_self]
  have hab : ⟪a - b, a - b⟫_ℝ = 0 := h' (a - b)
  rw [inner_self_eq_zero] at hab
  exact sub_eq_zero.mp hab

/-- For ε ≠ 0 and s > 0, there exists v with |v|² = s and ⟨v, ε⟩ ≠ 0. -/
lemma exists_v_with_norm_and_nonzero_inner_pos {n : ℕ}
    (ε : EuclideanSpace ℝ (Fin n)) (hε : ε ≠ 0) (s : ℝ) (hs : 0 < s) :
    ∃ v : EuclideanSpace ℝ (Fin n), ⟪v, v⟫_ℝ = s ∧ ⟪v, ε⟫_ℝ ≠ 0 := by
  have hε_norm : ⟪ε, ε⟫_ℝ > 0 := real_inner_self_pos.mpr hε
  let t := Real.sqrt (s / ⟪ε, ε⟫_ℝ)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (div_pos hs hε_norm)
  use t • ε
  constructor
  · rw [real_inner_smul_left, real_inner_smul_right]
    have ht_sq : t * t = s / ⟪ε, ε⟫_ℝ := Real.mul_self_sqrt (le_of_lt (div_pos hs hε_norm))
    calc t * (t * ⟪ε, ε⟫_ℝ) = (t * t) * ⟪ε, ε⟫_ℝ := by ring
      _ = (s / ⟪ε, ε⟫_ℝ) * ⟪ε, ε⟫_ℝ := by rw [ht_sq]
      _ = s := by field_simp
  · rw [real_inner_smul_left]
    intro h
    rw [mul_eq_zero] at h
    cases h with
    | inl h => exact (ne_of_gt ht_pos) h
    | inr h => exact (ne_of_gt hε_norm) h

/-- Core lemma: if 2·φ(|v|²)·⟨v,ε⟩ = ⟨g,v⟩ for all v with ε ≠ 0, then φ is constant on (0, ∞). -/
lemma deriv_const_of_totalDerivative_pos {n : ℕ} [_hn : Fact (0 < n)]
    (φ : ℝ → ℝ) (_hφ : Continuous φ)
    (ε : EuclideanSpace ℝ (Fin n)) (hε : ε ≠ 0)
    (g : EuclideanSpace ℝ (Fin n))
    (h : ∀ v, 2 * φ ⟪v, v⟫_ℝ * ⟪v, ε⟫_ℝ = ⟪g, v⟫_ℝ) :
    ∃ c : ℝ, ∀ x : ℝ, 0 < x → φ x = c := by
  -- Key insight: for v with ⟨v,ε⟩ ≠ 0, we have 2·φ(‖v‖²)·ε = g
  -- (by substituting v = t·w for various t and using linearity in v)
  have hε_norm : ⟪ε, ε⟫_ℝ > 0 := real_inner_self_pos.mpr hε
  -- The constant must be g·ε / (2·‖ε‖²)
  use ⟪g, ε⟫_ℝ / (2 * ⟪ε, ε⟫_ℝ)
  intro x hx
  -- From h (t•ε) for t² = x/‖ε‖²:
  let t := Real.sqrt (x / ⟪ε, ε⟫_ℝ)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (div_pos hx hε_norm)
  have h_tε := h (t • ε)
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right] at h_tε
  have ht_sq : t * t = x / ⟪ε, ε⟫_ℝ := Real.mul_self_sqrt (le_of_lt (div_pos hx hε_norm))
  have h_inner_tε : t * (t * ⟪ε, ε⟫_ℝ) = x := by
    calc t * (t * ⟪ε, ε⟫_ℝ) = (t * t) * ⟪ε, ε⟫_ℝ := by ring
      _ = (x / ⟪ε, ε⟫_ℝ) * ⟪ε, ε⟫_ℝ := by rw [ht_sq]
      _ = x := by field_simp
  rw [h_inner_tε] at h_tε
  -- h_tε : 2 * φ x * (t * ⟪ε, ε⟫_ℝ) = t * ⟪g, ε⟫_ℝ
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hεε_ne : ⟪ε, ε⟫_ℝ ≠ 0 := ne_of_gt hε_norm
  -- From h_tε: 2 * φ x * (t * ⟪ε, ε⟫_ℝ) = t * ⟪g, ε⟫_ℝ
  -- Divide by t and ⟪ε, ε⟫_ℝ to get φ x = ⟪g, ε⟫_ℝ / (2 * ⟪ε, ε⟫_ℝ)
  have h1 : 2 * φ x * (t * ⟪ε, ε⟫_ℝ) = t * ⟪g, ε⟫_ℝ := h_tε
  have h2 : φ x * (2 * t * ⟪ε, ε⟫_ℝ) = t * ⟪g, ε⟫_ℝ := by linarith
  have h3 : φ x = t * ⟪g, ε⟫_ℝ / (2 * t * ⟪ε, ε⟫_ℝ) := by
    field_simp at h2 ⊢
    linarith
  simp only [h3]
  field_simp

/-- Extension to [0, ∞) by continuity at 0. -/
lemma deriv_const_of_totalDerivative {n : ℕ} [hn : Fact (0 < n)]
    (φ : ℝ → ℝ) (hφ : Continuous φ)
    (ε : EuclideanSpace ℝ (Fin n)) (hε : ε ≠ 0)
    (g : EuclideanSpace ℝ (Fin n))
    (h : ∀ v, 2 * φ ⟪v, v⟫_ℝ * ⟪v, ε⟫_ℝ = ⟪g, v⟫_ℝ) :
    ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → φ x = c := by
  obtain ⟨c, hc⟩ := deriv_const_of_totalDerivative_pos φ hφ ε hε g h
  use c
  intro x hx
  rcases hx.eq_or_lt with rfl | hx_pos
  · -- x = 0: use continuity
    have hφ0 : Tendsto φ (nhds 0) (nhds (φ 0)) := hφ.tendsto 0
    have hφ0' : Tendsto (fun t => φ t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
      hφ0.mono_left nhdsWithin_le_nhds
    have hc_lim : Tendsto (fun (_ : ℝ) => c) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) :=
      tendsto_const_nhds
    have heq : ∀ t ∈ Set.Ioi (0 : ℝ), φ t = c := fun t ht => hc t ht
    exact tendsto_nhds_unique (hφ0'.congr' (eventually_nhdsWithin_of_forall heq)) hc_lim
  · exact hc x hx_pos

/-- Physical Galilean invariance forces dL/d(v²) to be constant. -/
theorem galileanInvariant_implies_const_deriv {n : ℕ} [hn : Fact (0 < n)]
    (L : ℝ → ℝ) (hL : ContDiff ℝ ⊤ L)
    (hGal : IsGalileanInvariant (n := n) L) :
    ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → deriv L x = c := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn.out
  let e : Fin n := ⟨0, Nat.pos_of_ne_zero hn'⟩
  let ε : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single e 1
  have hε : ε ≠ 0 := by
    simp only [ε, ne_eq]
    intro h
    have h1 : (EuclideanSpace.single e 1 : EuclideanSpace ℝ (Fin n)) e = 1 := by
      simp [EuclideanSpace.single_apply]
    have h2 : (0 : EuclideanSpace ℝ (Fin n)) e = 0 := rfl
    rw [h, h2] at h1
    exact one_ne_zero h1.symm
  obtain ⟨g, hg⟩ := hGal ε
  exact deriv_const_of_totalDerivative (deriv L) (hL.continuous_deriv le_top) ε hε g hg

/-- Physical definition implies the mathematical condition. -/
theorem galileanInvariant_implies_galileanInvariantLagrangian {n : ℕ} [hn : Fact (0 < n)]
    (L : ℝ → ℝ) (hL : ContDiff ℝ ⊤ L)
    (hGal : IsGalileanInvariant (n := n) L) :
    IsGalileanInvariantLagrangian L :=
  galileanInvariant_implies_const_deriv L hL hGal

/-- Constant derivative implies L(v²) = c·v² + L(0) by integration. -/
theorem lagrangian_eq_const_mul_of_galileanInvariant
    (L : ℝ → ℝ) (hL : ContDiff ℝ ⊤ L)
    (hGal : IsGalileanInvariantLagrangian L) :
    ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → L x = c * x + L 0 := by
  obtain ⟨c, hc⟩ := hGal
  use c
  intro x hx
  have hLcont : ContinuousOn L (Set.Icc 0 x) := hL.continuous.continuousOn
  have hLderiv : ∀ t ∈ Set.Ioo 0 x, HasDerivAt L (deriv L t) t := fun t _ =>
    hL.differentiable le_top |>.differentiableAt.hasDerivAt
  have hLint : IntervalIntegrable (deriv L) volume 0 x :=
    (hL.continuous_deriv le_top).intervalIntegrable 0 x
  have h1 : L x - L 0 = ∫ t in (0)..x, deriv L t := by
    symm
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hLcont hLderiv hLint
  have h2 : ∫ t in (0)..x, deriv L t = ∫ _ in (0)..x, c := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : 0 ≤ t := by
      simp only [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact ht.1
    exact hc t ht'
  rw [h2] at h1
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  linarith

/-- With normalization L(0) = 0, we get L(v²) = c·v². -/
theorem lagrangian_eq_const_mul_of_galileanInvariant'
    (L : ℝ → ℝ) (hL : ContDiff ℝ ⊤ L) (hL0 : L 0 = 0)
    (hGal : IsGalileanInvariantLagrangian L) :
    ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → L x = c * x := by
  obtain ⟨c, hc⟩ := lagrangian_eq_const_mul_of_galileanInvariant L hL hGal
  use c
  intro x hx
  rw [hc x hx, hL0, add_zero]

/-!

## E. The Kinetic Energy Lagrangian

The standard kinetic energy L = ½mv² satisfies all conditions.

-/

/-- The kinetic energy Lagrangian: L(v²) = ½m·v². -/
noncomputable def kineticEnergyLagrangian (m : ℝ) : ℝ → ℝ :=
  fun vsq => (1/2) * m * vsq

lemma kineticEnergyLagrangian_apply (m : ℝ) (vsq : ℝ) :
    kineticEnergyLagrangian m vsq = (1/2) * m * vsq := rfl

@[simp]
lemma kineticEnergyLagrangian_zero (m : ℝ) :
    kineticEnergyLagrangian m 0 = 0 := by simp [kineticEnergyLagrangian]

@[fun_prop]
lemma kineticEnergyLagrangian_contDiff (m : ℝ) :
    ContDiff ℝ ⊤ (kineticEnergyLagrangian m) := by
  unfold kineticEnergyLagrangian
  fun_prop

lemma kineticEnergyLagrangian_deriv (m : ℝ) (vsq : ℝ) :
    deriv (kineticEnergyLagrangian m) vsq = (1/2) * m := by
  unfold kineticEnergyLagrangian
  have h : (fun vsq => 1 / 2 * m * vsq) = (fun vsq => (1/2 * m) * vsq) := by ring_nf
  rw [h, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

/-- ½mv² satisfies the mathematical Galilean invariance condition. -/
theorem kineticEnergy_isGalileanInvariant (m : ℝ) :
    IsGalileanInvariantLagrangian (kineticEnergyLagrangian m) := by
  use (1/2) * m
  intro x _
  exact kineticEnergyLagrangian_deriv m x

/-- The boost change for ½mv² is m·⟨v,ε⟩ = d/dt(m·⟨r,ε⟩), a total time derivative. -/
theorem kineticEnergy_boost_isTotalDerivative {n : ℕ} (m : ℝ)
    (ε : EuclideanSpace ℝ (Fin n)) :
    IsTotalTimeDerivative (boostChange (kineticEnergyLagrangian m) ε) := by
  use m • ε
  intro v
  simp only [boostChange, kineticEnergyLagrangian_deriv]
  rw [real_inner_smul_left, real_inner_comm ε v]
  ring

/-- ½mv² satisfies the physical Galilean invariance condition. -/
theorem kineticEnergy_isGalileanInvariant' {n : ℕ} (m : ℝ) :
    IsGalileanInvariant (n := n) (kineticEnergyLagrangian m) := by
  intro ε
  exact kineticEnergy_boost_isTotalDerivative m ε

/-!

## F. Auxiliary: Boost Change Formulas

Explicit formulas for how |v|² and L change under v → v + ε.

-/

/-- Change in |v|² under boost: |v+ε|² - |v|² = 2⟨v,ε⟩ + |ε|². -/
lemma vsq_boost_change {n : ℕ} (v ε : EuclideanSpace ℝ (Fin n)) :
    ⟪v + ε, v + ε⟫_ℝ - ⟪v, v⟫_ℝ = 2 * ⟪v, ε⟫_ℝ + ⟪ε, ε⟫_ℝ := by
  simp only [inner_add_left, inner_add_right, real_inner_comm ε v]
  ring

/-- First-order Lagrangian change under boost. -/
noncomputable def lagrangianBoostChange (L : ℝ → ℝ) {n : ℕ}
    (v ε : EuclideanSpace ℝ (Fin n)) : ℝ :=
  deriv L ⟪v, v⟫_ℝ * (2 * ⟪v, ε⟫_ℝ)

lemma lagrangianBoostChange_eq (L : ℝ → ℝ) {n : ℕ} (v ε : EuclideanSpace ℝ (Fin n)) :
    lagrangianBoostChange L v ε = 2 * deriv L ⟪v, v⟫_ℝ * ⟪v, ε⟫_ℝ := by
  unfold lagrangianBoostChange
  ring

/-!

## G. Main Theorems

Landau's theorem: Galilean invariance + gauge equivalence forces L = ½mv².

-/

/-- Landau's theorem (mathematical version): if dL/d(v²) is constant and L(0) = 0,
then L = ½mv² for some m. -/
theorem landau_free_particle_lagrangian (L : ℝ → ℝ)
    (hL : ContDiff ℝ ⊤ L) (hL0 : L 0 = 0)
    (hGal : IsGalileanInvariantLagrangian L) :
    ∃ m : ℝ, ∀ x : ℝ, 0 ≤ x → L x = kineticEnergyLagrangian m x := by
  obtain ⟨c, hc⟩ := lagrangian_eq_const_mul_of_galileanInvariant' L hL hL0 hGal
  use 2 * c
  intro x hx
  rw [hc x hx, kineticEnergyLagrangian_apply]
  ring

/-- **Landau's theorem (physical version)**: A Lagrangian L(|v|²) satisfying physical
Galilean invariance (boost changes are gauge equivalent to zero) with L(0) = 0 must
be L = ½mv² for some constant m.

This is the complete formalization of Landau & Lifshitz, Mechanics §4. -/
theorem landau_free_particle_lagrangian' {n : ℕ} [hn : Fact (0 < n)]
    (L : ℝ → ℝ) (hL : ContDiff ℝ ⊤ L) (hL0 : L 0 = 0)
    (hGal : IsGalileanInvariant (n := n) L) :
    ∃ m : ℝ, ∀ x : ℝ, 0 ≤ x → L x = kineticEnergyLagrangian m x := by
  have hGal' : IsGalileanInvariantLagrangian L :=
    galileanInvariant_implies_galileanInvariantLagrangian L hL hGal
  exact landau_free_particle_lagrangian L hL hL0 hGal'

/-- Converse: ½mv² satisfies all Landau conditions (mathematical). -/
theorem kineticEnergy_satisfies_landau_conditions (m : ℝ) :
    ContDiff ℝ ⊤ (kineticEnergyLagrangian m) ∧
    kineticEnergyLagrangian m 0 = 0 ∧
    IsGalileanInvariantLagrangian (kineticEnergyLagrangian m) :=
  ⟨kineticEnergyLagrangian_contDiff m,
   kineticEnergyLagrangian_zero m,
   kineticEnergy_isGalileanInvariant m⟩

/-- Converse: ½mv² satisfies all Landau conditions (physical). -/
theorem kineticEnergy_satisfies_landau_conditions' {n : ℕ} (m : ℝ) :
    ContDiff ℝ ⊤ (kineticEnergyLagrangian m) ∧
    kineticEnergyLagrangian m 0 = 0 ∧
    IsGalileanInvariant (n := n) (kineticEnergyLagrangian m) :=
  ⟨kineticEnergyLagrangian_contDiff m,
   kineticEnergyLagrangian_zero m,
   kineticEnergy_isGalileanInvariant' m⟩

/-!

## H. Physical Interpretation: Momentum

The constant c in L = c·v² is m/2. This follows from the momentum relation:
p = ∂L/∂v = 2c·v, which equals mv when c = m/2, giving L = ½mv².

-/

end FreeParticle

end ClassicalMechanics
