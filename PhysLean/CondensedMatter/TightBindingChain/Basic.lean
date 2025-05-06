/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.TODO.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.QuantumMechanics.FiniteTarget.HilbertSpace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!

# The tight binding chain

The tight binding chain corresponds to an electron in motion
in a 1d solid with the assumption the electron can sit only on the atoms of the solid.

The solid is assumed to consist of `N` sites with a seperation of `a` between them

Mathematically, the tight binding chain corresponds to a
QM problem located on a lattice with only self and nearest neighbour interactions,
with periodic boundary conditions.

## Refs.

- https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf

-/

TODO "BBZAB" "Prove results related to the one-dimensional tight binding chain.
  This is related to the following issue/feature-request:
  https://github.com/HEPLean/PhysLean/issues/523 "

namespace CondensedMatter

/-- The physical parameters making up the tight binding chain. -/
structure TightBindingChain where
  /-- The number of sites, or atoms, in the chain -/
  N : Nat
  [N_ne_zero : NeZero N]
  /-- The distance between the sites -/
  a : ℝ
  a_pos : 0 < a
  /-- The energy associate with a particle sitting at a fixed site. -/
  E0 : ℝ
  /-- The hopping parameter. -/
  t : ℝ

namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-- The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional
Hilbert space. -/
abbrev HilbertSpace := QuantumMechanics.FiniteHilbertSpace T.N

instance : NeZero T.N := T.N_ne_zero

/-- The eigenstate corresponding to the particle been located on the `n`th site. -/
noncomputable def localizedState {T : TightBindingChain} :
    OrthonormalBasis (Fin T.N) ℂ (HilbertSpace T) :=
  EuclideanSpace.basisFun (Fin T.N) ℂ

@[inherit_doc localizedState]
scoped notation "|" n "⟩" => localizedState n

/-- The inner product of two localized states. -/
scoped notation "⟨" m "|" n "⟩" => ⟪localizedState m, localizedState n⟫_ℂ

/-- The localized states are normalized. -/
lemma localizedState_orthonormal : Orthonormal ℂ (localizedState (T := T)) :=
  (localizedState (T := T)).orthonormal

lemma localizedState_orthonormal_eq_ite (m n : Fin T.N) :
    ⟨m|n⟩ = if m = n then 1 else 0 := orthonormal_iff_ite.mp T.localizedState_orthonormal _ _

/-- The linear map `|m⟩⟨n|` for `⟨n|` localized states. -/
noncomputable def localizedComp {T : TightBindingChain} (m n : Fin T.N) :
    T.HilbertSpace →ₗ[ℂ] T.HilbertSpace where
  toFun ψ := ⟪|n⟩, ψ⟫_ℂ • |m⟩
  map_add' ψ1 ψ2 := by
    rw [inner_add_right]
    simp [add_smul]
  map_smul' _ _ := by
    rw [inner_smul_right]
    simp [smul_smul]

@[inherit_doc localizedComp]
scoped notation "|" n "⟩⟨" m "|" => localizedComp n m

lemma localizedComp_apply_localizedState (m n p : Fin T.N) :
    |m⟩⟨n| |p⟩ = if n = p then |m⟩ else 0 := by
  rw [localizedComp]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [orthonormal_iff_ite.mp T.localizedState_orthonormal n p]
  simp

/-- The Hamiltonian of the tight binding chain is given by
  `E₀ ∑ n, |n⟩⟨n| - t ∑ n, (|n⟩⟨n + 1| + |n + 1⟩⟨n|)`, with periodic
  boundary conditions. -/
noncomputable def hamiltonian : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.E0 • ∑ n : Fin T.N, |n⟩⟨n| - T.t • ∑ n : Fin T.N, (|n⟩⟨n + 1| + |n + 1⟩⟨n|)

/-- The Hamiltonian applied to the localized state `|n⟩` gives
  `T.E0 • |n⟩ - T.t • (|n + 1⟩ + |n - 1⟩)`. -/
lemma hamiltonian_apply_localizedState (n : Fin T.N) :
    T.hamiltonian |n⟩ = (T.E0 : ℂ) • |n⟩ - (T.t : ℂ) • (|n + 1⟩ + |n - 1⟩) := by
  rw [hamiltonian]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.add_apply, smul_add]
  congr
  · /- The `|n⟩` term -/
    conv_lhs => enter [2, c]; rw [localizedComp_apply_localizedState]
    simp
  · rw [← smul_add]
    congr
    rw [Finset.sum_add_distrib, add_comm]
    congr
    · /- The `|n + 1⟩` term-/
      conv_lhs => enter [2, c]; rw [localizedComp_apply_localizedState]
      simp
    · /- The `|n - 1⟩` term -/
      conv_lhs => enter [2, c]; rw [localizedComp_apply_localizedState]
      rw [Finset.sum_eq_single (n - 1)]
      · simp
      · intro b _ hb
        rw [if_neg]
        by_contra hn
        subst hn
        simp at hb
      · simp

/-- The energy of a localized state in the tight binding chain is `E0`.
  This lemma assumes that there is more then one site in the chain otherwise the
  result is not true. -/
lemma energy_localizedState (n : Fin T.N) (htn : 1 < T.N) : ⟪|n⟩, T.hamiltonian |n⟩⟫_ℂ = T.E0 := by
  rw [hamiltonian_apply_localizedState]
  simp only [smul_add, inner_sub_right, inner_add_right]
  erw [inner_smul_right, inner_smul_right, inner_smul_right]
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, Complex.coe_algebraMap, ZeroHom.coe_mk, localizedState_orthonormal_eq_ite,
    ↓reduceIte, mul_one, left_eq_add, Fin.one_eq_zero_iff, mul_ite, mul_zero, sub_eq_self]
  split_ifs with h1 h2
  · omega
  · omega
  · rename_i h2
    have hn : (-1 : Fin T.N) = 0 := by
      trans n - n
      · nth_rewrite 1 [h2]
        ring
      · ring
    simp only [neg_eq_zero, Fin.one_eq_zero_iff] at hn
    omega
  · simp

/-- The Brillouin zone of the tight binding model is `[-π/a, π/a)`.
  This is the set in which wave functions are uniquly defined. -/
def BrillouinZone : Set ℝ := Set.Ico (- Real.pi / T.a) (Real.pi / T.a)

def QuantaWaveNumber : Set ℝ := {x | (∃ n : Fin T.N,
     2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x)}

/-- The quantized wavenumbers form a subset of the `BrillouinZone`. -/
lemma quantaWaveNumber_subset_brillouinZone : T.QuantaWaveNumber ⊆ T.BrillouinZone := by
  intro x hx
  simp [QuantaWaveNumber] at hx
  obtain ⟨n, rfl⟩ := hx
  simp [BrillouinZone]
  apply And.intro
  · have ht : T.N ≠ 0 := by exact Ne.symm (NeZero.ne' T.N)
    generalize T.N = x at *
    have hT := T.a_pos
    have hT : T.a ≠ 0 := by positivity
    generalize T.a = a at *
    apply le_of_eq_of_le (by ring : _ = (Real.pi / a) * (-1 : ℝ))
    apply le_of_le_of_eq  (b := (Real.pi / a) * (2 * ((n : ℝ) - (x /2 : ℕ))/ x ) )
    · apply mul_le_mul_of_nonneg_left
      · have hk := Nat.even_or_odd' x
        obtain ⟨k, hk⟩ := hk
        rcases hk with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp
          have hl : 2 * (↑↑n - (k : ℝ)) / (2 * ↑k) = ↑↑n / ↑k - 1 := by
            simp at ht
            field_simp
            ring
          rw [hl]
          rw [@neg_le_sub_iff_le_add']
          simp
          positivity
        · have h0 : (2 * k + 1) / 2 = k := by
            omega
          rw [h0]
          rw [neg_le_iff_add_nonneg']
          have hl : 1 + 2 * (↑↑n - (↑k : ℝ)) / ↑(2 * k + 1) = (2 * k + 1 + 2 * (↑↑n - ↑k) ) / ↑(2 * k + 1) := by
            field_simp
          rw [hl]
          apply div_nonneg
          · have hl : 2 * (k : ℝ) + 1 + 2 * (↑↑n - ↑k) = 1 + 2 * n := by ring
            rw [hl]
            positivity
          · positivity
      · positivity
    · ring
  · have ht : T.N ≠ 0 := by exact Ne.symm (NeZero.ne' T.N)
    generalize T.N = x at *
    have hT := T.a_pos
    have hT' : T.a ≠ 0 := by positivity
    generalize T.a = a at *
    apply lt_of_lt_of_eq (b := (Real.pi / a) * (1 : ℝ))
    swap
    · ring
    apply lt_of_eq_of_lt (b := (Real.pi / a) * (2 * ((n : ℝ) - (x /2 : ℕ))/ x ) )
    · ring
    apply mul_lt_mul_of_pos_left
    · have hk := Nat.even_or_odd' x
      obtain ⟨k, hk⟩ := hk
      rcases hk with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp
        have hl : 2 * (↑↑n - (k : ℝ)) / (2 * ↑k) = ↑↑n / ↑k - 1 := by
          simp at ht
          field_simp
          ring
        rw [hl]
        rw [@sub_lt_iff_lt_add']
        ring
        field_simp
        refine (div_lt_iff₀' ?_).mpr ?_
        · simp at ht
          positivity
        · have hn : n < k * 2 := by omega
          simpa using (Nat.cast_lt (α := ℝ)).mpr hn
      · have h0 : (2 * k + 1) / 2 = k := by
          omega
        rw [h0]
        refine (div_lt_one ?_).mpr ?_
        · positivity
        rw [mul_sub]
        simp
        rw [sub_lt_iff_lt_add]
        have hl : 2 * (↑k : ℝ) + 1 + 2 * ↑k = 4 * ↑k  + 1 := by ring
        rw [hl]
        have hn := n.prop
        have hn : n.val ≤ 2 * k := by omega
        have hn' : 2 * n.val ≤ 4 * k := by omega
        have hn'' : 2 * (n.val : ℝ) ≤ 4 * (k : ℝ) := by
          simpa using (Nat.cast_le (α := ℝ)).mpr hn'
        apply lt_of_le_of_lt hn''
        simp only [lt_add_iff_pos_right, zero_lt_one]
    · positivity

/--

import Mathlib

lemma test1 (x : Nat) (n : Fin x) (a : Real):
   -Real.pi / a ≤ 2 * Real.pi / (a * ↑x) * (↑↑n - ↑(x / 2)) := by
  sorry

lemma test2 (x : Nat) (n : Fin x) (a : Real):
   -Real.pi / a ≤ 2 * Real.pi / (a * ↑x) * (↑↑n - ↑(x / 2)) := by
  sorry
  -/


lemma quantaWaveNumber_exp_N (n : ℕ) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * n * T.N * T.a) = 1 := by
  refine Complex.exp_eq_one_iff.mpr ?_
  match k with
  | ⟨k, hk⟩ =>
  obtain ⟨k, rfl⟩ := hk
  use ((k : Int) - (T.N / 2 : ℕ)) * (n : ℤ)
  have hp : T.N ≠ 0 := by exact Ne.symm (NeZero.ne' T.N)
  have hpp : (T.N : ℂ) ≠ 0 := by aesop
  have hT := T.a_pos
  have hT' : (T.a : ℂ) ≠ 0 := by aesop
  field_simp
  ring_nf
  congr 2
  simp only [mul_assoc]
  congr 2
  rw [mul_comm]
  simp only [mul_assoc]
  rfl

lemma quantaWaveNumber_exp_sub_one (n : Fin T.N) (k : T.QuantaWaveNumber)  :
    Complex.exp (Complex.I * k * (n - 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (- Complex.I * k * T.a) := by
  rw [Fin.coe_sub]
  trans Complex.exp (Complex.I * ↑↑k * ↑(((T.N - 1 + n)/T.N) * T.N  + (n - 1).val) * ↑T.a)
  · simp only [Nat.cast_add, Nat.cast_mul]
    have h0 :  (Complex.I * ↑↑k * (↑((T.N - 1 + ↑n) / T.N) * ↑T.N + (n - 1).val) * ↑T.a)
      = Complex.I * ↑↑k * ↑((T.N - 1 + ↑n) / T.N) * ↑T.N * ↑T.a + Complex.I * ↑↑k * ((n - 1).val* ↑T.a) := by
      ring
    rw [h0]
    rw [Complex.exp_add]
    rw [quantaWaveNumber_exp_N]
    simp
    congr 1
    simp [mul_assoc]
    left
    left
    rfl
  · have hx : (((T.N - 1 + n)/T.N) * T.N  + (n - 1).val) =
        (T.N - 1 + n) := by
      conv_rhs => rw [← Nat.div_add_mod' (a := T.N - 1 + n) (b := T.N)]
      congr
      by_cases hn : T.N = 1
      · simp [hn]
        have h0 : n = 0 := by
          omega
        subst h0
        simpa using hn
      · rw [@Fin.coe_sub]
        congr
        simp
        exact Nat.one_mod_eq_one.mpr hn
    rw [hx]
    have hl : (Complex.I * ↑↑k * ↑(T.N - 1 + ↑n) * ↑T.a)  =
      Complex.I * ↑↑k * n  * ↑T.a  + Complex.I * ↑↑k * ↑(T.N - 1)  * ↑T.a := by
      simp
      ring
    rw [hl]
    rw [Complex.exp_add]
    congr 1
    have hl : Nat.cast (T.N - 1) = (T.N : ℂ) -1 := by
      refine Nat.cast_pred ?_
      exact Nat.pos_of_neZero T.N
    rw [hl]
    have hl : (Complex.I * ↑↑k * (↑T.N - 1) * ↑T.a) =
      Complex.I * ↑↑k * (1 : ℕ) * ↑T.N * ↑T.a  + (- Complex.I * ↑↑k * ↑T.a) := by
      ring
    rw [hl]
    rw [Complex.exp_add]
    rw [quantaWaveNumber_exp_N]
    simp

lemma quantaWaveNumber_exp_add_one (n : Fin T.N) (k : T.QuantaWaveNumber)  :
    Complex.exp (Complex.I * k * (n + 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (Complex.I * k * T.a) := by
  have hn : n = (n + 1) - 1 := by
    ring
  conv_rhs =>
    rw [hn, quantaWaveNumber_exp_sub_one]
    rw [mul_assoc,←  Complex.exp_add]
    simp


/-- The energy eigenstates of the tight binding chain. -/
noncomputable def energyEigenstate (k : T.QuantaWaveNumber) : T.HilbertSpace :=
  ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩

/-- The energy eigenvalue of the tight binding chain for a `k` in the `BrillouinZone`. -/
noncomputable def energyEigenvalue (k : T.QuantaWaveNumber) : ℝ :=
  T.E0 - 2 * T.t * Real.cos (k * T.a)

lemma hamiltonian_energyEigenstate (k : T.QuantaWaveNumber) :
    T.hamiltonian (T.energyEigenstate k) = (T.energyEigenvalue k : ℂ) • T.energyEigenstate k := by
  rw [energyEigenstate]
  have hp1 : (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n + 1⟩)
    = ∑ n : Fin T.N, Complex.exp (Complex.I * k * (n - 1).val * T.a) • |n⟩ := by
    let e : Fin T.N ≃ Fin T.N := ⟨fun n => n + 1, fun n => n - 1, fun n => add_sub_cancel_right n 1,
      fun n => sub_add_cancel n 1⟩
    conv_rhs => rw [← e.sum_comp]
    congr
    funext n
    simp [e]
  have hm1 : (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n - 1⟩)
    = ∑ n : Fin T.N, Complex.exp (Complex.I * k * (n + 1).val * T.a) • |n⟩ := by
    let e : Fin T.N ≃ Fin T.N := ⟨fun n => n - 1, fun n => n + 1, fun n => sub_add_cancel n 1,
      fun n => add_sub_cancel_right n 1⟩
    conv_rhs => rw [← e.sum_comp]
    congr
    funext n
    simp [e]
  calc
      _ = ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • T.hamiltonian |n⟩ := by
        simp
      _ = ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • (T.E0 • |n⟩
          - T.t • (|n + 1⟩ + |n - 1⟩)) := by
        congr
        funext n
        rw [hamiltonian_apply_localizedState]
        rfl
      _ = T.E0 • (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩)
        - T.t • ((∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n + 1⟩) +
          (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n - 1⟩)) := by
        simp [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.smul_sum]
        congr
        funext n
        simp [smul_sub, smul_smul]
        congr 1
        · rw [smul_comm]
        · rw [smul_comm]
          congr 1
          rw [smul_comm]
      _ = T.E0 • (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩)
        - T.t • ((∑ n : Fin T.N, Complex.exp (Complex.I * k * (n - 1).val * T.a) • |n⟩) +
          (∑ n : Fin T.N, Complex.exp (Complex.I * k * (n + 1).val * T.a) • |n⟩ )) := by
        rw [hp1, hm1]
      _ = ∑ n : Fin T.N, (T.E0 * Complex.exp (Complex.I * k * n * T.a) - T.t *
          (Complex.exp (Complex.I * k * (n - 1).val * T.a) +
          Complex.exp (Complex.I * k * (n + 1).val * T.a))) • |n⟩ := by
        simp [Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_add_distrib, sub_smul, add_smul]
        congr
        · funext n
          rw [← smul_smul]
          rfl
        · rw [← Finset.sum_add_distrib]
          congr
          funext n
          rw [← smul_add, ← add_smul]
          rw [← smul_smul]
          rfl
  rw [Finset.smul_sum]
  congr
  funext n
  conv_rhs => rw [smul_smul]
  congr
  simp [energyEigenvalue]
  rw [sub_mul]
  congr 1
  rw [Complex.cos.eq_1]
  field_simp
  rw [quantaWaveNumber_exp_add_one, quantaWaveNumber_exp_sub_one]
  ring_nf

end TightBindingChain
end CondensedMatter
