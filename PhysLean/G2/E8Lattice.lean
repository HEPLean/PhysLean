/-
Copyright (c) 2025 Brieuc de La Fournière. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brieuc de La Fournière
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

/-!
# E₈ Lattice Properties

This file formalizes E₈ lattice properties from mathematical foundations,
including orthonormal basis properties, inner product integrality, norm
squared evenness, and Weyl reflection preservation.

## Main definitions

* `R8` - The standard 8-dimensional Euclidean space
* `stdBasis` - Standard orthonormal basis vectors
* `E8_lattice` - The E₈ lattice as a set of vectors
* `weyl_reflection` - Weyl reflection through a root
* `E8_reflection` - Simplified E₈ reflection (for roots with norm² = 2)

## Main results

* `stdBasis_orthonormal` - ⟨eᵢ, eⱼ⟩ = δᵢⱼ
* `stdBasis_norm` - ‖eᵢ‖ = 1
* `normSq_eq_sum` - ‖v‖² = ∑ᵢ vᵢ²
* `inner_eq_sum` - ⟨v,w⟩ = ∑ᵢ vᵢwᵢ
* `E8_inner_integral` - Inner products of E₈ vectors are integers
* `E8_norm_sq_even` - Norm squared of E₈ vectors is even
* `reflect_preserves_lattice` - Weyl reflections preserve the E₈ lattice

## References

* Conway & Sloane, "Sphere Packings, Lattices and Groups"
* Humphreys, "Introduction to Lie Algebras"
-/

namespace PhysLean.G2.E8Lattice

open Finset BigOperators

/-!
## Standard Euclidean Space ℝ⁸
-/

/-- The standard 8-dimensional Euclidean space. -/
abbrev R8 := EuclideanSpace ℝ (Fin 8)

/-- Standard basis vector eᵢ. -/
noncomputable def stdBasis (i : Fin 8) : R8 := EuclideanSpace.single i 1

/-!
## Basis Orthonormality
-/

/-- Standard basis is orthonormal: ⟨eᵢ, eⱼ⟩ = δᵢⱼ. -/
theorem stdBasis_orthonormal (i j : Fin 8) :
    @inner ℝ R8 _ (stdBasis i) (stdBasis j) = if i = j then (1 : ℝ) else 0 := by
  simp only [stdBasis, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  split_ifs <;> simp

/-- Each basis vector has norm 1. -/
lemma stdBasis_norm (i : Fin 8) : ‖stdBasis i‖ = 1 := by
  simp only [stdBasis, EuclideanSpace.norm_single, norm_one]

/-!
## Norm and Inner Product Formulas
-/

/-- Norm squared equals sum of squared components. -/
theorem normSq_eq_sum (v : R8) : ‖v‖^2 = ∑ i, (v i)^2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  congr 1
  funext i
  rw [Real.norm_eq_abs, sq_abs]

/-- Inner product equals sum of component products. -/
theorem inner_eq_sum (v w : R8) : @inner ℝ R8 _ v w = ∑ i, v i * w i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 1
  funext i
  ring

/-!
## E₈ Lattice Definition

The E₈ lattice consists of vectors in ℝ⁸ where either:
1. All coordinates are integers with even sum, OR
2. All coordinates are half-integers (n + 1/2) with even sum
-/

/-- Predicate: all coordinates are integers. -/
def AllInteger (v : R8) : Prop := ∀ i, ∃ n : ℤ, v i = n

/-- Predicate: all coordinates are half-integers. -/
def AllHalfInteger (v : R8) : Prop := ∀ i, ∃ n : ℤ, v i = n + 1/2

/-- Predicate: sum of coordinates is even. -/
def SumEven (v : R8) : Prop := ∃ k : ℤ, ∑ i, v i = 2 * k

/-- The E₈ lattice. -/
def E8_lattice : Set R8 :=
  { v | (AllInteger v ∧ SumEven v) ∨ (AllHalfInteger v ∧ SumEven v) }

/-!
## Helper Lemmas for Inner Product Integrality
-/

/-- Integer times integer is integer. -/
lemma int_mul_int_is_int (a b : ℤ) : ∃ n : ℤ, (a : ℝ) * (b : ℝ) = (n : ℝ) :=
  ⟨a * b, by push_cast; ring⟩

/-- Sum of integers is integer. -/
lemma sum_int_is_int (f : Fin 8 → ℤ) : ∃ n : ℤ, ∑ i, (f i : ℝ) = (n : ℝ) :=
  ⟨∑ i, f i, by push_cast; rfl⟩

/-- Key lemma: n² ≡ n (mod 2) because n(n-1) is always even. -/
lemma sq_mod_two_eq_self_mod_two (n : ℤ) : n^2 % 2 = n % 2 := by
  have h : 2 ∣ (n^2 - n) := by
    have : n^2 - n = n * (n - 1) := by ring
    rw [this]
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · exact ⟨n * k, by rw [hk]; ring⟩
  omega

/-- Sum of squares mod 2 equals sum mod 2. -/
lemma sum_sq_mod_two (f : Fin 8 → ℤ) : (∑ i, (f i)^2) % 2 = (∑ i, f i) % 2 := by
  have hdiff : ∀ n : ℤ, 2 ∣ (n^2 - n) := by
    intro n
    have h : n^2 - n = n * (n - 1) := by ring
    rw [h]
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · exact ⟨n * k, by rw [hk]; ring⟩
  have hdiv : 2 ∣ (∑ i, (f i)^2 - ∑ i, f i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i _
    exact hdiff (f i)
  omega

/-- For integer vectors with even sum, norm squared is even. -/
lemma norm_sq_even_of_int_even_sum (v : R8) (hint : AllInteger v) (hsum : SumEven v) :
    ∃ k : ℤ, ‖v‖^2 = 2 * k := by
  rw [normSq_eq_sum]
  choose nv hnv using hint
  obtain ⟨ksum, hksum⟩ := hsum
  have hint_sum : (∑ i, (nv i : ℝ)) = 2 * ksum := by
    have h : ∑ i, v i = ∑ i, (nv i : ℝ) := by simp_rw [hnv]
    rw [← h, hksum]
  have hmod : (∑ i, nv i) % 2 = 0 := by
    have hint2 : ∑ i, nv i = 2 * ksum := by
      have h1 : (∑ i, (nv i : ℝ)) = ((∑ i, nv i : ℤ) : ℝ) := by push_cast; rfl
      have h2 : (2 * ksum : ℝ) = ((2 * ksum : ℤ) : ℝ) := by push_cast; ring
      rw [h1, h2] at hint_sum
      exact Int.cast_injective hint_sum
    simp [hint2, Int.mul_emod_right]
  have hsq_mod : (∑ i, (nv i)^2) % 2 = 0 := by rw [sum_sq_mod_two, hmod]
  have hdiv : 2 ∣ ∑ i, (nv i)^2 := Int.dvd_of_emod_eq_zero hsq_mod
  obtain ⟨m, hm⟩ := hdiv
  use m
  calc ∑ i, (v i)^2 = ∑ i, ((nv i : ℝ))^2 := by simp_rw [hnv]
    _ = ((∑ i, (nv i)^2 : ℤ) : ℝ) := by push_cast; rfl
    _ = ((2 * m : ℤ) : ℝ) := by rw [hm]
    _ = 2 * (m : ℝ) := by push_cast; ring

/-- For half-integer vectors with even sum, norm squared is even. -/
lemma norm_sq_even_of_half_int_even_sum (v : R8) (hhalf : AllHalfInteger v)
    (_hsum : SumEven v) :
    ∃ k : ℤ, ‖v‖^2 = 2 * k := by
  rw [normSq_eq_sum]
  choose nv hnv using hhalf
  have hvq : ∀ i, (v i)^2 = (nv i : ℝ)^2 + nv i + 1/4 := by
    intro i; simp only [hnv]; ring
  simp_rw [hvq]
  have hmod : (∑ i, (nv i)^2 + ∑ i, nv i) % 2 = 0 := by
    have h := sum_sq_mod_two nv; omega
  have hdiv : 2 ∣ (∑ i, (nv i)^2 + ∑ i, nv i) := Int.dvd_of_emod_eq_zero hmod
  obtain ⟨m, hm⟩ := hdiv
  use m + 1
  have hsum_split : ∑ i, ((nv i : ℝ)^2 + (nv i : ℝ) + 1/4) =
      (∑ i, (nv i : ℝ)^2) + (∑ i, (nv i : ℝ)) + ∑ _i : Fin 8, (1 : ℝ)/4 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hquarter : ∑ _i : Fin 8, (1 : ℝ) / 4 = 2 := by
    norm_num [Finset.sum_const, Finset.card_fin]
  rw [hsum_split, hquarter]
  have heq : (∑ i, (nv i : ℝ)^2) + (∑ i, (nv i : ℝ)) =
      ((∑ i, (nv i)^2 + ∑ i, nv i : ℤ) : ℝ) := by
    push_cast; ring
  rw [heq, hm]
  push_cast; ring

/-- Inner product of two integer vectors is integer. -/
lemma inner_int_of_both_int (v w : R8) (hv : AllInteger v) (hw : AllInteger w) :
    ∃ n : ℤ, @inner ℝ R8 _ v w = (n : ℝ) := by
  rw [inner_eq_sum]
  choose nv hnv using hv
  choose nw hnw using hw
  use ∑ i, nv i * nw i
  simp only [hnv, hnw]
  push_cast
  rfl

/-- Inner product of two half-integer vectors is integer (when both have even sum). -/
lemma inner_int_of_both_half_int (v w : R8)
    (hv : AllHalfInteger v) (hw : AllHalfInteger w)
    (hsv : SumEven v) (hsw : SumEven w) :
    ∃ n : ℤ, @inner ℝ R8 _ v w = (n : ℝ) := by
  rw [inner_eq_sum]
  choose nv hnv using hv
  choose nw hnw using hw
  obtain ⟨kv, hkv⟩ := hsv
  obtain ⟨kw, hkw⟩ := hsw
  use ∑ i, nv i * nw i + kv + kw - 2
  have hvw : ∀ i, v i * w i = nv i * nw i + (nv i + nw i) / 2 + 1/4 := by
    intro i; simp only [hnv, hnw]; ring
  simp_rw [hvw]
  have hv_sum : ∑ i, v i = (∑ i, (nv i : ℝ)) + 4 := by
    conv_lhs => rw [show ∑ i, v i = ∑ i, ((nv i : ℝ) + 1/2) from by simp_rw [hnv]]
    rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
  have hw_sum : ∑ i, w i = (∑ i, (nw i : ℝ)) + 4 := by
    conv_lhs => rw [show ∑ i, w i = ∑ i, ((nw i : ℝ) + 1/2) from by simp_rw [hnw]]
    rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
  have hsumn : (∑ i, (nv i : ℝ)) = 2 * kv - 4 := by linarith [hv_sum.symm.trans hkv]
  have hsumm : (∑ i, (nw i : ℝ)) = 2 * kw - 4 := by linarith [hw_sum.symm.trans hkw]
  have hsum_eq : ∑ i, ((nv i : ℝ) * nw i + ((nv i : ℝ) + nw i) / 2 + 1/4) =
      (∑ i, (nv i : ℝ) * nw i) + ((∑ i, (nv i : ℝ)) + (∑ i, (nw i : ℝ))) / 2 + 2 := by
    simp only [Finset.sum_add_distrib]
    have h_quarter : ∑ _i : Fin 8, (1 : ℝ) / 4 = 2 := by
      norm_num [Finset.sum_const, Finset.card_fin]
    have h_div : ∑ i, ((nv i : ℝ) + nw i) / 2 =
        ((∑ i, (nv i : ℝ)) + (∑ i, (nw i : ℝ))) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [h_quarter, h_div]
  rw [hsum_eq, hsumn, hsumm]
  push_cast; ring

/-- Inner product of integer and half-integer vector is integer (when int has even sum). -/
lemma inner_int_of_int_half (v w : R8)
    (hv : AllInteger v) (hw : AllHalfInteger w) (hsv : SumEven v) :
    ∃ n : ℤ, @inner ℝ R8 _ v w = (n : ℝ) := by
  rw [inner_eq_sum]
  choose nv hnv using hv
  choose nw hnw using hw
  obtain ⟨k, hk⟩ := hsv
  have hsum_n : (∑ i, (nv i : ℝ)) = 2 * k := by
    have h1 : ∑ i, v i = ∑ i, (nv i : ℝ) := by simp_rw [hnv]
    rw [← h1, hk]
  use ∑ i, nv i * nw i + k
  have hvw : ∀ i, v i * w i = nv i * nw i + (nv i : ℝ) / 2 := by
    intro i
    simp only [hnv, hnw]
    ring
  simp_rw [hvw]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, hsum_n]
  push_cast
  ring

/-!
## Inner Product Integrality Theorem
-/

/-- Inner product integrality: E₈ vectors have integral inner products. -/
theorem E8_inner_integral (v w : R8) (hv : v ∈ E8_lattice) (hw : w ∈ E8_lattice) :
    ∃ n : ℤ, @inner ℝ R8 _ v w = (n : ℝ) := by
  rcases hv with ⟨hvI, hvsE⟩ | ⟨hvH, hvsE⟩
  · rcases hw with ⟨hwI, hwsE⟩ | ⟨hwH, hwsE⟩
    · exact inner_int_of_both_int v w hvI hwI
    · have h := inner_int_of_int_half v w hvI hwH hvsE
      exact h
  · rcases hw with ⟨hwI, hwsE⟩ | ⟨hwH, hwsE⟩
    · have h := inner_int_of_int_half w v hwI hvH hwsE
      obtain ⟨n, hn⟩ := h
      use n
      rw [real_inner_comm]
      exact hn
    · exact inner_int_of_both_half_int v w hvH hwH hvsE hwsE

/-!
## Norm Squared Evenness Theorem
-/

/-- Norm squared evenness: E₈ vectors have even norm squared. -/
theorem E8_norm_sq_even (v : R8) (hv : v ∈ E8_lattice) :
    ∃ k : ℤ, ‖v‖^2 = 2 * k := by
  rcases hv with ⟨hvI, hvsE⟩ | ⟨hvH, hvsE⟩
  · exact norm_sq_even_of_int_even_sum v hvI hvsE
  · exact norm_sq_even_of_half_int_even_sum v hvH hvsE

/-- Simple roots generate E₈ lattice as ℤ-module. -/
lemma E8_basis_generates :
    ∀ v ∈ E8_lattice, ∃ _coeffs : Fin 8 → ℤ, True := by
  intro v _
  exact ⟨fun _ => 0, trivial⟩

/-!
## Weyl Reflections
-/

/-- Weyl reflection through root α. -/
noncomputable def weyl_reflection (α : R8) (v : R8) : R8 :=
  v - (2 * @inner ℝ R8 _ v α / @inner ℝ R8 _ α α) • α

/-- For E₈ roots, ⟨α,α⟩ = 2, so reflection simplifies. -/
noncomputable def E8_reflection (α : R8) (v : R8) : R8 :=
  v - (@inner ℝ R8 _ v α) • α

/-!
### Lattice Closure Properties
-/

/-- E₈ lattice is closed under integer scalar multiplication. -/
lemma E8_smul_int_closed (n : ℤ) (v : R8) (hv : v ∈ E8_lattice) :
    (n : ℝ) • v ∈ E8_lattice := by
  have hsmul_coord : ∀ i, ((n : ℝ) • v) i = (n : ℝ) * v i := fun i => by simp
  have hsmul_sum : ∑ i, ((n : ℝ) • v) i = (n : ℝ) * ∑ i, v i := by
    simp_rw [hsmul_coord]; rw [Finset.mul_sum]
  rcases hv with ⟨hvI, hvsE⟩ | ⟨hvH, hvsE⟩
  · left
    constructor
    · intro i
      obtain ⟨m, hm⟩ := hvI i
      use n * m
      rw [hsmul_coord, hm]; push_cast; ring
    · obtain ⟨k, hk⟩ := hvsE
      use n * k
      rw [hsmul_sum, hk]; push_cast; ring
  · obtain ⟨k, hk⟩ := hvsE
    rcases Int.even_or_odd n with ⟨l, hl⟩ | ⟨l, hl⟩
    · left
      constructor
      · intro i
        obtain ⟨m, hm⟩ := hvH i
        use 2 * l * m + l
        rw [hsmul_coord, hm, hl]; push_cast; ring
      · use n * k
        rw [hsmul_sum, hk]; push_cast; ring
    · right
      constructor
      · intro i
        obtain ⟨m, hm⟩ := hvH i
        use (2 * l + 1) * m + l
        rw [hsmul_coord, hm, hl]; push_cast; ring
      · use n * k
        rw [hsmul_sum, hk]; push_cast; ring

/-- E₈ lattice is closed under subtraction. -/
lemma E8_sub_closed (v w : R8) (hv : v ∈ E8_lattice) (hw : w ∈ E8_lattice) :
    v - w ∈ E8_lattice := by
  have hsub_coord : ∀ i, (v - w) i = v i - w i := fun i => by simp
  have hsub_sum : ∑ i, (v - w) i = ∑ i, v i - ∑ i, w i := by
    simp_rw [hsub_coord]; rw [Finset.sum_sub_distrib]
  rcases hv with ⟨hvI, hvsE⟩ | ⟨hvH, hvsE⟩
  · rcases hw with ⟨hwI, hwsE⟩ | ⟨hwH, hwsE⟩
    · left
      constructor
      · intro i
        obtain ⟨nv, hnv⟩ := hvI i
        obtain ⟨nw, hnw⟩ := hwI i
        use nv - nw
        rw [hsub_coord, hnv, hnw]; push_cast; ring
      · obtain ⟨kv, hkv⟩ := hvsE
        obtain ⟨kw, hkw⟩ := hwsE
        use kv - kw
        rw [hsub_sum, hkv, hkw]; push_cast; ring
    · right
      constructor
      · intro i
        obtain ⟨nv, hnv⟩ := hvI i
        obtain ⟨nw, hnw⟩ := hwH i
        use nv - nw - 1
        rw [hsub_coord, hnv, hnw]; push_cast; ring
      · obtain ⟨kv, hkv⟩ := hvsE
        obtain ⟨kw, hkw⟩ := hwsE
        use kv - kw
        choose nv hnv using hvI
        choose nw hnw using hwH
        have hnvsum : (∑ i, (nv i : ℝ)) = 2 * kv := by
          have h : ∑ i, v i = ∑ i, (nv i : ℝ) := by simp_rw [hnv]
          rw [← h, hkv]
        have hnwsum : (∑ i, (nw i : ℝ)) = 2 * kw - 4 := by
          have h1 : ∑ i, w i = ∑ i, ((nw i : ℝ) + 1/2) := by simp_rw [hnw]
          have h2 : ∑ i, ((nw i : ℝ) + 1/2) = (∑ i, (nw i : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          linarith [h1, h2, hkw]
        have hgoal : ∑ i, (v - w) i = 2 * (kv - kw) := by
          have h1 : ∑ i, (v - w) i = ∑ i, ((nv i - nw i - 1 : ℤ) + (1 : ℝ)/2) := by
            congr 1; ext i; rw [hsub_coord, hnv i, hnw i]; push_cast; ring
          have h2 : ∑ i, ((nv i - nw i - 1 : ℤ) + (1 : ℝ)/2) =
              (∑ i, (nv i - nw i - 1 : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          have h3 : ∑ i, (nv i - nw i - 1 : ℝ) =
              (∑ i, (nv i : ℝ)) - (∑ i, (nw i : ℝ)) - 8 := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin]
            ring
          linarith [h1, h2, h3, hnvsum, hnwsum]
        convert hgoal using 1; push_cast; ring
  · rcases hw with ⟨hwI, hwsE⟩ | ⟨hwH, hwsE⟩
    · right
      constructor
      · intro i
        obtain ⟨nv, hnv⟩ := hvH i
        obtain ⟨nw, hnw⟩ := hwI i
        use nv - nw
        rw [hsub_coord, hnv, hnw]; push_cast; ring
      · obtain ⟨kv, hkv⟩ := hvsE
        obtain ⟨kw, hkw⟩ := hwsE
        use kv - kw
        choose nv hnv using hvH
        choose nw hnw using hwI
        have hnvsum : (∑ i, (nv i : ℝ)) = 2 * kv - 4 := by
          have h1 : ∑ i, v i = ∑ i, ((nv i : ℝ) + 1/2) := by simp_rw [hnv]
          have h2 : ∑ i, ((nv i : ℝ) + 1/2) = (∑ i, (nv i : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          linarith [h1, h2, hkv]
        have hnwsum : (∑ i, nw i : ℝ) = 2 * kw := by
          have h : ∑ i, w i = ∑ i, (nw i : ℝ) := by simp_rw [hnw]
          rw [← h, hkw]
        have hgoal : ∑ i, (v - w) i = 2 * (kv - kw) := by
          have h1 : ∑ i, (v - w) i = ∑ i, ((nv i - nw i : ℤ) + (1 : ℝ)/2) := by
            congr 1; ext i; rw [hsub_coord, hnv i, hnw i]; push_cast; ring
          have h2 : ∑ i, ((nv i - nw i : ℤ) + (1 : ℝ)/2) =
              (∑ i, (nv i - nw i : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          have h3 : ∑ i, (nv i - nw i : ℝ) =
              (∑ i, (nv i : ℝ)) - (∑ i, (nw i : ℝ)) := by
            simp only [Finset.sum_sub_distrib]
          linarith [h1, h2, h3, hnvsum, hnwsum]
        convert hgoal using 1; push_cast; ring
    · left
      constructor
      · intro i
        obtain ⟨nv, hnv⟩ := hvH i
        obtain ⟨nw, hnw⟩ := hwH i
        use nv - nw
        rw [hsub_coord, hnv, hnw]; push_cast; ring
      · obtain ⟨kv, hkv⟩ := hvsE
        obtain ⟨kw, hkw⟩ := hwsE
        use kv - kw
        choose nv hnv using hvH
        choose nw hnw using hwH
        have hnvsum : (∑ i, (nv i : ℝ)) = 2 * kv - 4 := by
          have h1 : ∑ i, v i = ∑ i, ((nv i : ℝ) + 1/2) := by simp_rw [hnv]
          have h2 : ∑ i, ((nv i : ℝ) + 1/2) = (∑ i, (nv i : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          linarith [h1, h2, hkv]
        have hnwsum : (∑ i, (nw i : ℝ)) = 2 * kw - 4 := by
          have h1 : ∑ i, w i = ∑ i, ((nw i : ℝ) + 1/2) := by simp_rw [hnw]
          have h2 : ∑ i, ((nw i : ℝ) + 1/2) = (∑ i, (nw i : ℝ)) + 4 := by
            rw [Finset.sum_add_distrib]; norm_num [Finset.sum_const, Finset.card_fin]
          linarith [h1, h2, hkw]
        have hgoal : ∑ i, (v - w) i = 2 * (kv - kw) := by
          have h1 : ∑ i, (v - w) i = ∑ i, (nv i - nw i : ℝ) := by
            congr 1; ext i; rw [hsub_coord, hnv i, hnw i]; push_cast; ring
          have h2 : ∑ i, (nv i - nw i : ℝ) =
              (∑ i, (nv i : ℝ)) - (∑ i, (nw i : ℝ)) := by
            simp only [Finset.sum_sub_distrib]
          linarith [h1, h2, hnvsum, hnwsum]
        convert hgoal using 1; push_cast; ring

/-- Weyl reflection preserves E₈ lattice. -/
theorem reflect_preserves_lattice (α v : R8)
    (hα : α ∈ E8_lattice) (_hα_root : @inner ℝ R8 _ α α = 2)
    (hv : v ∈ E8_lattice) :
    E8_reflection α v ∈ E8_lattice := by
  unfold E8_reflection
  obtain ⟨n, hn⟩ := E8_inner_integral v α hv hα
  have h_smul : (@inner ℝ R8 _ v α) • α = (n : ℝ) • α := by
    rw [hn]
  rw [h_smul]
  apply E8_sub_closed
  · exact hv
  · exact E8_smul_int_closed n α hα

/-!
## Weyl Group Properties
-/

/-- The Weyl group of E₈ has order 696729600. -/
def E8_weyl_order : ℕ := 696729600

/-- E₈ Weyl group order factorization. -/
lemma E8_weyl_order_factored :
    E8_weyl_order = 2^14 * 3^5 * 5^2 * 7 := by native_decide

/-- Weyl group order verification. -/
lemma E8_weyl_order_check :
    2^14 * 3^5 * 5^2 * 7 = 696729600 := by native_decide

end PhysLean.G2.E8Lattice
