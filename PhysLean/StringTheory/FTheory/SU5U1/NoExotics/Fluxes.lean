/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.ChiralityFlux
/-!

# Chirality flux and hypercharge flux and no exotics

The condition on the matter content for there to be no exotics in the spectrum
leads to constraints on the allowed combintation of `ChiralityFlux`
and `HyperchargeFlux` of the matter content.

This file contains these constraints for the 5-bar and
10d matter representations.

Note: the module depends on `NoExotics.ChiralityFlux` but `NoExotics.HyperchargeFlux` depends on
  this module.

## Important results

- `quantaBarFiveMatter_MN_mem` - Specifies the multisets of `ChiralityFlux × HyperChargeFlux`
  carried by the 5-bar matter representations allowed by the no exotics conditions.
- `quantaTen_chiralityFlux_mem` - Specifies the allowed multisets of
  `ChiralityFlux × HyperChargeFlux` carried by the 10d matter representations allowed by the
  no exotics conditions.
-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

/-!

## Five-bar matter

-/

lemma quantaBarFiveMatter_MN_abs_le_three (h3L : 𝓜.ThreeLeptonDoublets) :
    ∀ a ∈ (𝓜.quantaBarFiveMatter.map QuantaBarFive.MN), |a.1 + a.2| ≤ 3 := by
  have hC := 𝓜.quantaBarFiveMatter_map_MN_sum_of_threeLeptonDoublets h3L
  rw [← hC]
  intro a ha
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro x hx
    simp at hx
    obtain ⟨a', b, c, ha, rfl⟩ := hx
    exact abs_nonneg (QuantaBarFive.M (a', b, c) + QuantaBarFive.N (a', b, c))
  · simp at ha
    obtain ⟨a, b, c, ha, rfl⟩ := ha
    simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map, Prod.exists]
    use a, b, c

/-!

## Some auxiliary lemmas regarding multisets

-/
lemma multiset_eq_of_prod_fst_eq_five {c1 c2 c3 c4 c5 : ℤ}
    (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {c1, c2, c3, c4, c5}) :
    ∃ n1 n2 n3 n4 n5, S = {(c1, n1), (c2, n2), (c3, n3), (c4, n4), (c5, n5)} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
    Prod.exists, exists_and_right, exists_eq_right] at hprod
  obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
  obtain ⟨_, n2, h2, rfl, hi⟩ := hi
  obtain ⟨_, n3, h3, rfl, hi⟩ := hi
  obtain ⟨_, n4, h4, rfl, hi⟩ := hi
  obtain ⟨n5, hi⟩ := hi
  rw [← (Multiset.cons_erase h1), ← (Multiset.cons_erase h2),
    ← (Multiset.cons_erase h3), ← (Multiset.cons_erase h4), hi]
  use n1, n2, n3, n4, n5
  simp

lemma multiset_eq_of_prod_fst_eq_four {c1 c2 c3 c4 : ℤ}
    (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {c1, c2, c3, c4}) :
    ∃ n1 n2 n3 n4, S = {(c1, n1), (c2, n2), (c3, n3), (c4, n4)} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
    Prod.exists, exists_and_right, exists_eq_right] at hprod
  obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
  obtain ⟨_, n2, h2, rfl, hi⟩ := hi
  obtain ⟨_, n3, h3, rfl, hi⟩ := hi
  obtain ⟨n4, hi⟩ := hi
  rw [← (Multiset.cons_erase h1), ← (Multiset.cons_erase h2),
    ← (Multiset.cons_erase h3), hi]
  use n1, n2, n3, n4
  simp

lemma multiset_eq_of_prod_fst_eq_three {c1 c2 c3 : ℤ}
    (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {c1, c2, c3}) :
    ∃ n1 n2 n3, S = {(c1, n1), (c2, n2), (c3, n3)} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
    Prod.exists, exists_and_right, exists_eq_right] at hprod
  obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
  obtain ⟨_, n2, h2, rfl, hi⟩ := hi
  obtain ⟨n3, hi⟩ := hi
  rw [← (Multiset.cons_erase h1), ← (Multiset.cons_erase h2), hi]
  use n1, n2, n3
  simp

lemma multiset_eq_of_prod_fst_eq_two {c1 c2 : ℤ}
    (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {c1, c2}) :
    ∃ n1 n2, S = {(c1, n1), (c2, n2)} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
    Prod.exists, exists_and_right, exists_eq_right] at hprod
  obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
  obtain ⟨n2, hi⟩ := hi
  rw [← (Multiset.cons_erase h1), hi]
  use n1, n2
  simp

lemma multiset_eq_of_prod_fst_eq_one {c1 : ℤ}
    (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {c1}) :
    ∃ n1, S = {(c1, n1)} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
    Prod.exists, exists_and_right, exists_eq_right] at hprod
  obtain ⟨n1, hi⟩ := hprod
  rw [hi]
  use n1

-- 30 cases overall.
lemma quantaBarFiveMatter_MN_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map QuantaBarFive.MN
    ∈ ({
    -- {1, 1, 1, 0, 0} (2 cases)
    {(1, -1), (1, -1), (1, -1), (0, 1), (0, 2)}, {(1, -1), (1, -1), (1, 0), (0, 1), (0, 1)},
    -- {1, 1, 1, 0} (4 cases)
    {(1, 1), (1, -1), (1, -1), (0, 1)}, {(1, 0), (1, 0), (1, -1), (0, 1)},
    {(1, -1), (1, 0), (1, -1), (0, 2)}, {(1, -1), (1, -1), (1, -1), (0, 3)},
    -- {1, 1, 1} (3 cases)
    {(1, -1), (1, -1), (1, 2)}, {(1, -1), (1, 0), (1, 1)}, {(1, 0), (1, 0), (1, 0)},
    -- {1, 2, 0, 0, 0} (1 case)
    {(1, -1), (2, -2), (0, 1), (0, 1), (0, 1)},
    -- {1, 2, 0, 0} (3 cases)
    {(1, -1), (2, -2), (0, 1), (0, 2)}, {(1, -1), (2, -1), (0, 1), (0, 1)},
    {(1, 0), (2, -2), (0, 1), (0, 1)},
    -- {1, 2, 0} (6 cases)
    {(1, 1), (2, -2), (0, 1)}, {(1, 0), (2, -1), (0, 1)}, {(1, 0), (2, -2), (0, 2)},
    {(1, -1), (2, 0), (0, 1)}, {(1, -1), (2, -1), (0, 2)}, {(1, -1), (2, -2), (0, 3)},
    -- {1, 2} (4 cases)
    {(1, -1), (2, 1)}, {(1, 0), (2, 0)}, {(1, 1), (2, -1)}, {(1, 2), (2, -2)},
    -- {3, 0, 0, 0} (1 cases)
    {(3, -3), (0, 1), (0, 1), (0, 1)},
    -- {3, 0, 0} (2 cases)
    {(3, -3), (0, 1), (0, 2)}, {(3, -2), (0, 1), (0, 1)},
    -- {3, 0} (3 cases)
    {(3, -3), (0, 3)}, {(3, -2), (0, 2)}, {(3, -1), (0, 1)},
    -- {3} (1 cases)
    {(3, 0)}} : Finset (Multiset (ChiralityFlux × HyperChargeFlux))) := by
  have hr := quantaBarFiveMatter_chiralityFlux_mem h3 h3L
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  have hC1 := 𝓜.quantaBarFiveMatter_map_MN_sum_of_noExotics he
  have hC2 := 𝓜.quantaBarFiveMatter_map_MN_bound_N_of_noExotics he
  have hC3 := 𝓜.quantaBarFiveMatter_map_MN_sum_of_threeLeptonDoublets h3L
  have hC4 := 𝓜.quantaBarFiveMatter_map_MN_not_both_zero
  have hC5 := 𝓜.quantaBarFiveMatter_MN_abs_le_three h3L
  have hl0 {m : ℤ} (hm : -1 - 0 ≤ m ∧ m ≤ 3) (hx : m ≠ 0) :
      m ∈ ({-1, 1, 2, 3} : Finset ℤ) := by
    simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hl1 {m : ℤ} (hm : -1 - 1 ≤ m ∧ m ≤ 3) (hm2 : |1 + m| ≤ 3) :
      m ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
    have hl1' : m ∈ ({-2, -1, 0, 1, 2, 3} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    revert hm
    revert hm2
    fin_cases hl1' <;> decide
  have hl2 {m : ℤ} (hm : -1 - 2 ≤ m ∧ m ≤ 3) (hm2 : |2 + m| ≤ 3) :
      m ∈ ({-3, -2, -1, 0, 1} : Finset ℤ) := by
    have hl1' : m ∈ ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    revert hm
    revert hm2
    fin_cases hl1' <;> decide
  have hl3 {m : ℤ} (hm : -1 - 3 ≤ m ∧ m ≤ 3) (hm2 : |3 + m| ≤ 3) :
      m ∈ ({-4, -3, -2, -1, 0} : Finset ℤ) := by
    have hl1' : m ∈ ({-4, -3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    revert hm
    revert hm2
    fin_cases hl1' <;> decide
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · /- The case of `{1, 1, 1, 0, 0}` -/
    obtain ⟨n1, n2, n3, n4, n5, hS⟩ :=
      multiset_eq_of_prod_fst_eq_five (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl1 hC2.2.1 hC5.2.1
    have hln3 := hl1 hC2.2.2.1 hC5.2.2.1
    have hln4 := hl0 hC2.2.2.2.1 hC4.1
    have hln5 := hl0 hC2.2.2.2.2 hC4.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3; revert n4; revert n5
    decide
  · /- The case of `{1, 1, 1, 0}` -/
    obtain ⟨n1, n2, n3, n4, hS⟩ :=
      multiset_eq_of_prod_fst_eq_four (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl1 hC2.2.1 hC5.2.1
    have hln3 := hl1 hC2.2.2.1 hC5.2.2.1
    have hln4 := hl0 hC2.2.2.2 hC4
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3; revert n4
    decide
  · /- The case of `{1, 1, 1}` -/
    obtain ⟨n1, n2, n3, hS⟩ :=
      multiset_eq_of_prod_fst_eq_three (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl1 hC2.2.1 hC5.2.1
    have hln3 := hl1 hC2.2.2 hC5.2.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3;
    decide
  · /- The case of `{1, 2, 0, 0, 0}` -/
    obtain ⟨n1, n2, n3, n4, n5, hS⟩ :=
      multiset_eq_of_prod_fst_eq_five (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl2 hC2.2.1 hC5.2.1
    have hln3 := hl0 hC2.2.2.1 hC4.2.1
    have hln4 := hl0 hC2.2.2.2.1 hC4.2.2.1
    have hln5 := hl0 hC2.2.2.2.2 hC4.2.2.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3; revert n4; revert n5
    decide
  · /- The case of `{1, 2, 0, 0}` -/
    obtain ⟨n1, n2, n3, n4, hS⟩ :=
      multiset_eq_of_prod_fst_eq_four (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl2 hC2.2.1 hC5.2.1
    have hln3 := hl0 hC2.2.2.1 hC4.2.1
    have hln4 := hl0 hC2.2.2.2 hC4.2.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3; revert n4;
    decide
  · /- The case of `{1, 2, 0}` -/
    obtain ⟨n1, n2, n3, hS⟩ :=
      multiset_eq_of_prod_fst_eq_three (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl2 hC2.2.1 hC5.2.1
    have hln3 := hl0 hC2.2.2 hC4.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3;
    decide
  · /- The case of `{1, 2}` -/
    obtain ⟨n1, n2, hS⟩ :=
      multiset_eq_of_prod_fst_eq_two (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl1 hC2.1 hC5.1
    have hln2 := hl2 hC2.2 hC5.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2;
    decide
  · /- The case of `{3, 0, 0, 0}` -/
    obtain ⟨n1, n2, n3, n4, hS⟩ :=
      multiset_eq_of_prod_fst_eq_four (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl3 hC2.1 hC5.1
    have hln2 := hl0 hC2.2.1 hC4.2.1
    have hln3 := hl0 hC2.2.2.1 hC4.2.2.1
    have hln4 := hl0 hC2.2.2.2 hC4.2.2.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3; revert n4;
    decide
  · /- The case of `{3, 0, 0}` -/
    obtain ⟨n1, n2, n3, hS⟩ :=
      multiset_eq_of_prod_fst_eq_three (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl3 hC2.1 hC5.1
    have hln2 := hl0 hC2.2.1 hC4.2.1
    have hln3 := hl0 hC2.2.2 hC4.2.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2; revert n3;
    decide
  · /- The case of `{3, 0}` -/
    obtain ⟨n1, n2, hS⟩ :=
      multiset_eq_of_prod_fst_eq_two (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl3 hC2.1 hC5.1
    have hln2 := hl0 hC2.2 hC4.2
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1; revert n2;
    decide
  · /- The case of `{3}` -/
    obtain ⟨n1, hS⟩ :=
      multiset_eq_of_prod_fst_eq_one (𝓜.quantaBarFiveMatter.map QuantaTen.MN) (by simpa using hr)
    rw [hS] at hC1 hC2 hC3 hC4 hC5 ⊢
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, Int.reduceNeg, neg_zero, forall_eq, zero_add, ne_eq, one_ne_zero,
      IsEmpty.forall_iff, forall_const, true_and] at hC1 hC2 hC3 hC4 hC5
    have hln1 := hl3 hC2 hC5
    clear hr hS hC5 h3 he hC2 hC4
    revert hC1 hC3
    revert n1;
    decide
/-!

## Ten-d matter

-/

/-- The condition of no exotics in the matter spectrum constrains the allowed
  values of the `ChiralityFlux` and `HyperChargeFlux` carried by the 10d representations to be one
  of the following Multisets:

  `{(1, 0), (1, 0), (1, 0)}`, `{(1, 1), (1, -1), (1, 0)}`,
      `{(1, 0), (2, 0)}`, `{(1, -1), (2, 1)}`, `{(1, 1), (2, -1)}, {(3, 0)}`.
-/
lemma quantaTen_MN_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map QuantaTen.MN
    ∈ ({{(1, 0), (1, 0), (1, 0)}, {(1, 1), (1, -1), (1, 0)},
      {(1, 0), (2, 0)}, {(1, -1), (2, 1)}, {(1, 1), (2, -1)}, {(3, 0)}} :
      Finset (Multiset (ChiralityFlux × HyperChargeFlux))) := by
  have hr := quantaTen_chiralityFlux_mem he h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with hr | hr | hr
  · /- The case of Chirality flux equal to `{1, 1, 1}`. -/
    have hS (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {1, 1, 1}) :
        ∃ n1 n2 n3, S = {(1, n1), (1, n2), (1, n3)} := by
      simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
        Prod.exists, exists_and_right, exists_eq_right] at hprod
      obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
      obtain ⟨_, n2, h2, rfl, hi⟩ := hi
      obtain ⟨n3, hi⟩ := hi
      rw [← (Multiset.cons_erase h1), ← (Multiset.cons_erase h2), hi]
      use n1, n2
      simp
    obtain ⟨n1, n2, n3, hS⟩ := hS (𝓜.quantaTen.map QuantaTen.MN) (by simpa using hr)
    have hx := he.1
    have hx2 := 𝓜.quantaTen_map_MN_bound_N_of_noExotics he
    rw [show (Multiset.map QuantaTen.N 𝓜.quantaTen) = (𝓜.quantaTen.map QuantaTen.MN).map Prod.snd
      by rw [Multiset.map_map]; rfl] at hx
    rw [hS] at hx hx2 ⊢
    simp at hx hx2
    have hl (m : ℤ) (hm : -1 ≤ m) (hm1 : m ≤ 1) : m ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hn := hl n1 hx2.1.1 hx2.1.2
    have hn2 := hl n2 hx2.2.1.1 hx2.2.1.2
    have hn3 := hl n3 hx2.2.2.1 hx2.2.2.2
    clear hr hS
    clear h3 he hS hl
    revert hx hx2
    revert n1
    revert n2
    revert n3
    decide
  · /- The case of Chirality flux equal to `{1, 2}`. -/
    have hS (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {1, 2}) :
        ∃ n1 n2, S = {(1, n1), (2, n2)} := by
      simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
        Prod.exists, exists_and_right, exists_eq_right] at hprod
      obtain ⟨_, n1, h1, rfl, hi⟩ := hprod
      obtain ⟨n2, hi⟩ := hi
      rw [← (Multiset.cons_erase h1), hi]
      use n1, n2
      simp
    obtain ⟨n1, n2, hS⟩ := hS (𝓜.quantaTen.map QuantaTen.MN) (by simpa using hr)
    have hx := he.1
    have hx2 := 𝓜.quantaTen_map_MN_bound_N_of_noExotics he
    rw [show (Multiset.map QuantaTen.N 𝓜.quantaTen) = (𝓜.quantaTen.map QuantaTen.MN).map Prod.snd
      by rw [Multiset.map_map]; rfl] at hx
    rw [hS] at hx hx2 ⊢
    simp at hx hx2
    clear hr hS
    clear h3 he hS
    have hl (m : ℤ) (hm : -1 ≤ m) (hm1 : m ≤ 1) : m ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hl2 (m : ℤ) (hm : -2 ≤ m) (hm1 : m ≤ 2) : m ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hn := hl n1 hx2.1.1 hx2.1.2
    have hn2 := hl2 n2 hx2.2.1 hx2.2.2
    revert hx hx2
    revert n1
    revert n2
    decide
  · /- The case of Chirality flux equal to `{3}`. -/
    have hS (S : Multiset (ℤ × ℤ)) (hprod : S.map Prod.fst = {3}) :
        ∃ n1, S = {(3, n1)} := by
      simp only [Multiset.insert_eq_cons, ← Multiset.map_eq_cons, Multiset.map_eq_singleton,
        Prod.exists, exists_and_right, exists_eq_right] at hprod
      obtain ⟨n1, h1, rfl, hi⟩ := hprod
      use n1
    obtain ⟨n1, hS⟩ := hS (𝓜.quantaTen.map QuantaTen.MN) (by simpa using hr)
    have hx := he.1
    have hx2 := 𝓜.quantaTen_map_MN_bound_N_of_noExotics he
    rw [show (Multiset.map QuantaTen.N 𝓜.quantaTen) = (𝓜.quantaTen.map QuantaTen.MN).map Prod.snd
      by rw [Multiset.map_map]; rfl] at hx
    rw [hS] at hx hx2 ⊢
    simp at hx hx2
    clear hr hS
    clear h3 he hS
    have hl (m : ℤ) (hm : -3 ≤ m) (hm1 : m ≤ 3) : m ∈ ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ) := by
      simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hn := hl n1 hx2.1 hx2.2
    revert hx hx2
    revert n1
    decide

end MatterContent

end SU5U1

end FTheory
