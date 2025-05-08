/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Basic
/-!

# No exotics for 5-bar representations

In this module we give lemmas on the 5-bar matter content arising
from the conditions of a valid spectrum.

## Important results

- `quantaBarFive_card_le_eight` :
  The number of 5-bar representations is less than or equal to eight.
- `quantaBarFive_chiralityFlux_mem` :
  Constrains the chirality fluxes of the 5-bar representations to be one
  of a finite set of possibilities.

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaBarFiveMatter_chiralityFlux_nonneg' {a : QuantaBarFive}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFiveMatter) : 0 ≤ a.M := by
  exact h3.2.2.1 a (by simp [quantaBarFive]; right; right; exact h)

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaBarFiveMatter_chiralityFlux_nonneg {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles)
    (h : a ∈ (𝓜.quantaBarFiveMatter).map QuantaBarFive.M) : 0 ≤ a := by
  simp only [Multiset.mem_map] at h
  obtain ⟨a', h', rfl⟩ := h
  refine h3.2.2.1 a' ?_
  simp [quantaBarFive]
  right
  right
  exact h'

/-- The chirality flux associated with a 5-bar representation must be
  less then or equal to three. -/
lemma quantaBarFiveMatter_chiralityFlux_le_three {a : QuantaBarFive}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFiveMatter) : a.M ≤ 3 := by
  rw [← h3.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map, Prod.exists, Subtype.exists] at ha
    obtain ⟨a', b, c, h, rfl⟩ := ha
    rw [quantaBarFive] at h
    simp at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | h
    · simp
    · simp
    · refine quantaBarFiveMatter_chiralityFlux_nonneg' h3 h
  · simp only [Multiset.mem_map, Prod.exists, Subtype.exists]
    use a.1, a.2.1, a.2.2
    simp [quantaBarFive]
    right
    right
    exact h

lemma quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum = 3 := by
  have h2 : ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum = 0 := by
    rw [Multiset.sum_eq_zero]
    intro x hx
    rw [Multiset.mem_filter] at hx
    exact hx.2
  trans ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum +
      ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum
  · rw [h2]
    simp
  rw [Multiset.sum_filter_add_sum_filter_not]
  simpa [quantaBarFive, QuantaBarFive.M] using h3.1

/-- The number of 5-bar matter representations with non-zero chirality
  flux is less than or equal to three. -/
lemma quantaBarFiveMatter_chiralityFlux_filter_non_zero_card_le_three (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card ≤ 3 := by
  have h1 := quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum h3
  have hl : ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card • 1 ≤
      ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    rw [Multiset.mem_filter] at hx
    have hx' := quantaBarFiveMatter_chiralityFlux_nonneg h3 hx.1
    have hx'' := hx.2
    simp_all only [ChiralityFlux]
    omega
  simp only [nsmul_eq_mul, mul_one] at hl
  simp_all only [ChiralityFlux]
  omega

lemma pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles)
    (h : a ∈ ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0))) :
    0 < a := by
  rw [Multiset.mem_filter] at h
  have h' := quantaBarFiveMatter_chiralityFlux_nonneg h3 h.1
  have h'' := h.2
  simp_all only [ChiralityFlux]
  omega

lemma quantaBarFiveMatter_chiralityFlux_filter_non_zero_card_mem (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card ∈
    ({1, 2, 3} : Finset ℕ) := by
  have hn {n : ℕ} (hn : n ≤ 3) (hn : n ≠ 0) : n ∈ ({1, 2, 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine hn (quantaBarFiveMatter_chiralityFlux_filter_non_zero_card_le_three h3) ?_
  by_contra hn
  have hl := quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum h3
  simp at hn
  rw [hn] at hl
  simp at hl

/-- The multiset of non-zero chirality fluxes of matter content in the 5-bar
  representation satisfying
  `ThreeChiralFamiles` must either be
- `{1, 1, 1}`
- `{1, 2}`
- `{3}`
-/
lemma quantaBarFiveMatter_chiralityFlux_filter_non_zero_mem (h3 : 𝓜.ThreeChiralFamiles) :
    (𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)
    ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ChiralityFlux)) := by
  have hr := quantaBarFiveMatter_chiralityFlux_filter_non_zero_card_mem h3
  simp at hr
  rcases hr with hr | hr | hr
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨a, ha⟩ := hr
    have hl := quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl
    simp at hl
    rw [ha, hl]
    simp
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨a, b, ha⟩ := hr
    have hl := quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl ⊢
    simp at hl
    have a_mem_filter : a ∈
        (𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have b_mem_filter : b ∈
        (𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have a_pos : 0 < a :=
      pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero h3 a_mem_filter
    have b_pos : 0 < b :=
      pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero h3 b_mem_filter
    have hab (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 3) :
        (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by omega
    rcases hab a b a_pos b_pos hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · conv_rhs => rw [Multiset.pair_comm]
      simp
    · simp
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨a, b, c, ha⟩ := hr
    have hl := quantaBarFiveMatter_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl
    simp [← add_assoc] at hl
    rw [ha]
    have a_mem_filter : a ∈ (𝓜.quantaBarFiveMatter.map
        (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have b_mem_filter : b ∈ (𝓜.quantaBarFiveMatter.map
        (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have c_mem_filter : c ∈ (𝓜.quantaBarFiveMatter.map
        (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have a_pos : 0 < a :=
      pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero h3 a_mem_filter
    have b_pos : 0 < b :=
      pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero h3 b_mem_filter
    have c_pos : 0 < c :=
      pos_of_mem_quantaBarFiveMatter_chiralityFlux_filter_non_zero h3 c_mem_filter
    have habc (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :
        (a = 1 ∧ b = 1 ∧ c = 1) := by omega
    rcases habc a b c a_pos b_pos c_pos hl with ⟨rfl, rfl, rfl⟩
    simp

lemma quantaBarFiveMatter_zero_chiralityFlux_abs_sum_le_three (h3L : 𝓜.ThreeLeptonDoublets) :
    (Multiset.map (fun a => |a.M + a.N|)
      (𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0))).sum ≤ 3 := by
  simp [ThreeLeptonDoublets, quantaBarFive, QuantaBarFive.M, QuantaBarFive.N] at h3L
  have h3L : (Multiset.map (fun x => |x.1 + x.2.1|) 𝓜.quantaBarFiveMatter).sum = 3 := by linarith
  have h1 : (Multiset.map (fun a => |a.M + a.N|) 𝓜.quantaBarFiveMatter).sum
      = (Multiset.map (fun a => |a.M + a.N|) (𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0))).sum
      + (Multiset.map (fun a => |a.M + a.N|)
      (𝓜.quantaBarFiveMatter.filter (fun x => ¬ x.M = 0))).sum := by
    conv_lhs => rw [Eq.symm (Multiset.filter_add_not (fun x => x.M = 0) 𝓜.quantaBarFiveMatter)]
    rw [Multiset.map_add]
    rw [Multiset.sum_add]
  rw [h1] at h3L
  have hz_pos : 0 ≤
      (Multiset.map (fun a => |a.M + a.N|)
        (𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0))).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    simp at hx
    obtain ⟨a, b, hc, d, ha, rfl⟩ := hx
    exact abs_nonneg _
  have hz_non_zero_pos : 0 ≤ (Multiset.map (fun a => |a.M + a.N|)
      (𝓜.quantaBarFiveMatter.filter (fun x => ¬ x.M = 0))).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    simp at hx
    obtain ⟨a, b, hc, d, ha, rfl⟩ := hx
    exact abs_nonneg _
  have hab {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a + b = 3) : a ≤ 3 := by omega
  exact hab hz_pos hz_non_zero_pos h3L

/-- The number of 5d representations with chirality flux equal to zero is
  less than or equal to five. -/
lemma quantaBarFiveMatter_zero_chiralityFlux_card_le_three (h3L : 𝓜.ThreeLeptonDoublets) :
    ((𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0))).card ≤ 3 := by
  have h1' : ((𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0)).map
      (fun a => |a.M + a.N|)).card • 1 ≤
      ((𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0)).map (fun a => |a.M + a.N|)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    simp only [Multiset.mem_map, Multiset.mem_filter, Prod.exists, Subtype.exists] at hx
    obtain ⟨m, n, q, ha, rfl⟩ := hx
    rw [ha.2]
    have hp := 𝓜.chirality_charge_not_both_zero_bar_five (m, n, q) (by
      simp [quantaBarFive]
      right; right
      exact ha.1)
    simp [ha.2] at hp
    have ha {a : ℤ} (h : ¬ a = 0) : 1 ≤ |a| := by
      exact Int.one_le_abs h
    apply ha
    simpa using hp
  have h1 := 𝓜.quantaBarFiveMatter_zero_chiralityFlux_abs_sum_le_three h3L
  simp_all [HyperChargeFlux, ChiralityFlux]
  exact Int.ofNat_le.mp (le_trans h1' h1)

lemma quantaBarFiveMatter_zero_chiralityFlux_card_mem (h3L : 𝓜.ThreeLeptonDoublets) :
    ((𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => x = 0)).card ∈
    ({0, 1, 2, 3} : Finset ℕ) := by
  have hn {n : ℕ} (hn : n ≤ 3) : n ∈ ({0, 1, 2, 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  apply hn
  simpa [Multiset.filter_map] using 𝓜.quantaBarFiveMatter_zero_chiralityFlux_card_le_three h3L

open Multiset in
lemma quantaBarFiveMatter_zero_chiralityFlux_mem (h3L : 𝓜.ThreeLeptonDoublets) :
    (𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => x = 0) ∈
    ({replicate 3 0, replicate 2 0, replicate 1 0, replicate 0 0} :
      Finset (Multiset ChiralityFlux)) := by
  have h1 := quantaBarFiveMatter_zero_chiralityFlux_card_mem h3L
  have hn (n : ℕ) (hr :
      (filter (fun x => x = 0) (map QuantaBarFive.M 𝓜.quantaBarFiveMatter)).card = n) :
      (𝓜.quantaBarFiveMatter.map (QuantaBarFive.M)).filter (fun x => x = 0) = replicate n 0 := by
    rw [eq_replicate, hr]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with hr | hr | hr | hr
  · rw [hn 0 hr]
    simp
  · rw [hn 1 hr]
    simp
  · rw [hn 2 hr]
    simp
  · rw [hn 3 hr]
    simp

/-- The number of 5-bar matter representations is less than or equal to six.
  Note the existences of `quantaBarFive_card_le_seven`. The proof of this weaker result
  does not rely on the assumptions of no-duplicate charges. -/
lemma quantaBarFiveMatter_card_le_six (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.card ≤ 6 := by
  have h1 : 𝓜.quantaBarFiveMatter.card =
      ((𝓜.quantaBarFiveMatter.filter (fun x => x.M = 0))).card +
      ((𝓜.quantaBarFiveMatter.filter (fun x => ¬ x.M = 0))).card := by
    conv_lhs => rw [Eq.symm (Multiset.filter_add_not (fun x => x.M = 0) 𝓜.quantaBarFiveMatter)]
    exact Multiset.card_add _ _
  rw [h1]
  have h2 : ((𝓜.quantaBarFiveMatter.filter (fun x => ¬ x.M = 0))).card ≤ 3 := by
    simpa [Multiset.filter_map] using
      𝓜.quantaBarFiveMatter_chiralityFlux_filter_non_zero_card_le_three h3
  have h3 := quantaBarFiveMatter_zero_chiralityFlux_card_le_three h3L
  omega

/-- The multiset of chirality fluxes of matter content in the 5 bar representation
  satisfying `ThreeChiralFamiles` and
  `ThreeLeptonDoublets` must either be
- `{1, 1, 1}`
- `{1, 2}`
- `{3}`
with zero to three chirality fluxes equal to zero.
-/
lemma quantaBarFiveMatter_chiralityFlux_mem
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map QuantaBarFive.M ∈
    ({{1, 1, 1, 0, 0}, {1, 1, 1, 0}, {1, 1, 1},
      {1, 2, 0, 0, 0}, {1, 2, 0, 0}, {1, 2, 0}, {1, 2},
      {3, 0, 0, 0}, {3, 0, 0}, {3, 0}, {3}} :
      Finset (Multiset ChiralityFlux)) := by
  have hcard : (𝓜.quantaBarFive.map QuantaBarFive.M).card ≤ 7 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaBarFive_card_le_seven
  have hcard : (𝓜.quantaBarFiveMatter.map QuantaBarFive.M).card ≤ 5 := by
    simp [quantaBarFive] at hcard
    simpa using hcard
  rw [← (Multiset.filter_add_not (fun x => x = 0)
    (Multiset.map QuantaBarFive.M 𝓜.quantaBarFiveMatter))] at hcard ⊢
  have hz := quantaBarFiveMatter_zero_chiralityFlux_mem h3L
  have h0 := quantaBarFiveMatter_chiralityFlux_filter_non_zero_mem h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0
  simp only [Multiset.insert_eq_cons]
  rcases hz with hz | hz | hz | hz
    <;> rcases h0 with h0 | h0 | h0
  all_goals
    rw [hz, h0]
    repeat rw [Multiset.replicate_succ]
    try rw [Multiset.replicate_zero]
    repeat rw [Multiset.insert_eq_cons]
    repeat rw [Multiset.add_cons]
    rw [Multiset.add_comm, Multiset.singleton_add]
    simp only [Multiset.cons_zero, Finset.mem_insert, Finset.mem_singleton,
      Multiset.empty_eq_zero, true_or, or_true]
  -- The case of {1, 1, 1, 0, 0, 0, 0, 0}
  rw [hz, h0] at hcard
  simp at hcard

/-- The number of 5-bar representations (including the Higges) is greater then or equal to three. -/
lemma quantaBarFiveMatter_one_le_card (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    1 ≤ 𝓜.quantaBarFiveMatter.card := by
  refine le_of_le_of_eq ?_ (Multiset.card_map QuantaBarFive.M 𝓜.quantaBarFiveMatter)
  have hr := 𝓜.quantaBarFiveMatter_chiralityFlux_mem h3 h3L
  generalize (Multiset.map QuantaBarFive.M 𝓜.quantaBarFiveMatter) = x at *
  fin_cases hr
    <;> simp

/-!

## With hypercharge flux

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

-- 22 cases overall.
lemma quantaBarFiveMatter_N_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map QuantaBarFive.N ∈ ({
    -- card 5 (3 cases)
    {-1, -1, -1, 1, 2}, {-1, -1, 0, 1, 1}, {-1, -2, 1, 1, 1},
    -- card 4 (7 cases)
    {-3, 1, 1, 1}, {-2, -1, 1, 2},
    {-2, 0, 1, 1}, {-1, -1, -1, 3},
    {-1, -1, 0, 2}, {-1, -1, 1, 1}, {0, 0, -1, 1},
    -- card 3 (7 cases)
    -- Corresponding to 6 + 6 + 6 + 3 + 3 + 6 + 1 = 31 ACC conditions.
    {-3, 1, 2}, {-2, -1, 3}, {-2, 0, 2}, {-2, 1, 1},
    {-1, -1, 2}, {-1, 0, 1}, {0, 0, 0},
    -- card 2 (4 cases)
    -- Corresponding to 2 + 2 + 2 + 1 = 7 ACC conditions.
    {-3, 3}, {-2, 2}, {-1, 1}, {0, 0},
    -- card 1 (1 case)
    -- Corresponding to 1 ACC condition.
    {0}} : Finset (Multiset ℤ)) := by
  have hr := quantaBarFiveMatter_MN_mem he h3 h3L
  have hn : 𝓜.quantaBarFiveMatter.map QuantaBarFive.N =
    (Multiset.map QuantaBarFive.MN 𝓜.quantaBarFiveMatter).map Prod.snd := by
    simp
  rw [hn]
  generalize (Multiset.map QuantaBarFive.MN 𝓜.quantaBarFiveMatter) = S at *
  clear hn
  revert S
  decide

end MatterContent

end SU5U1

end FTheory
