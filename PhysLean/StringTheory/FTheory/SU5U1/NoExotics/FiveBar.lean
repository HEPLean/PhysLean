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
lemma quantaBarFive_chiralityFlux_nonneg' {a : QuantaBarFive I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFive) : 0 ≤ a.M := by
  exact h3.2.2.1 a h

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaBarFive_chiralityFlux_nonneg {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ (𝓜.quantaBarFive).map QuantaBarFive.M) : 0 ≤ a := by
  simp only [Multiset.mem_map] at h
  obtain ⟨a', h', rfl⟩ := h
  exact h3.2.2.1 a' h'

/-- The chirality flux associated with a 5-bar representation must be
  less then or equal to three. -/
lemma quantaBarFive_chiralityFlux_le_three {a : QuantaBarFive I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaBarFive) : a.M ≤ 3 := by
  rw [← h3.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map, Prod.exists, Subtype.exists] at ha
    obtain ⟨a', b, c, d, h, h2, rfl⟩ := ha
    exact quantaBarFive_chiralityFlux_nonneg' h3 h
  · simp only [Multiset.mem_map, Prod.exists, Subtype.exists]
    use a.1, a.2.1, a.2.2, a.2.2.2

lemma quantaBarFive_chiralityFlux_filter_non_zero_sum (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum = 3 := by
  have h2 : ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum = 0 := by
    rw [Multiset.sum_eq_zero]
    intro x hx
    rw [Multiset.mem_filter] at hx
    exact hx.2
  trans ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).sum +
      ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum
  · rw [h2]
    simp
  rw [Multiset.sum_filter_add_sum_filter_not]
  exact h3.1

/-- The number of 5-bar representations with non-zero chirality
  flux is less than or equal to three. -/
lemma quantaBarFive_chiralityFlux_filter_non_zero_card_le_three (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card ≤ 3 := by
  have h1 := quantaBarFive_chiralityFlux_filter_non_zero_sum h3
  have hl : ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card • 1 ≤
      ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    rw [Multiset.mem_filter] at hx
    have hx' := quantaBarFive_chiralityFlux_nonneg h3 hx.1
    have hx'' := hx.2
    simp_all only [ChiralityFlux]
    omega
  simp only [nsmul_eq_mul, mul_one] at hl
  simp_all only [ChiralityFlux]
  omega

lemma pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles)
    (h : a ∈ ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0))) :
    0 < a := by
  rw [Multiset.mem_filter] at h
  have h' := quantaBarFive_chiralityFlux_nonneg h3 h.1
  have h'' := h.2
  simp_all only [ChiralityFlux]
  omega

lemma quantaBarFive_chiralityFlux_filter_non_zero_card_mem (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)).card ∈
    ({1, 2, 3} : Finset ℕ) := by
  have hn {n : ℕ} (hn : n ≤ 3) (hn : n ≠ 0) : n ∈ ({1, 2, 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine hn (quantaBarFive_chiralityFlux_filter_non_zero_card_le_three h3) ?_
  by_contra hn
  have hl := quantaBarFive_chiralityFlux_filter_non_zero_sum h3
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
lemma quantaBarFive_chiralityFlux_filter_non_zero_mem (h3 : 𝓜.ThreeChiralFamiles) :
    (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0)
    ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ChiralityFlux)) := by
  have hr := quantaBarFive_chiralityFlux_filter_non_zero_card_mem h3
  simp at hr
  rcases hr with hr | hr | hr
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨a, ha⟩ := hr
    have hl := quantaBarFive_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl
    simp at hl
    rw [ha, hl]
    simp
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨a, b, ha⟩ := hr
    have hl := quantaBarFive_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl ⊢
    simp at hl
    have a_mem_filter : a ∈ (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have b_mem_filter : b ∈ (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have a_pos : 0 < a := pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero h3 a_mem_filter
    have b_pos : 0 < b := pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero h3 b_mem_filter
    have hab (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 3) :
        (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by omega
    rcases hab a b a_pos b_pos hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · conv_rhs => rw [Multiset.pair_comm]
      simp
    · simp
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨a, b, c, ha⟩ := hr
    have hl := quantaBarFive_chiralityFlux_filter_non_zero_sum h3
    rw [ha] at hl
    simp [← add_assoc] at hl
    rw [ha]
    have a_mem_filter : a ∈ (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have b_mem_filter : b ∈ (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have c_mem_filter : c ∈ (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => ¬ x = 0) := by
      simp [ha]
    have a_pos : 0 < a := pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero h3 a_mem_filter
    have b_pos : 0 < b := pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero h3 b_mem_filter
    have c_pos : 0 < c := pos_of_mem_quantaBarFive_chiralityFlux_filter_non_zero h3 c_mem_filter
    have habc (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :
        (a = 1 ∧ b = 1 ∧ c = 1) := by omega
    rcases habc a b c a_pos b_pos c_pos hl with ⟨rfl, rfl, rfl⟩
    simp

lemma quantaBarFive_zero_chiralityFlux_abs_sum_le_five (h3L : 𝓜.ThreeLeptonDoublets) :
    (Multiset.map (fun a => |a.M + a.N|) (𝓜.quantaBarFive.filter (fun x => x.M = 0))).sum ≤ 5 := by
  simp [ThreeLeptonDoublets] at h3L
  have h1 : (Multiset.map (fun a => |a.M + a.N|) 𝓜.quantaBarFive).sum
      = (Multiset.map (fun a => |a.M + a.N|) (𝓜.quantaBarFive.filter (fun x => x.M = 0))).sum
      + (Multiset.map (fun a => |a.M + a.N|)
      (𝓜.quantaBarFive.filter (fun x => ¬ x.M = 0))).sum := by
    conv_lhs => rw [Eq.symm (Multiset.filter_add_not (fun x => x.M = 0) 𝓜.quantaBarFive)]
    rw [Multiset.map_add]
    rw [Multiset.sum_add]
  rw [h1] at h3L
  have hz_pos : 0 ≤
      (Multiset.map (fun a => |a.M + a.N|) (𝓜.quantaBarFive.filter (fun x => x.M = 0))).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    simp at hx
    obtain ⟨a, b, hc, d, ha, rfl⟩ := hx
    exact abs_nonneg _
  have hz_non_zero_pos : 0 ≤
      (Multiset.map (fun a => |a.M + a.N|) (𝓜.quantaBarFive.filter (fun x => ¬ x.M = 0))).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    simp at hx
    obtain ⟨a, b, hc, d, ha, rfl⟩ := hx
    exact abs_nonneg _
  have hab {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a + b = 5) : a ≤ 5 := by omega
  exact hab hz_pos hz_non_zero_pos h3L

/-- The number of 5d representations with chirality flux equal to zero is
  less than or equal to five. -/
lemma quantaBarFive_zero_chiralityFlux_card_le_five (h3L : 𝓜.ThreeLeptonDoublets) :
    ((𝓜.quantaBarFive.filter (fun x => x.M = 0))).card ≤ 5 := by
  have h1' : ((𝓜.quantaBarFive.filter (fun x => x.M = 0)).map (fun a => |a.M + a.N|)).card • 1 ≤
      ((𝓜.quantaBarFive.filter (fun x => x.M = 0)).map (fun a => |a.M + a.N|)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    simp only [Multiset.mem_map, Multiset.mem_filter, Prod.exists, Subtype.exists] at hx
    obtain ⟨m, n, q, hq, ha, rfl⟩ := hx
    rw [ha.2]
    have hp := 𝓜.chirality_charge_not_both_zero_bar_five (m, n, ⟨q, hq⟩) ha.1
    simp [ha.2] at hp
    have ha {a : ℤ} (h : ¬ a = 0) : 1 ≤ |a| := by
      exact Int.one_le_abs h
    apply ha
    simpa using hp
  have h1 := 𝓜.quantaBarFive_zero_chiralityFlux_abs_sum_le_five h3L
  simp_all [HyperChargeFlux, ChiralityFlux]
  exact Int.ofNat_le.mp (le_trans h1' h1)

lemma quantaBarFive_zero_chiralityFlux_card_mem (h3L : 𝓜.ThreeLeptonDoublets) :
    ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).card ∈
    ({0, 1, 2, 3, 4, 5} : Finset ℕ) := by
  have hn {n : ℕ} (hn : n ≤ 5) : n ∈ ({0, 1, 2, 3, 4, 5} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  apply hn
  simpa [Multiset.filter_map] using 𝓜.quantaBarFive_zero_chiralityFlux_card_le_five h3L

open Multiset in
lemma quantaBarFive_zero_chiralityFlux_mem (h3L : 𝓜.ThreeLeptonDoublets) :
    (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0) ∈
    ({replicate 5 0, replicate 4 0, replicate 3 0, replicate 2 0} :
      Finset (Multiset ChiralityFlux)) := by
  have h1 := quantaBarFive_zero_chiralityFlux_card_mem h3L
  have hn (n : ℕ) (hr : (filter (fun x => x = 0) (map QuantaBarFive.M 𝓜.quantaBarFive)).card = n) :
      (𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0) = replicate n 0 := by
    rw [eq_replicate, hr]
    simp
  simp only [Finset.mem_insert, Multiset.card_eq_zero, Finset.mem_singleton] at h1
  have hcard := 𝓜.quantaBarFive_chiralityFlux_two_le_filter_zero_card
  rcases h1 with hr | hr | hr | hr | hr | hr
  · rw [hr] at hcard
    simp at hcard
  · rw [hn 1 hr] at hcard
    simp at hcard
  · rw [hn 2 hr]
    simp
  · rw [hn 3 hr]
    simp
  · rw [hn 4 hr]
    simp
  · rw [hn 5 hr]
    simp

/-- The number of 5-bar representations is less than or equal to eight.
  Note the existences of `quantaBarFive_card_le_seven`. The proof of this weaker result
  does not rely on the assumptions of no-duplicate charges. -/
lemma quantaBarFive_card_le_eight (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFive.card ≤ 8 := by
  have h1 : 𝓜.quantaBarFive.card =
      ((𝓜.quantaBarFive.filter (fun x => x.M = 0))).card +
      ((𝓜.quantaBarFive.filter (fun x => ¬ x.M = 0))).card := by
    conv_lhs => rw [Eq.symm (Multiset.filter_add_not (fun x => x.M = 0) 𝓜.quantaBarFive)]
    exact Multiset.card_add _ _
  rw [h1]
  have h2 : ((𝓜.quantaBarFive.filter (fun x => ¬ x.M = 0))).card ≤ 3 := by
    simpa [Multiset.filter_map] using
      𝓜.quantaBarFive_chiralityFlux_filter_non_zero_card_le_three h3
  have h3 := quantaBarFive_zero_chiralityFlux_card_le_five h3L
  omega

/-- The multiset of chirality fluxes of matter content in the 5 bar representation
  satisfying `ThreeChiralFamiles` and
  `ThreeLeptonDoublets` must either be
- `{1, 1, 1}`
- `{1, 2}`
- `{3}`
with zero to five chirality fluxes equal to zero.
-/
lemma quantaBarFive_chiralityFlux_mem (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFive.map QuantaBarFive.M ∈
    ({{1, 1, 1, 0, 0, 0, 0}, {1, 1, 1, 0, 0, 0}, {1, 1, 1, 0, 0},
      {1, 2, 0, 0, 0, 0, 0}, {1, 2, 0, 0, 0, 0}, {1, 2, 0, 0, 0}, {1, 2, 0, 0},
      {3, 0, 0, 0, 0, 0}, {3, 0, 0, 0, 0}, {3, 0, 0, 0}, {3, 0, 0}} :
      Finset (Multiset ChiralityFlux)) := by
  have hcard : (𝓜.quantaBarFive.map QuantaBarFive.M).card ≤ 7 := by
    rw [Multiset.card_map]
    exact 𝓜.quantaBarFive_card_le_seven
  rw [← (Multiset.filter_add_not (fun x => x = 0)
    (Multiset.map QuantaBarFive.M 𝓜.quantaBarFive))] at hcard ⊢
  have hz := quantaBarFive_zero_chiralityFlux_mem h3L
  have h0 := quantaBarFive_chiralityFlux_filter_non_zero_mem h3
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
lemma quantaBarFive_three_le_card (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    3 ≤ 𝓜.quantaBarFive.card := by
  refine le_of_le_of_eq ?_ (Multiset.card_map QuantaBarFive.M 𝓜.quantaBarFive)
  have hr := 𝓜.quantaBarFive_chiralityFlux_mem h3 h3L
  generalize (Multiset.map QuantaBarFive.M 𝓜.quantaBarFive) = x at *
  fin_cases hr
    <;> simp

end MatterContent

end SU5U1

end FTheory
