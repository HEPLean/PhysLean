/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Basic
/-!

# Chirality flux and no exotics

The condition on the matter content for there to be no exotics in the spectrum
leads to constraints on the chirality fluxes of the matter content.

This file contains these constraints for the 5-bar and
10d matter representations.

The constraints present in this file are done without explicit consideration
of the `HyperChargeFlux`.

## Important results

- `quantaBarFiveMatter_chiralityFlux_mem` - Specifies the multisets of `ChiralityFlux`
  carried by the 5-bar matter representations potentially allowed by the no exotics conditions.
- `quantaTen_chiralityFlux_mem` - Specifies the allowed multisets of `ChiralityFlux`
  carried by the 10d matter representations potentially allowed by the no exotics conditions.

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

/-!

## 5bar matter

-/

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

/-- Without explicit consideration of `HyperChargeFlux`, the condition of no exotics in the
  matter spectrum constrains the allowed value of the `ChiralityFlux` carried by the 5-bar
  representations to be one of the following Multisets:
- `{1, 1, 1, 0, 0}`, `{1, 1, 1, 0}`, `{1, 1, 1}`
- `{1, 2, 0, 0, 0}`, `{1, 2, 0, 0}`, `{1, 2, 0}`, `{1, 2}`
- `{3, 0, 0, 0}`, `{3, 0, 0}`, `{3, 0}`, `{3}`
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

## 10d matter

-/

/-- The chirality flux associated with a 10d representation must be non-negative. -/
lemma quantaTen_chiralityFlux_nonneg' {a : QuantaTen}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaTen) : 0 ≤ a.M := by
  exact h3.2.2.2 a h

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaTen_chiralityFlux_nonneg {a : ChiralityFlux}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ (𝓜.quantaTen).map QuantaTen.M) : 0 ≤ a := by
  simp only [Multiset.mem_map] at h
  obtain ⟨a', h', rfl⟩ := h
  exact h3.2.2.2 a' h'

/-- Due to the condition of having no exotics in the spectrum, the chirality flux of a
  10d representation must be non-zero.
  This also uses the condition that the hypercharge flux and the chirality flux cannot both
  be zero. -/
lemma quantaTen_chiralityFlux_ne_zero {a : ChiralityFlux}
    (he : 𝓜.NoExotics) (h : a ∈ (𝓜.quantaTen).map QuantaTen.M) : ¬ a = 0 := by
  rw [Multiset.mem_map] at h
  obtain ⟨a', h', rfl⟩ := h
  have h1 := he.2.2.1 a' h'
  have h2 := 𝓜.chirality_charge_not_both_zero_ten a' h'
  rcases a' with ⟨m, n, q⟩
  simp_all [QuantaTen.N, QuantaTen.M]
  by_contra hn
  subst hn
  simp_all only [neg_zero, forall_const]
  have h0 (n : ℤ) (hn : 0 ≤ n ∧ n ≤ 0) (hn : ¬ n = 0) : False := by omega
  exact h0 n h1 h2

/-- The chirality flux associated with a 5-bar representation must be non-negative. -/
lemma quantaTen_chiralityFlux_pos {a : ChiralityFlux} (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ (𝓜.quantaTen).map QuantaTen.M) : 0 < a := by
  have h1 := quantaTen_chiralityFlux_nonneg h3 h
  have h2 := quantaTen_chiralityFlux_ne_zero he h
  simp_all only [ChiralityFlux]
  omega

lemma quantaTen_chiralityFlux_filter_ne_zero_eq_self (he : 𝓜.NoExotics) :
    (𝓜.quantaTen.map (QuantaTen.M)).filter (fun x => ¬ x = 0) =
    𝓜.quantaTen.map (QuantaTen.M) := by
  refine Multiset.filter_eq_self.mpr ?_
  intro a ha
  exact quantaTen_chiralityFlux_ne_zero he ha

/-- The chirality flux associated with a 10d representation must be
  less then or equal to three. -/
lemma quantaTen_chiralityFlux_le_three {a : QuantaTen}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaTen) : a.M ≤ 3 := by
  rw [← h3.2.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map] at ha
    obtain ⟨a', h1, rfl⟩ := ha
    exact quantaTen_chiralityFlux_nonneg' h3 h1
  · simp only [Multiset.mem_map]
    use a

lemma quantaTen_chiralityFlux_card_le_three (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    (𝓜.quantaTen.map (QuantaTen.M)).card ≤ 3 := by
  have h1 := h3.2.1
  have hl : (𝓜.quantaTen.map (QuantaTen.M)).card • 1 ≤ (𝓜.quantaTen.map (QuantaTen.M)).sum := by
    apply Multiset.card_nsmul_le_sum
    intro x hx
    have hx' := quantaTen_chiralityFlux_pos he h3 hx
    simp_all only [ChiralityFlux]
    omega
  simp only [nsmul_eq_mul, mul_one] at hl
  simp_all [ChiralityFlux]

lemma quantaTen_chiralityFlux_card_mem (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    ((𝓜.quantaTen.map (QuantaTen.M))).card ∈
    ({1, 2, 3} : Finset ℕ) := by
  have hn {n : ℕ} (hn : n ≤ 3) (hn : n ≠ 0) : n ∈ ({1, 2, 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine hn (quantaTen_chiralityFlux_card_le_three he h3) ?_
  by_contra hn
  have hl := h3.2
  simp at hn
  rw [hn] at hl
  simp at hl

/-- The number of 10d representations is less than or equal to three. -/
lemma quantaTen_card_le_three (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) : 𝓜.quantaTen.card ≤ 3 := by
  simpa using quantaTen_chiralityFlux_card_le_three he h3

lemma Q10_mem_powerset_filter_card_three (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) : 𝓜.Q10.toFinset ∈
    I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3) := by
  rw [Finset.mem_filter]
  apply And.intro
  · exact 𝓜.Q10_mem_powerset
  · apply le_of_eq_of_le _ (𝓜.quantaTen_card_le_three he h3)
    trans 𝓜.Q10.card
    · conv_rhs => rw [𝓜.Q10_eq_toFinset]
      simp only [Multiset.toFinset_val]
      rfl
    · rw [Multiset.card_map]

/-- Without consideration of `HyperChargeFlux`, the condition of no exotics in the matter spectrum
  constrains the allowed value of the `ChiralityFlux` carried by the 10d representations to be one
  of the following Multisets:

  `{1, 1, 1}`, `{1, 2}`, `{3}`
-/
lemma quantaTen_chiralityFlux_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map QuantaTen.M
    ∈ ({{1, 1, 1}, {1, 2}, {3}} : Finset (Multiset ChiralityFlux)) := by
  have hr := quantaTen_chiralityFlux_card_mem he h3
  simp at hr
  rcases hr with hr | hr | hr
  · rw [Multiset.card_eq_one] at hr
    obtain ⟨a, ha⟩ := hr
    have hl := h3.2
    rw [ha] at hl
    simp at hl
    rw [ha]
    simpa using hl.1
  · rw [Multiset.card_eq_two] at hr
    obtain ⟨a, b, ha⟩ := hr
    have hl := h3.2
    rw [ha] at hl ⊢
    simp at hl
    have a_mem_filter : a ∈ 𝓜.quantaTen := by simp [ha]
    have b_mem_filter : b ∈ 𝓜.quantaTen := by simp [ha]
    have a_pos : 0 < a.M := quantaTen_chiralityFlux_pos he h3 (by rw [Multiset.mem_map]; use a)
    have b_pos : 0 < b.M := quantaTen_chiralityFlux_pos he h3 (by rw [Multiset.mem_map]; use b)
    have hab (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 3) :
        (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by omega
    rcases hab a.M b.M a_pos b_pos hl.1 with hr | hr
    · conv_rhs => rw [Multiset.pair_comm]
      simp [hr]
    · simp [hr]
  · rw [Multiset.card_eq_three] at hr
    obtain ⟨a, b, c, ha⟩ := hr
    have hl := h3.2
    rw [ha] at hl
    simp [← add_assoc] at hl
    rw [ha]
    have a_mem_filter : a ∈ 𝓜.quantaTen := by simp [ha]
    have b_mem_filter : b ∈ 𝓜.quantaTen := by simp [ha]
    have c_mem_filter : c ∈ 𝓜.quantaTen := by simp [ha]
    have a_pos : 0 < a.M := quantaTen_chiralityFlux_pos he h3 (by rw [Multiset.mem_map]; use a)
    have b_pos : 0 < b.M := quantaTen_chiralityFlux_pos he h3 (by rw [Multiset.mem_map]; use b)
    have c_pos : 0 < c.M := quantaTen_chiralityFlux_pos he h3 (by rw [Multiset.mem_map]; use c)
    have habc (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :
        (a = 1 ∧ b = 1 ∧ c = 1) := by omega
    rcases habc a.M b.M c.M a_pos b_pos c_pos hl.1 with hr
    simp [hr]

end MatterContent

end SU5U1

end FTheory
