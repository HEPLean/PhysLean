/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Chirality flux constraints

In this module we use the conditions on
the matter content of the SU(5) GUT model in F-theory
with an additional U(1) symmetry corresponding to having a valid spectrum
to constrain the chirality flux of the matter content.

The two conditions used are `ThreeChiralFamiles` and `NoExotics`.

## Important results

- `quantaTen_card_le_three` given these constraints, there are at most
  three 10d representations.

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

/-!

## The 5-bar representations.

-/

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

/-!

## The 10d representations.

-/

/-- The chirality flux associated with a 10d representation must be non-negative. -/
lemma quantaTen_chiralityFlux_nonneg' {a : QuantaTen I}
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
lemma quantaTen_chiralityFlux_le_three {a : QuantaTen I}
    (h3 : 𝓜.ThreeChiralFamiles) (h : a ∈ 𝓜.quantaTen) : a.M ≤ 3 := by
  rw [← h3.2.1]
  refine Multiset.single_le_sum (α := ChiralityFlux) ?_ _ ?_
  · intro a ha
    simp only [Multiset.mem_map, Prod.exists, Subtype.exists] at ha
    obtain ⟨a', h1, rfl⟩ := ha
    exact quantaTen_chiralityFlux_nonneg' h3 h1
  · simp only [Multiset.mem_map, Prod.exists, Subtype.exists]
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

/-- The multiset of chirality fluxes of matter content in the 10d representation
  satisfying `NoExotics` and
  `ThreeChiralFamiles` must either be
- `{1, 1, 1}`
- `{1, 2}`
- `{3}`
-/
lemma quantaTen_chiralityFlux_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map (QuantaTen.M)
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
    have a_pos : 0 < a.M := quantaTen_chiralityFlux_pos he h3 (by simp; use a)
    have b_pos : 0 < b.M := quantaTen_chiralityFlux_pos he h3 (by simp; use b)
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
    have a_pos : 0 < a.M := quantaTen_chiralityFlux_pos he h3 (by simp; use a)
    have b_pos : 0 < b.M := quantaTen_chiralityFlux_pos he h3 (by simp; use b)
    have c_pos : 0 < c.M := quantaTen_chiralityFlux_pos he h3 (by simp; use c)
    have habc (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :
        (a = 1 ∧ b = 1 ∧ c = 1) := by omega
    rcases habc a.M b.M c.M a_pos b_pos c_pos hl.1 with hr
    simp [hr]

end MatterContent

end SU5U1

end FTheory
