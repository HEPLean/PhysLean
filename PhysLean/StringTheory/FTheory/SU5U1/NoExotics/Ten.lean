/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Basic
/-!

# No exotics for 10d representations

In this module we give lemmas on the 10d matter content arising
from the conditions of a valid spectrum.

## Important results

- `quantaTen_card_le_three` :
  The number of 10d representations is less than or equal to three.
- `quantaTen_chiralityFlux_mem` :
  The multiset of chirality fluxes of matter content in the 10d representation
  satisfying `ThreeChiralFamiles` and `ThreeLeptonDoublets` must either be
  `{1, 1, 1}`, `{1, 2}`, or `{3}`.

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}

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

lemma quantaTen_map_q_powerset_filter_card_three (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    (𝓜.quantaTen.map QuantaTen.q).toFinset ∈
    I.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3) := by
  rw [Finset.mem_filter]
  apply And.intro
  · exact 𝓜.quantaTen_map_q_mem_powerset
  · apply le_of_eq_of_le _ (𝓜.quantaTen_card_le_three he h3)
    trans (𝓜.quantaTen.map QuantaTen.q).card
    · conv_rhs => rw [𝓜.quantaTen_map_q_eq_toFinset]
      simp only [Multiset.toFinset_val]
      rfl
    · rw [Multiset.card_map]

/-- The multiset of chirality fluxes of matter content in the 10d representation
  satisfying `NoExotics` and
  `ThreeChiralFamiles` must either be
- `{1, 1, 1}`
- `{1, 2}`
- `{3}`
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

-- 5 cases overall.
lemma quantaTen_N_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map QuantaTen.N ∈ ({
    {0, 0, 0}, {1, -1, 0}, {0, 0}, {-1, 1}, {0}} : Finset (Multiset ℤ)) := by
  have hr := quantaTen_MN_mem he h3
  have hn : 𝓜.quantaTen.map QuantaTen.N =
    (Multiset.map QuantaTen.MN 𝓜.quantaTen).map Prod.snd := by
    simp
  rw [hn]
  generalize (Multiset.map QuantaTen.MN 𝓜.quantaTen) = S at *
  clear hn
  revert S
  decide

end MatterContent

end SU5U1

end FTheory
