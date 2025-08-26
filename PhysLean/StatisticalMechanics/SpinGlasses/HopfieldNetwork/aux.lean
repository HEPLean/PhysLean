/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis, Matteo Cipollina
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option checkBinderAnnotations false

variable {U : Type*} [Field R] --[LinearOrder R] [IsStrictOrderedRing R]
open Finset Fintype Matrix

@[simp]
lemma isSymm_sum (f : Fin m → Matrix U U R) (hi : ∀ i, (f i).IsSymm) :
  (∑ x : Fin m, f x).IsSymm := by
  rw [Matrix.IsSymm]
  simp only [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact hi x

--def fair' (sseq : Nat → NN.State) : Prop := ∀ n, ∃ m > n, sseq (m + 1) ≠ sseq m

/--
A sequence `useq` is fair if for every element `u` and every index `n`,
there exists an index `m` greater than or equal to `n` such that `useq m = u`.
--/
def fair (useq : ℕ → U) : Prop := ∀ u n, ∃ m ≥ n, useq m = u

/--
`cyclic useq` is a property that holds if `useq` is a sequence such that:
1. Every element of type `U` appears at least once in the sequence.
2. The sequence is periodic with a period equal to the cardinality of `U`.
--/
def cyclic [Fintype U] (useq : ℕ → U) : Prop :=
  (∀ u : U, ∃ i, useq i = u) ∧ (∀ i j, i % card U = j % card U → useq i = useq j)

@[simp]
lemma Fintype.exists_mod_eq_within_bounds [Fintype U] [Nonempty U] : ∀ i (n : ℕ),
    ∃ m ≥ n, m < n + card U ∧ m % card U = i % (card U) := by  {
  simp only [ge_iff_le]
  intros i n
  let a := (n / card U) + 1
  have : a * card U ≥ n := by {
    simp only [ge_iff_le]
    simp only [a]
    rw [add_mul]
    simp only [one_mul]
    rw [le_iff_lt_or_eq]
    left
    exact Nat.lt_div_mul_add Fintype.card_pos}
  let j := i + a * card U
  have hj : j ≥ n := by {
    simp only [j]
    exact le_add_of_le_right this}
  use (n + (j - n) % card U)
  constructor
  · simp only [ge_iff_le, a, j] at *
    exact Nat.le_add_right n ((i + (n / Fintype.card U + 1) * Fintype.card U - n) % Fintype.card U)
  · constructor
    · simp only [add_lt_add_iff_left]
      exact Nat.mod_lt _ Fintype.card_pos
    · simp only [Nat.add_mod_mod]
      simp_all only [ge_iff_le, add_tsub_cancel_of_le, Nat.add_mul_mod_self_right, a, j]}

@[simp]
lemma cycl_Fair [Fintype U] [Nonempty U] (useq : ℕ → U) : cyclic useq → fair useq :=
  fun ⟨hcov, hper⟩ u n =>
  let ⟨i, hi⟩ := hcov u
  let ⟨m, hm, hkmod⟩ := @Fintype.exists_mod_eq_within_bounds U _ _ i n
  ⟨m, hm, hi ▸ hper m i hkmod.2⟩

@[simp]
lemma Fintype.cyclic_Fair_bound [Fintype U] [Nonempty U] (useq : ℕ → U) :
    cyclic useq → ∀ u (n : ℕ),
      ∃ m ≥ n, m < n + card U ∧ useq m = u := fun ⟨hcov, hper⟩ u n => by {
  obtain ⟨i, hi⟩ := hcov u
  have := @Fintype.exists_mod_eq_within_bounds U _ _ i n
  obtain ⟨m, hm, hle, hkmod⟩ := this
  use m
  constructor
  · exact hm
  · constructor
    · exact hle
    · rw [← hi]
      exact hper m i hkmod}

/-- Split a sum over elements satisfying P into sums over elements satisfying P∧Q and P∧¬Q -/
lemma sum_split (P Q : α → Prop) [DecidablePred P] [AddCommMonoid β]
    [DecidablePred Q] (f : α → β) :
  ∑ u ∈ filter (fun u => P u) s, f u = ∑ u ∈ filter (fun u => P u ∧ Q u) s, f u  +
      ∑ u ∈ filter (fun u => P u ∧ ¬ Q u) s, f u := by
  simp only [sum_filter, ← sum_add_distrib, ite_and, ite_add, ite_not, zero_add, add_zero, zero_add]
  simp_all only [↓reduceIte, add_zero, ite_self]

lemma sum_over_subset (f : α → β) (s : Finset α) [Fintype α] [AddCommMonoid β]
  [DecidablePred (fun x => x ∈ s)] :
  ∑ x ∈ s, f x = ∑ x, if x ∈ s then f x else 0 := by
  simp_rw [← sum_filter]; congr;
  ext; simp only [mem_filter, mem_univ, true_and]

/-- Convert telescope sum to filtered sum --/
@[simp]
lemma tsum_to_filter {α : Type} [Fintype α] {p : α → ENNReal} {y : β} (f : α → β) :
  ∑' (a : α), p a = ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
  rw [tsum_fintype]
  exact Eq.symm (sum_filter (fun a ↦ f a = y) p)

/-- If filtered sum is positive, there exists a positive element satisfying filter condition --/
@[simp]
lemma filter_sum_pos_exists {α β : Type} [Fintype α] [DecidableEq β] {p : α → ENNReal}
    {f : α → β} {y : β} :
  ∑ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 →
  ∃ x : α, p x > 0 ∧ f x = y := by
  intro sum_pos
  have exists_pos : ∃ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 := by
    by_contra h
    have all_zero : ∀ a ∈ filter (fun a ↦ f a = y) univ, p a = 0 := by
      intro a ha
      apply le_antisymm
      · push_neg at h
        exact h a ha
      · simp_all only [gt_iff_lt, mem_filter, mem_univ, true_and, not_exists, not_and, not_lt,
        nonpos_iff_eq_zero, le_refl]
    simp_all only [Finset.sum_eq_zero all_zero, sum_const_zero, gt_iff_lt, lt_self_iff_false]
  rcases exists_pos with ⟨x, h_mem, h_p_pos⟩
  -- Membership in filter means f x = y
  simp only [filter_subset, mem_filter, mem_univ, true_and] at h_mem
  subst h_mem
  simp_all only [gt_iff_lt]
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl
    }
    · simp_all only

/-- Any element in finset contributes to supremum over filtered sums --/
@[simp]
lemma ENNReal.le_iSup_finset {α : Type} {s : Finset α} {f : α → ENNReal} :
    ∑ a ∈ s, f a ≤ ⨆ (t : Finset α), ∑ a ∈ t, f a := by
  -- Use s as witness for supremum bound
  exact le_iSup_iff.mpr fun b a ↦ a s

/-- If there exists an element with positive value, then the telescope sum is positive --/
@[simp]
lemma ENNReal.tsum_pos_of_exists {α : Type} {f : α → ENNReal} (h : ∃ a : α, f a > 0) :
  (∑' a, f a) > 0 := by
  -- Extract the element with positive value
  rcases h with ⟨a₀, h_pos⟩

  -- Show that sum is at least as large as the term f a₀
  have h_le : f a₀ ≤ ∑' a, f a := by
    apply ENNReal.le_tsum

  -- Since f a₀ > 0 and sum ≥ f a₀, the sum must be positive
  exact lt_of_lt_of_le h_pos h_le

/-- If there exists a positive element satisfying filter condition, filtered sum is positive --/
@[simp]
lemma exists_pos_filter_sum_pos {α β : Type} {p : α → ENNReal} {f : α → β} {y : β} :
  (∃ x : α, 0 < p x ∧ f x = y) →
  ∃ x : α, 0 < p x ∧ f x = y := by
  rintro ⟨x, h_p_pos, h_fx_eq_y⟩
  exact ⟨x, h_p_pos, h_fx_eq_y⟩

/-- Filter of non-equal elements is equivalent to erase operation --/
@[simp]
lemma filter_erase_equiv {U : Type}
  [DecidableEq U] [Fintype U] (u : U) :
  filter (fun v => v ≠ u) univ = univ.erase u := by
  ext v
  simp only [mem_filter, mem_erase, mem_univ, true_and]
  exact Iff.symm (and_iff_left_of_imp fun a ↦ trivial)

lemma pmf_map_apply_eq_tsum {α β : Type} [Fintype α] [DecidableEq β] {p : α → ENNReal}
  (h_pmf : ∑ a, p a = 1) (f : α → β) (y : β) :
  (PMF.map f (PMF.ofFintype p h_pmf)) y = ∑' (a : α), if y = f a
    then (PMF.ofFintype p h_pmf) a else 0 := by
  simp only [PMF.map_apply]; simp_all only [PMF.ofFintype_apply]

lemma filter_mem_iff {α β : Type} [Fintype α] [DecidableEq β] {f : α → β} {y : β} {x : α} :
  x ∈ filter (fun a ↦ f a = y) univ ↔ f x = y := by
  simp only [mem_filter, mem_univ, true_and]

@[simp]
lemma tsum_eq_filter_sum {α β : Type} [Fintype α] [DecidableEq β]
    {p : α → ENNReal} {y : β} (f : α → β) :
  (∑' (a : α), if y = f a then p a else 0) = ∑ a ∈ filter (fun a ↦ f a = y) univ, p a := by
  rw [tsum_fintype]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    simp only [mem_filter, mem_univ, true_and]
    by_cases h : f a = y
    · simp [h]
    · simp [h]; exact fun a_1 ↦ h (id (Eq.symm a_1))
  · intro a ha; simp_all only [mem_filter, mem_univ, true_and]

@[simp]
lemma pmf_ofFintype_apply_eq {α : Type} [Fintype α]
  {p : α → ENNReal} (h_pmf : ∑ a, p a = 1) (a : α) :
  (PMF.ofFintype p h_pmf) a = p a := by
  simp only [PMF.ofFintype_apply]

@[simp]
lemma filter_sum_pos_iff_exists_pos {α β : Type} [Fintype α]
  [DecidableEq β] {p : α → ENNReal} {f : α → β} {y : β} :
  (∑ a ∈ filter (fun a ↦ f a = y) univ, p a) > 0 ↔
  ∃ x : α, f x = y ∧ p x > 0 := by
  constructor
  · intro h_pos
    have exists_pos : ∃ a ∈ filter (fun a ↦ f a = y) univ, p a > 0 := by
      by_contra h
      have all_zero : ∀ a ∈ filter (fun a ↦ f a = y) univ, p a = 0 := by
        intro a ha
        apply le_antisymm
        · push_neg at h
          exact h a ha
        · exact zero_le (p a)
      have sum_zero := Finset.sum_eq_zero all_zero
      exact not_lt_of_ge (by exact nonpos_iff_eq_zero.mpr sum_zero) h_pos
    rcases exists_pos with ⟨x, hx_mem, hx_pos⟩
    exact ⟨x, filter_mem_iff.mp hx_mem, hx_pos⟩
  · rintro ⟨x, hx_mem, hx_pos⟩
    simp_all only [mem_filter, mem_univ, true_and, gt_iff_lt]
    subst hx_mem
    have x_in_filter : x ∈ filter (fun a ↦ f a = f x) univ := by
      simp only [filter_mem_iff]
    have sum_ge_x : ∑ a ∈ filter (fun a ↦ f a = f x) univ, p a ≥ p x := by
      exact CanonicallyOrderedAddCommMonoid.single_le_sum x_in_filter
    exact lt_of_lt_of_le hx_pos sum_ge_x

/-- Main aux lemma:
    For a mapped PMF, the probability of a state is positive if and only if
    there exists a preimage with positive probability --/
@[simp]
lemma pmf_map_pos_iff_exists_pos {α β : Type}
    {p : α → ENNReal} (f : α → β) (y : β) :
    (∃ x : α, f x = y ∧ 0 < p x) ↔
    ∃ x : α, p x > 0 ∧ f x = y := by
  constructor
  · intro h_pos
    rcases h_pos with ⟨x, hx_eq, hx_pos⟩
    use x
  · intro h_exists
    rcases h_exists with ⟨x, hx_pos, hx_eq⟩
    rw [← hx_eq]
    rw [hx_eq]
    rw [← hx_eq]
    use x
lemma Array.mkArray_size {α : Type} (n : ℕ) (a : α) :
  (Array.replicate n a).size = n := by simp only [size_replicate]

lemma Array.mkArray_get {α : Type} (n : ℕ) (a : α) (i : Nat) (h : i < n) :
  (Array.replicate n a)[i]'(by rw [Array.size_replicate]; exact h) = a :=
    getElem_replicate (Eq.mpr (id (congrArg (fun _a ↦ i < _a) size_replicate)) h)

/--
Proves that `Array.mkArray` creates valid parameters for a Hopfield network.
Given a vertex `u` in a Hopfield network with `n` nodes, this lemma establishes that:
1. The array `σ_u` has size equal to `κ1 u`
2. The array `θ_u` has size equal to `κ2 u`
3. All elements in `σ_u` are initialized to 0
4. All elements in `θ_u` are initialized to 0
where `κ1` and `κ2` are dimension functions defined in the `HopfieldNetwork` structure.
-/
lemma Array.mkArray_creates_valid_nn_params {α : Type} (κ₁ κ₂ : α → ℕ) (u : α) (a₁ a₂ : ℝ) :
  let σ_u := Array.replicate (κ₁ u) a₁
  let θ_u := Array.replicate (κ₂ u) a₂
  σ_u.size = κ₁ u ∧
  θ_u.size = κ₂ u ∧
  (∀ i : Nat, ∀ h : i < κ₁ u, σ_u[i]'(by {
    simp only [σ_u]; rw [Array.mkArray_size]; exact h }) = a₁) ∧
  (∀ i : Nat, ∀ h : i < κ₂ u, θ_u[i]'(by {
    simp only [θ_u]; rw [Array.mkArray_size]; exact h }) = a₂) := by
  let σ_u := Array.replicate (κ₁ u) a₁
  let θ_u := Array.replicate (κ₂ u) a₂
  refine ⟨Array.size_replicate .., Array.size_replicate .., ?_, ?_⟩
  · intro i h; exact Array.getElem_replicate ..
  · intro i h; exact Array.getElem_replicate ..
