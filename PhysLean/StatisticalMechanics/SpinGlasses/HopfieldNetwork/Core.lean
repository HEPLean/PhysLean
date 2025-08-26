/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Vector.Defs
import Init.Data.Vector.Lemmas
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.aux
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.NeuralNetwork

open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U]

/--
`HNfnet` computes the weighted sum of predictions for all elements in `U`, excluding `u`.
-/
abbrev HNfnet (u : U) (wu : U → R) (pred : U → R) : R := ∑ v ∈ {v | v ≠ u}, wu v * pred v

lemma HNfnet_eq (u : U) (wu : U → R) (pred : U → R) (hw : wu u = 0) :
    HNfnet u wu pred = ∑ v, wu v * pred v := by
  simp_rw [sum_filter, ite_not]
  rw [Finset.sum_congr rfl]
  intros v _
  rw [ite_eq_right_iff, zero_eq_mul]
  intros hvu
  left
  rwa [hvu]

/--
`HNfact` returns `1` if `θ` is less than or equal to `input`, otherwise `-1`.
-/
abbrev HNfact (θ input : R) : R := if θ ≤ input then 1 else -1

/--
`HNfout` is an identity function that returns its input unchanged.
-/
abbrev HNfout (act : R) : R := act

/--
`HopfieldNetwork` is a type of neural network with parameters `R` and `U`.

- `R`: A linear ordered field.
- `U`: A finite, nonempty set of neurons with decidable equality.
-/
abbrev HopfieldNetwork (R U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
   [DecidableEq U] [Nonempty U] [Fintype U] : NeuralNetwork R U R where
  /- The adjacency relation between neurons `u` and `v`, defined as `u ≠ v`. -/
  Adj u v := u ≠ v
  /- The set of input neurons, defined as the universal set. -/
  Ui := Set.univ
  /- The set of output neurons, defined as the universal set. -/
  Uo := Set.univ
  /- A proof that the intersection of the input and output sets is empty. -/
  hhio := Set.empty_inter (Set.univ ∪ Set.univ)
  /- The set of hidden neurons, defined as the empty set. -/
  Uh := ∅
  /- A proof that all neurons are in the universal set. -/
  hU := by simp only [Set.mem_univ, Set.union_self, Set.union_empty]
  /- A proof that the input set is not equal to the empty set. -/
  hUi := Ne.symm Set.empty_ne_univ
  /- A proof that the output set is not equal to the empty set. -/
  hUo := Ne.symm Set.empty_ne_univ
  /- A property that the weight matrix `w` is symmetric. -/
  pw w := w.IsSymm
  /- κ₁ is 0 for every neuron. -/
  κ1 _ := 0
  /- κ₂ is 1 for every neuron. -/
  κ2 _ := 1
  /- The network function for neuron `u`, given weights `w` and predecessor states `pred`. -/
  fnet u w pred _ := HNfnet u w pred
  /- The activation function for neuron `u`, given input and threshold `θ`. -/
  fact u _ net_input_val θ_vec := HNfact (θ_vec.get 0) net_input_val
  /- The output function is identity since σ = R here. -/
  fout _ act := act
  /- Optional σ → R map; identity since σ = R. -/
  m := id
  /- A predicate that the activation state `act` is either 1 or -1. -/
  pact act := act = 1 ∨ act = -1
  /- A proof that the activation state of neuron `u`
    is determined by the threshold `θ` and the network function. -/
  hpact w _ _ _ θ act _ u :=
    ite_eq_or_eq ((θ u).get 0 ≤ HNfnet u (w u) fun v => HNfout (act v)) 1 (-1)

variable [Nonempty U]

/--
In a Hopfield network, two neurons are adjacent if and only if they are different.
This formalizes the fully connected nature of Hopfield networks.
-/
lemma HopfieldNetwork.all_nodes_adjacent (u v : U) :
    ¬(HopfieldNetwork R U).Adj u v → u = v := by
  intro h
  unfold HopfieldNetwork at h
  simp only [ne_eq] at h
  simp_all only [Decidable.not_not]

/-- In a Hopfield network, activation values can only be 1 or -1. -/
lemma hopfield_value_dichotomy
  (val : R) (hval : (HopfieldNetwork R U).pact val) :
  val ≠ 1 → val = -1 := by
  intro h_not_one
  unfold HopfieldNetwork at hval
  simp only at hval
  cases hval with
  | inl h_eq_one =>
    contradiction
  | inr h_eq_neg_one =>
    exact h_eq_neg_one

/--
Extracts the first element from a vector of length 1.
-/
def θ' : Vector R ((HopfieldNetwork R U).κ2 u) → R := fun (θ : Vector R 1) => θ.get 0

/--
Computes the outer product of two patterns in a Hopfield Network.

Returns:
- A matrix where each element `(i, j)` is the product of the
activations of `p1` at `i` and `p2` at `j`.
-/
abbrev outerProduct (p1 : (HopfieldNetwork R U).State)
  (p2 : (HopfieldNetwork R U).State) : Matrix U U R := fun i j => p1.act i * p2.act j

variable {s : (HopfieldNetwork R U).State}

lemma NeuralNetwork.State.act_one_or_neg_one (u : U) : s.act u = 1 ∨ s.act u = -1 := s.hp u

/-- Instances o establish decidability of equality for network states
  under certain conditions. -/
instance decidableEqState :
  DecidableEq ((HopfieldNetwork R U).State) := by
  intro s₁ s₂
  apply decidable_of_iff (∀ u, s₁.act u = s₂.act u) ⟨fun h ↦ ext h, fun h u ↦ by rw [h]⟩

/--
Defines the Hebbian learning rule for a Hopfield Network.

Given a set of patterns `ps`, this function returns the network parameters
using the Hebbian learning rule, which adjusts weights based on pattern correlations.
-/
def Hebbian {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) : Params (HopfieldNetwork R U) where
  /- The weight matrix, calculated as the sum of the outer products of the patterns minus
      a scaled identity matrix. -/
  w := ∑ k, outerProduct (ps k) (ps k) - (m : R) • (1 : Matrix U U R)
  /- The threshold function, which is set to a constant value of 0 for all units. -/
  θ u := ⟨#[0], rfl⟩
  /- The state function, which is set to an empty vector. -/
  σ _ := Vector.emptyWithCapacity 0
  /- A proof that the weight matrix is symmetric and satisfies the Hebbian learning rule. -/
  hw u v huv := by
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [Finset.sum_apply, Finset.sum_apply]
    have : ∀ k i, (ps k).act i * (ps k).act i = 1 := by
      intros k i ; rw [mul_self_eq_one_iff.mpr]; exact act_one_or_neg_one i
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    conv => enter [1, 1, 2];
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_apply_eq,
      sub_self]
  /- A proof that the weight matrix is symmetric. -/
  hw' := by
    simp only [Matrix.IsSymm, Fin.isValue, transpose_sub, transpose_smul, transpose_one, sub_left_inj]
    rw [isSymm_sum]
    intro k
    refine IsSymm.ext_iff.mpr (fun i j => CommMonoid.mul_comm ((ps k).act j) ((ps k).act i))

variable (wθ : Params (HopfieldNetwork R U))

@[simp]
lemma act_up_def : (s.Up wθ u).act u =
    (if (wθ.θ u : Vector R ((HopfieldNetwork R U).κ2 u)).get 0 ≤ s.net wθ u then 1 else -1) := by
  simp only [Up, reduceIte, Fin.isValue]
  rfl

@[simp]
lemma act_of_non_up (huv : v2 ≠ u) : (s.Up wθ u).act v2 = s.act v2 := by
  simp [Up, huv]

@[simp]
lemma act_new_neg_one_if_net_lt_th (hn : s.net wθ u < θ' (wθ.θ u)) : (s.Up wθ u).act u = -1 := by
  rw [act_up_def]; exact ite_eq_right_iff.mpr fun hyp => (hn.not_ge hyp).elim

@[simp]
lemma actnew_neg_one_if_net_lt_th (hn : s.net wθ u < θ' (wθ.θ u)) : (s.Up wθ u).act u = -1 :=
  ((s.Up wθ _).act_one_or_neg_one _).elim (fun _ => act_new_neg_one_if_net_lt_th wθ hn) id

@[simp]
lemma act_new_neg_one_if_not_net_lt_th (hn : ¬s.net wθ u < θ' (wθ.θ u)) : (s.Up wθ u).act u = 1 := by
  rw [act_up_def]; exact ite_eq_left_iff.mpr fun hyp => (hn (lt_of_not_ge hyp)).elim

@[simp]
lemma act_new_neg_one_if_net_eq_th (hn : s.net wθ u = θ' (wθ.θ u)) : (s.Up wθ u).act u = 1 := by
  rw [act_up_def]; exact ite_eq_left_iff.mpr fun hyp => (hyp (le_iff_lt_or_eq.mpr (Or.inr hn.symm))).elim

@[simp]
lemma activ_old_one (hc : (s.Up wθ u).act u ≠ s.act u) (hn : s.net wθ u < θ' (wθ.θ u)) : s.act u = 1 :=
  (act_one_or_neg_one _).elim id (fun h2 => (hc (actnew_neg_one_if_net_lt_th wθ hn ▸ h2.symm)).elim)

@[simp]
lemma actnew_one (hn : ¬s.net wθ u < θ' (wθ.θ u)) : (s.Up wθ u).act u = 1 :=
  ((s.Up wθ _).act_one_or_neg_one _).elim id (fun _ => act_new_neg_one_if_not_net_lt_th wθ hn)

@[simp]
lemma activ_old_neg_one (hc : (s.Up wθ u).act u ≠ s.act u) (_ : ¬s.net wθ u < θ' (wθ.θ u))
  (hnew : (s.Up wθ u).act u = 1) : s.act u = -1 :=
(act_one_or_neg_one _).elim (fun h1 => (hc (hnew ▸ h1.symm)).elim) id

@[simp]
lemma act_eq_neg_one_if_up_act_eq_one_and_net_eq_th (hc : (s.Up wθ u).act u ≠ s.act u)
  (h2 : s.net wθ u = θ' (wθ.θ u)) (hactUp : (s.Up wθ u).act u = 1) : s.act u = -1 :=
activ_old_neg_one wθ hc h2.symm.not_gt hactUp

/--
`NeuralNetwork.State.Wact` computes the weighted activation for neurons `u` and `v`
by multiplying the weight `wθ.w u v` with their activations `s.act u` and `s.act v`.
-/
abbrev NeuralNetwork.State.Wact u v := wθ.w u v * s.act u * s.act v

/--
`NeuralNetwork.State.Eθ` computes the sum of `θ' (wθ.θ u) * s.act u` for all `u`.
-/
def NeuralNetwork.State.Eθ := ∑ u, θ' (wθ.θ u) * s.act u

/--
`NeuralNetwork.State.Ew` computes the energy contribution from the weights in a state.
It is defined as `-1/2` times the sum of `s.Wact wθ u v2` for all `u` and `v2` where `v2 ≠ u`.
-/
def NeuralNetwork.State.Ew := - 1/2 * (∑ u, (∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ u v2))

/--
Calculates the energy `E` of a state `s` in a Hopfield Network.

The energy is the sum of:
- `Ew` : Weighted energy component.
- `Eθ` : Threshold energy component.

Arguments:
- `s`: A state in the Hopfield Network.
-/
def NeuralNetwork.State.E (s : (HopfieldNetwork R U).State) : R := s.Ew wθ + s.Eθ wθ

@[simp]
lemma Wact_sym (v1 v2 : U) : s.Wact wθ v1 v2 = s.Wact wθ v2 v1 := by
  by_cases h : v1 = v2;
  · simp_rw [mul_comm, h]
  · simp_rw [mul_comm, congrFun (congrFun (id (wθ.hw').symm) v1) v2]
    exact mul_left_comm (s.act v2) (s.act v1) (wθ.w v2 v1)

@[simp]
lemma Ew_update_formula_split : s.Ew wθ = (- ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u) +
  - 1/2 * ∑ v1, (∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, s.Wact wθ v1 v2) := by

  have Ew_sum_formula_eq :
    ∑ v1, (∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 = u}, s.Wact wθ v1 v2) =
    ∑ v1, (∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 = u}, s.Wact wθ v1 v2) := by
    rw [sum_congr rfl]; intro v1 _; rw [sum_congr]
    ext v2; simp only [mem_filter, mem_univ, true_and, and_congr_left_iff, iff_self_and]
    intro hv2 hnv1; rw [← hv2]; exact fun hv1v2 => hnv1 (id (hv1v2.symm)); intro v2 _; rfl

  calc _ = -1 / 2 * ∑ v1 : U, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v1 = u}, s.Wact wθ v1 v2 +
           -1 / 2 * ∑ v1 : U, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v1 ≠ u}, s.Wact wθ v1 v2 := ?_
       _ = -1 / 2 * ∑ v1 : U, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v1 = u}, s.Wact wθ v1 v2 +
           -1 / 2 * (∑ v1 : U, ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 = u}, s.Wact wθ v1 v2 +
             ∑ v1 : U, ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, s.Wact wθ v1 v2) := ?_
       _ = (- ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u) +
            - 1/2 * ∑ v1, (∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, s.Wact wθ v1 v2) := ?_
  · simp only [Ew, mem_filter, mem_univ, true_and, true_implies, mul_sum, and_imp,
     ← sum_add_distrib, ← sum_split]
  · simp only [← sum_add_distrib, sum_congr, div_eq_zero_iff, neg_eq_zero,
      one_ne_zero, OfNat.ofNat_ne_zero, or_self, or_false, ← sum_split]
  · rw [mul_add, ← add_assoc, add_right_cancel_iff]

    have sum_v1_v2_not_eq_v1_eq_u :
        ∑ v1, (∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v1 = u}, s.Wact wθ v1 v2) = ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ u v2 := by
      rw [Fintype.sum_eq_single u]; simp only [and_true];
      intro v1 hv1; simp_all only [and_false, filter_False, sum_empty]
    rw [sum_v1_v2_not_eq_v1_eq_u]

    have sum_v1_v2_not_eq_v1_eq_u' :
    ∑ v1, (∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 = u}, s.Wact wθ v1 v2) = ∑ v1 ∈ {v1 | v1 ≠ u}, s.Wact wθ u v1 := by
      rw [← Ew_sum_formula_eq]; nth_rw 2 [sum_over_subset]; rw [sum_congr rfl]; intro v1 hv1
      have sum_Wact_v1_u : ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 = u}, s.Wact wθ v1 v2 = if v1 ≠ u then s.Wact wθ v1 u else 0 := by
        split
        · rw [sum_filter]; rw [sum_eq_single u]
          · simp_all only [ne_eq, and_true, ite_not, ite_eq_right_iff]
            intro a; subst a; simp_all only [not_true_eq_false]
          · intro hv1 _ a; simp_all only [mem_univ, and_false, reduceIte]
          · intro a; simp_all only [mem_univ, not_true_eq_false]
        · simp_all only [Decidable.not_not, not_and_self, filter_False, sum_empty]
      simp_rw [sum_Wact_v1_u, ite_not, mem_filter, mem_univ, true_and];
      split; next h => exact (if_neg fun hv1u => hv1u h).symm; ; exact Wact_sym wθ v1 u

    rw [← sum_v1_v2_not_eq_v1_eq_u', ← Ew_sum_formula_eq]
    have sum_Wact_eq_sum_Wact_sym : ∑ v1, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 = u}, s.Wact wθ v1 v2 =
      ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u := by
      rw [Ew_sum_formula_eq, sum_v1_v2_not_eq_v1_eq_u']; apply sum_congr rfl (fun _ _ => Wact_sym wθ u _)
    rw [sum_Wact_eq_sum_Wact_sym, mul_sum, ← sum_add_distrib, ← sum_neg_distrib];
    congr; apply funext; intro v2;
    rw [← mul_add, (two_mul (Wact wθ v2 u)).symm, div_eq_mul_inv]
    simp_all only [neg_mul, one_mul, isUnit_iff_ne_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_left]

@[simp]
lemma Ew_diff' : (s.Up wθ u).Ew wθ - s.Ew wθ =
    - ∑ v2 ∈ {v2 | v2 ≠ u}, (s.Up wθ u).Wact wθ v2 u - (- ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u) := by
  rw [Ew_update_formula_split, Ew_update_formula_split, sub_eq_add_neg, sub_eq_add_neg]
  simp only [neg_add_rev, neg_neg]; rw [mul_sum, mul_sum]
  calc _ = -∑ v2 ∈ {v2 | v2 ≠ u}, (s.Up wθ u).Wact wθ v2 u +
           (∑ v1, -1 / 2 * ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, (s.Up wθ u).Wact wθ v1 v2 +
           -∑ v1, -1 / 2 * ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, s.Wact wθ v1 v2) +
            ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u := ?_
       _ = - ∑ v2 ∈ {v2 | v2 ≠ u}, (s.Up wθ u).Wact wθ v2 u - (- ∑ v2 ∈ {v2 | v2 ≠ u}, s.Wact wθ v2 u) := ?_
  · nth_rw 2 [← add_assoc]; rw [(add_assoc
      (-∑ v2 ∈ {v2 | v2 ≠ u}, Wact wθ v2 u + ∑ v1, -1 / 2 *
        ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, (s.Up wθ u).Wact wθ v1 v2)
      (-∑ v1, -1 / 2 * ∑ v2 ∈ {v2 | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u}, s.Wact wθ v1 v2)
       (∑ v2 ∈ {v2 | v2 ≠ u}, Wact wθ v2 u))]
  · simp only [sub_neg_eq_add, add_left_inj, add_eq_left]
    rw [← sum_neg_distrib, ← sum_add_distrib, sum_eq_zero]
    simp only [mem_univ, true_implies]; intro v1
    rw [mul_sum, mul_sum, ← sum_neg_distrib, ← sum_add_distrib, sum_eq_zero]
    simp only [mem_filter, mem_univ, true_and, and_imp]; intro v2 _ hv1 hvneg2
    simp_all only [Wact, Up, mul_ite, ite_mul, reduceIte, add_neg_cancel]
    simp only [↓reduceDIte, add_neg_cancel]
  simp only [sub_neg_eq_add]

@[simp]
lemma θ_stable : ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * s.act v2 =
    ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * (s.Up wθ u).act v2 := by
  rw [sum_congr rfl]; intro v2 hv2; rw [act_of_non_up]
  simp only [mem_filter, mem_univ, true_and] at hv2; assumption

lemma θ_formula : ∑ v2, θ' (wθ.θ v2) * s.act v2 = θ' (wθ.θ u) * s.act u +
    ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * s.act v2 := by
  have : ∑ v2 ∈ {v2 | v2 = u}, θ' (wθ.θ v2) * s.act v2 = θ' (wθ.θ u) * s.act u := by
    rw [sum_filter]; simp only [sum_ite_eq', mem_univ, reduceIte]
  rw [← this]; rw [sum_filter_add_sum_filter_not]

@[simp]
theorem Eθ_diff : (s.Up wθ u).Eθ wθ - s.Eθ wθ = θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := by
  calc _ =  θ' (wθ.θ u) * (s.Up wθ u).act u + ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * (s.Up wθ u).act v2 +
          - (θ' (wθ.θ u) * s.act u + ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * s.act v2) := ?_
       _ = θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := ?_
  · unfold NeuralNetwork.State.Eθ; rw [θ_formula, θ_formula, θ_stable]
    rw [sub_eq_add_neg (θ' (wθ.θ u) * (s.Up wθ u).act u +
        ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * ((s.Up wθ u).Up wθ u).act v2)
        (θ' (wθ.θ u) * s.act u + ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * s.act v2)]
  · rw [neg_add_rev, (add_assoc (θ' (wθ.θ u) * (s.Up wθ u).act u +
      ∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * (s.Up wθ u).act v2)
       (-∑ v2 ∈ {v2 | v2 ≠ u}, θ' (wθ.θ v2) * s.act v2) (-(θ' (wθ.θ u) * s.act u))).symm]
    simp only [add_assoc, add_right_inj, add_eq_left]; nth_rw 2 [θ_stable]
    rw [sub_eq_add_neg, mul_add, mul_neg]; simp only [add_neg_cancel_left]

@[simp]
lemma E_final_Form : (s.Up wθ u).E wθ - s.E wθ = (s.act u - (s.Up wθ u).act u) *
    ((∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act v2) - θ' (wθ.θ u)) := by
  calc _ = (s.Up wθ u).Eθ wθ- s.Eθ wθ +  (s.Up wθ u).Ew wθ - s.Ew wθ := ?_
       _ = ∑ v2 ∈ {v2 | v2 ≠ u}, (- wθ.w v2 u * (s.Up wθ u).act v2 * (s.Up wθ u).act u +
         (wθ.w v2 u * s.act v2 * s.act u)) + θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := ?_
       _ = ∑ v2 ∈ {v2 | v2 ≠ u}, (- wθ.w v2 u * s.act v2 * (s.Up wθ u).act u + wθ.w v2 u * s.act v2 * s.act u)
          + θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := ?_
       _ = ∑ v2 ∈ {v2 | v2 ≠ u}, - (wθ.w v2 u * s.act v2 * ((s.Up wθ u).act u - s.act u))
          + θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := ?_
       _ = ((s.Up wθ u).act u - s.act u) * ∑ v2 ∈ {v2 | v2 ≠ u}, - (wθ.w v2 u * s.act v2)
          + θ' (wθ.θ u) * ((s.Up wθ u).act u - s.act u) := ?_
       _ = ((s.Up wθ u).act u - s.act u) * (∑ v2 ∈ {v2 | v2 ≠ u}, - (wθ.w v2 u * s.act v2) + θ' (wθ.θ u)) := ?_
       _ =  ((s.Up wθ u).act u - s.act u) * - (∑ v2 ∈ {v2 | v2 ≠ u}, (wθ.w v2 u * s.act v2) + - θ' (wθ.θ u)) := ?_
       _ = - ((s.Up wθ u).act u - s.act u) * ((∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w v2 u * s.act v2) - θ' (wθ.θ u)) := ?_
       _ = (s.act u - (s.Up wθ u).act u) * ((∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act v2) - θ' (wθ.θ u)) := ?_

  · simp_rw [NeuralNetwork.State.E, sub_eq_add_neg, neg_add_rev]
    rw [add_assoc, add_comm, ← add_assoc, add_right_comm (Eθ wθ + -Eθ wθ) (-Ew wθ) (Ew wθ) ]
  · rw [add_sub_assoc (Eθ wθ - Eθ wθ) (Ew wθ) (Ew wθ), Eθ_diff, Ew_diff']
    nth_rw 1 [add_comm]; simp only [sub_neg_eq_add, neg_mul, add_left_inj]
    rw [← sum_neg_distrib, ← sum_add_distrib]
  · rw [sum_congr rfl]; intro v2 hv2
    rw  [add_left_inj, mul_eq_mul_right_iff, mul_eq_mul_left_iff]
    left; left; rw [act_of_non_up]
    simp only [mem_filter, mem_univ, true_and] at hv2
    assumption
  · simp_rw [neg_mul, sum_neg_distrib, add_left_inj]
    rw [← sum_neg_distrib, sum_congr rfl]; intro v2 _; rw [mul_sub, add_comm, neg_sub]
    rw [sub_eq_neg_add (wθ.w v2 u * s.act v2 * s.act u) (wθ.w v2 u * s.act v2 * (s.Up wθ u).act u)]
    rw [add_comm]
  · simp only [sum_neg_distrib, mul_neg, add_left_inj, neg_inj]
    rw [mul_sum, sum_congr rfl]; intro v2 _; rw [mul_comm]
  · rw [mul_add]; nth_rw 2 [mul_comm]
  · simp_rw [sum_neg_distrib, neg_add_rev, neg_neg, mul_eq_mul_left_iff, add_comm,true_or]
  · rw [neg_mul_comm, mul_eq_mul_left_iff]; left; simp only [neg_add_rev, neg_neg, neg_sub]
    rw [(sub_eq_add_neg (θ' (wθ.θ u)) (∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w v2 u * s.act v2))]
  · simp only [neg_sub, ne_eq]; rw [mul_eq_mul_left_iff, sub_left_inj]
    left; rw [sum_congr rfl]; intro v2 hv2
    simp_all only [mem_filter, mem_univ, true_and, mul_eq_mul_right_iff]
    left; exact ((congrFun (congrFun (id (wθ.hw').symm) u) v2).symm)

@[simp]
lemma energy_diff_leq_zero (hc : (s.Up wθ u).act u ≠ s.act u) : (s.Up wθ u).E wθ ≤ s.E wθ := by
  apply le_of_sub_nonpos; rw [E_final_Form]
  by_cases hs : s.net wθ u < θ' (wθ.θ u)
  · apply mul_nonpos_of_nonneg_of_nonpos ?_ ?_
    · apply le_of_lt; apply sub_pos_of_lt;
      simp_rw [activ_old_one wθ hc hs , actnew_neg_one_if_net_lt_th wθ hs,
        neg_lt_self_iff, zero_lt_one]
    · apply le_of_lt; rwa [sub_neg]
  · apply mul_nonpos_of_nonpos_of_nonneg ?_ ?_
    · simp only [tsub_le_iff_right, zero_add]
      simp_rw [activ_old_neg_one wθ hc hs (actnew_one wθ hs),
        actnew_one wθ hs, neg_le_self_iff, zero_le_one]
    · apply sub_nonneg_of_le; rwa [← not_lt]

/--
`NeuralNetwork.State.pluses` counts the number of neurons in the state `s` with activation `1`.
-/
def NeuralNetwork.State.pluses := ∑ u, if s.act u = 1 then 1 else 0

@[simp]
theorem energy_lt_zero_or_pluses_increase (hc : (s.Up wθ u).act u ≠ s.act u) :
    (s.Up wθ u).E wθ < s.E wθ ∨ (s.Up wθ u).E wθ = s.E wθ ∧ s.pluses < (s.Up wθ u).pluses :=
(lt_or_eq_of_le (energy_diff_leq_zero wθ hc)).elim Or.inl (fun hr => Or.inr (by
  constructor; assumption; rw [← sub_eq_zero, E_final_Form, mul_eq_zero] at hr
  cases' hr with h1 h2
  · rw [sub_eq_zero] at h1; apply sum_lt_sum;
    · simp_all only [ne_eq, not_true_eq_false]
    · simp_all only [ne_eq, not_true_eq_false]
  · rw [sub_eq_zero] at h2
    have hactUp := act_new_neg_one_if_net_eq_th wθ h2
    have hactu := act_eq_neg_one_if_up_act_eq_one_and_net_eq_th wθ hc h2 hactUp
    apply sum_lt_sum
    · intro v hv; split
      · simp only [Up, HNfact]; split
        · simp_all only [mem_univ, ne_eq]
        · apply le_refl
      · simp only [Up]; split
        · split; apply zero_le_one; apply le_refl
        · apply le_refl
    · use u; simp_rw [hactUp, reduceIte]; split
      · simp_all only [not_true_eq_false]
      · simp only [zero_lt_one, true_and, mem_univ]))

variable (extu : (HopfieldNetwork R U).State) (hext : extu.onlyUi)

/--
`stateToActValMap` maps a state from a `HopfieldNetwork` to the set `{-1, 1}`.
-/
def stateToActValMap : (HopfieldNetwork R U).State → ({-1,1} : Finset R) := fun _ => by
 simp_all only [mem_insert, mem_singleton]; apply Subtype.mk; apply Or.inr; rfl

/--
`neuronToActMap` maps a neuron `u` to its activation value in the set `{-1, 1}`.
-/
def neuronToActMap : U → ({-1,1} : Finset R) := fun _ => stateToActValMap s

/--
`stateToNeurActMap` maps a Hopfield Network state to a function that returns
the activation state (1 or -1) of a given neuron.
-/
def stateToNeurActMap : (HopfieldNetwork R U).State → (U → ({1,-1} : Finset R)) := fun s u =>
  ⟨s.act u, by simp only [mem_insert, mem_singleton, s.act_one_or_neg_one u]⟩

/--
`NeuralNetwork.stateToNeurActMap_equiv'` provides an equivalence between the `State` type
of a `HopfieldNetwork` and a function type `U → ({1, -1} : Finset R)`.
This equivalence allows for easier manipulation of neural network states.
-/
def NeuralNetwork.stateToNeurActMap_equiv' :
    (HopfieldNetwork R U).State ≃ (U → ({1,-1} : Finset R)) where
  toFun := stateToNeurActMap
  invFun := fun f =>
   { act := fun u => f u, hp := fun u => by
      simp only; cases' f u with val hval; simp only
      simp_all only [mem_insert, mem_singleton]}
  left_inv := congrFun rfl
  right_inv := congrFun rfl

instance : Fintype ((HopfieldNetwork R U).State) := Fintype.ofEquiv _ ((stateToNeurActMap_equiv').symm)

/--
`State'` is a type alias for the state of a `HopfieldNetwork` with given parameters.
-/
def State' (_ : Params (HopfieldNetwork R U)) := (HopfieldNetwork R U).State

variable {wθ : Params (HopfieldNetwork R U)}

/--
`Up'` updates the state `s` at neuron `u`.
-/
abbrev Up' (s : State' wθ) (u : U) : State' wθ := s.Up wθ u

/--
Generates a sequence of states for a Hopfield Network.

Parameters:
- `s`: A state.
- `useq`: A sequence of states.

-/
def seqStates' {wθ : Params (HopfieldNetwork R U)} (s : State' wθ) (useq : ℕ → U) : ℕ → State' wθ
  := seqStates wθ s useq

/--
Defines a ordering between two states `s1` and `s2` based on their energy `E`
and the number of pluses.
A state `s1` is before `s2` if:
- `s1` has lower energy than `s2`, or
- `s1` has the same energy as `s2`, but more pluses.
-/
def stateLt (s1 s2 : State' wθ) : Prop := s1.E wθ < s2.E wθ ∨ s1.E wθ = s2.E wθ ∧ s2.pluses < s1.pluses

@[simp]
lemma stateLt_antisym (s1 s2 : State' wθ) : stateLt s1 s2 → ¬stateLt s2 s1 := by
  rintro (h1 | ⟨_, h3⟩) (h2 | ⟨_, h4⟩)
  · exact h1.not_gt h2
  · simp_all only [lt_self_iff_false]
  · simp_all only [lt_self_iff_false]
  · exact h3.not_gt h4

/--
Defines a partial order on states. The relation `stateOrd` holds between two states `s1` and `s2`
if `s1` is equal to `s2` or if `s1` is before `s2` according to `stateLt`.
-/
def stateOrd (s1 s2 : State' wθ) : Prop := s1 = s2 ∨ stateLt s1 s2

instance StatePartialOrder : PartialOrder (State' wθ) where
  le s1 s2 := stateOrd s1 s2
  le_refl _ := Or.inl rfl
  le_trans s1 s2 s3 h12 h23 := by
    cases' h12 with h12 h12
    · cases' h23 with h23 h23
      · left; rw [h12, h23]
      · right; rw [h12]; assumption
    · cases' h23 with h23 h23; right; simp_all only; right
      have : stateLt s1 s2 → stateLt s2 s3 → stateLt s1 s3 := by
        rintro (h1 | ⟨h1, h2⟩) (h3 | ⟨h3, h4⟩)
        · left; exact lt_trans h1 h3
        · left; rw [← h3]; assumption
        · left; rw [h1]; assumption
        · right; exact ⟨h1.trans h3, h4.trans h2⟩
      exact this h12 h23
  le_antisymm s1 s2 h12 h21 := by
    cases' h12 with h12 h12
    · cases' h21 with h21 h21; assumption; assumption
    · cases' h21 with h21 h21; exact h21.symm
      by_contra; exact stateLt_antisym s1 s2 h12 h21

@[simp]
lemma stateLt_lt (s1 s2 : State' wθ) : s1 < s2 ↔ stateLt s1 s2 := by
  simp only [LT.lt]; unfold stateOrd; simp_all only [not_or]
  constructor
  · intro H; obtain ⟨hl, hr⟩ := H
    obtain ⟨_, hr⟩ := hr
    cases' hl with hl hr
    · subst hl; simp_all only [not_true_eq_false]
    · simp_all only
  · intro hs2; simp_all only [or_true, true_and]
    constructor
    · intro hs; subst hs;
      have : ¬stateLt s2 s2:= fun
        | Or.inl h1 => h1.not_gt h1
        | Or.inr ⟨_, h3⟩ => h3.not_gt h3
      exact this hs2
    · intro hs; apply stateLt_antisym s1 s2 hs2 hs

@[simp]
lemma state_act_eq (s1 s2 : State' wθ) : s1.act = s2.act → s1 = s2 := by
  intro h; cases' s1 with act1 hact1; cases' s2 with act2 hact2
  simp only at h; simp only [h]

@[simp]
lemma state_Up_act (s : State' wθ) : (Up' s u).act u = s.act u → Up' s u = s := by
  intro h; cases' s with act hact; apply state_act_eq; ext v
  by_cases huv : v = u; simp only [huv, h]; simp [Up', Up, huv, reduceIte]

@[simp]
lemma up_act_eq_act_of_up_eq (s : State' wθ) : Up' s u = s → (Up' s u).act u = s.act u := fun hs =>
  congrFun (congrArg act hs) u

@[simp]
lemma up_act_eq_iff_eq (s : State' wθ) : (Up' s u).act u = s.act u ↔ Up' s u = s := by
  exact ⟨state_Up_act s, fun hs => congrFun (congrArg act hs) u⟩

@[simp]
lemma update_less' (s : State' wθ) : Up' s u ≠ s → Up' s u < s := fun h => by
  simp only [stateLt_lt]
  apply energy_lt_zero_or_pluses_increase
  intros H
  apply h
  apply state_Up_act
  assumption

@[simp]
lemma update_le (s : State' wθ) : Up' s u ≤ s := by
  by_cases h : Up' s u = s; left; assumption
  right; simp only [← stateLt_lt]; exact update_less' s h

@[simp]
lemma n_leq_n'_imp_sseq_n (n : ℕ) :
  (seqStates wθ s useq (n + 1)) = (seqStates wθ s useq n).Up wθ (useq n):= by
  unfold seqStates; split; rfl; simp_all only [Nat.succ_eq_add_one]; rfl

@[simp]
lemma n_leq_n'_imp_sseq_n_k'' (n : ℕ) :
  (seqStates wθ s useq (n+1)) = (seqStates wθ s useq n).Up wθ (useq n):= rfl

@[simp]
lemma n_leq_n'_imp_sseq_n_k (n k : ℕ) :
  (seqStates wθ s useq ((n + k) + 1)) = (seqStates wθ s useq (n + k)).Up wθ (useq (n + k)) := by
  simp only [seqStates]

@[simp]
lemma NeuralNetwork.n_leq_n'_imp_sseq_n'_leq_sseq''  (s : State' wθ) (n k : ℕ) :
  seqStates' s useq (n + k) ≤ seqStates' s useq n := by
  induction k with
  | zero => simp only [Nat.add_zero]; apply le_refl
  | succ k hk => rw [Nat.add_succ, seqStates', n_leq_n'_imp_sseq_n_k]; trans; apply update_le; exact hk

@[simp]
lemma not_stable_u (s : (HopfieldNetwork R U).State) : ¬s.isStable wθ → ∃ u, (s.Up wθ u) ≠ s := by
  intro h;
  obtain ⟨u, h⟩ := not_forall.mp h
  exact ⟨u, fun a => h (congrFun (congrArg act a) u)⟩

@[simp]
theorem seqStates_lt (s : State' wθ) (useq : ℕ → U) (n : ℕ) (m' : ℕ) (hm' : m' > n) :
  seqStates' s useq m' ≤ seqStates' s useq n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hm'
  rw [hk, Nat.add_left_comm k n 1]
  exact n_leq_n'_imp_sseq_n'_leq_sseq'' s n (k + 1)

variable (s s' : State' wθ)

instance : DecidablePred (fun s' => s' < s) := fun s' => by
  simp only; rw [stateLt_lt, stateLt]; exact instDecidableOr

/--
`states_less` is the set of patterns in a Hopfield Network that are less than a given state `s`.
-/
def states_less : Finset (HopfieldNetwork R U).State := {s' : State' wθ | s' < s}

open Fintype

/--
`num_of_states_less` returns the number of states that come before a given state `s`.
-/
def num_of_states_less := Fintype.card (states_less s)

@[simp]
lemma num_of_states_decreases (hs : s < s') :
  num_of_states_less s < num_of_states_less s' := by
  unfold num_of_states_less states_less
  simp only [Fintype.card_coe]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  simp only [mem_filter, mem_univ, true_and, not_lt]
  use s; exact ⟨hs, lt_irrefl s⟩
  simp only [Finset.subset_iff, mem_filter, mem_univ, true_and]
  exact fun _ hx => hx.trans hs

@[simp]
lemma num_of_states_leq_zero_implies_stable (hn : num_of_states_less s = 0) :
  s.isStable wθ := fun u => by
  cases' update_le s with h1 h2
  · exact congrFun (congrArg act h1) u
  · rw [← stateLt_lt] at h2
    unfold num_of_states_less states_less at hn
    simp only [Fintype.card_eq_zero_iff] at hn
    simp only [mem_filter, mem_univ, true_and, isEmpty_subtype] at hn
    cases hn ((s.Up wθ u)) h2

@[simp]
lemma seqStates_le' (useq : ℕ → U) (n : ℕ) (m' : ℕ) (hm' : m' ≥ n) :
  seqStates' s useq m' ≤ seqStates' s useq n := by
    simp only [ge_iff_le, le_iff_lt_or_eq] at hm'
    cases' hm' with h1 h2
    · exact seqStates_lt s useq n m' h1
    · exact le_of_eq (congrArg (seqStates wθ s useq) (id (h2.symm)))

@[simp]
lemma not_stable_implies_sseqm_lt_sseqn (useq : ℕ → U) (hf : fair useq) (n : ℕ)
    (hstable : ¬ (seqStates' s useq n).isStable wθ) :
  ∃ m, m ≥ n ∧ (seqStates' s useq m) < (seqStates' s useq n) := by
  obtain ⟨u, hc⟩ := not_forall.mp hstable
  obtain ⟨m', ⟨hm', hu⟩⟩ := hf u n
  have : seqStates' s useq m' ≤ (seqStates' s useq n) := seqStates_le' s useq n m' hm'
  cases' (le_iff_lt_or_eq.mp this) with h1 h2
  · use m';
  · use m' + 1; constructor
    · exact Nat.le_add_right_of_le hm'
    · calc _ < _ := ?_
           _ = _ := h2
      · apply update_less' (seqStates' s useq m')
        intro a; simp_all only [not_true_eq_false]

@[simp]
lemma num_of_states_leq_c_implies_stable_sseq (s : (HopfieldNetwork R U).State)
  (useq : ℕ → U) (hf : fair useq) (c : ℕ) :
    ∀ n : ℕ, (@num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq n)) ≤ c →
  ∃ m ≥ n, (@seqStates' _ _ _ _ _ _ _ _ wθ s useq m).isStable wθ := by
  induction' c with c hc
  · intros n hn; use n; constructor
    · apply Nat.le_refl
    · apply num_of_states_leq_zero_implies_stable
      simp only [nonpos_iff_eq_zero] at hn; assumption
  · intros n hn;
    by_cases H : (@seqStates' _ _ _ _ _ _ _ _ wθ s useq n).isStable wθ
    · use n
    · obtain ⟨m, ⟨hm, hlt⟩⟩ := not_stable_implies_sseqm_lt_sseqn s useq hf n H
      have : @num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq m)
        < @num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq n) := by
          apply num_of_states_decreases; assumption
      have : @num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq m) ≤ c := by
        apply Nat.le_of_lt_succ;
        rw [← Nat.succ_eq_add_one] at hn
        calc _ < @num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq n) := this
             _ ≤ c.succ := hn
      obtain ⟨m', ⟨hm', hstable⟩⟩ := hc m this
      use m'; constructor
      trans; assumption; assumption; assumption

@[simp]
theorem HopfieldNet_convergence_fair : ∀ (useq : ℕ → U), fair useq →
  ∃ N, (seqStates' s useq N).isStable wθ := fun useq hfair => by
  let c := @num_of_states_less _ _ _ _ _ _ _ _ wθ (seqStates' s useq 0)
  obtain ⟨N, ⟨_, hN⟩⟩ := num_of_states_leq_c_implies_stable_sseq s useq hfair c 0 (Nat.le_refl c)
  use N

instance (s : State' wθ): Decidable (isStable wθ s) := Fintype.decidableForallFintype

/--
A function that returns the stabilized state after updating.
-/
def HopfieldNet_stabilize (wθ : Params (HopfieldNetwork R U))
    (s : State' wθ) (useq : ℕ → U) (hf : fair useq) : State' wθ :=
  (seqStates' s useq) (Nat.find (HopfieldNet_convergence_fair s useq hf))

@[simp]
lemma isStable_HN_stabilize : ∀ (s : State' wθ) (useq : ℕ → U) (hf : fair useq),
  (HopfieldNet_stabilize wθ s useq hf).isStable wθ := fun s useq hf =>
  Nat.find_spec (HopfieldNet_convergence_fair s useq hf)

@[simp]
lemma not_stable_implies_sseqm_lt_sseqn_cyclic (useq : ℕ → U) (hf : cyclic useq) (n : ℕ)
    (hstable : ¬ (seqStates' s useq n).isStable wθ) :
  ∃ m, m ≥ n ∧ m ≤ n + card U ∧ (seqStates' s useq m) < (seqStates' s useq n) := by
  obtain ⟨u, hc⟩ := not_forall.mp hstable
  have : (Up' (seqStates' s useq n) u).act u = (seqStates' s useq n).act u ↔
      (Up' (seqStates' s useq n) u) = (seqStates' s useq n) := up_act_eq_iff_eq (seqStates' s useq n)
  rw [this] at hc
  obtain ⟨m', ⟨hm', ⟨hm, hfoo⟩⟩⟩ := cyclic_Fair_bound useq hf u n
  have :  seqStates' s useq m' ≤ (seqStates' s useq n) := seqStates_le' s useq n m' hm'
  cases' (le_iff_lt_or_eq.mp this) with h1 h2
  · use m'; constructor; exact hm'; subst hfoo
    simp_all only [gt_iff_lt, and_self, and_true]
    rw [le_iff_lt_or_eq]; left; exact hm
  · use m' + 1; simp only [ge_iff_le] at hm'; constructor
    · simp only [ge_iff_le]; exact Nat.le_add_right_of_le hm'
    · constructor
      · exact hm
      · calc _ < _ := ?_
             _ = _ := h2
        · apply update_less' (seqStates' s useq m')
          intro a; simp_all only [not_true_eq_false]

@[simp]
lemma num_of_states_leq_c_implies_stable_sseq_cyclic (s : State' wθ) (useq : ℕ → U)
  (hcy : cyclic useq) (c : ℕ) : ∀ n, num_of_states_less (seqStates' s useq n) ≤ c →
  ∃ m ≥ n, m ≤ n + card U * c ∧ (s.seqStates wθ useq m).isStable wθ := by
  induction' c with c hc
  · intros n hn; use n; constructor
    · exact Nat.le_refl n
    · constructor
      · exact Nat.le_add_right n (card U * 0)
      · apply num_of_states_leq_zero_implies_stable
        simp only [nonpos_iff_eq_zero] at hn; exact hn
  · intros n hn
    by_cases H : (s.seqStates wθ useq n).isStable wθ
    · simp only [ge_iff_le]; use n; constructor
      · exact Nat.le_refl n
      · constructor
        · exact Nat.le_add_right n (card U * (c + 1))
        · assumption
    · obtain ⟨m, ⟨hm, hlt⟩⟩ := not_stable_implies_sseqm_lt_sseqn_cyclic s useq hcy n H
      have : num_of_states_less (seqStates' s useq m) ≤ c := by
        apply Nat.le_of_lt_succ; rw [← Nat.succ_eq_add_one] at hn
        calc _ < num_of_states_less (seqStates' s useq n) :=
           num_of_states_decreases _ _ hlt.2
             _ ≤ c.succ := hn
      obtain ⟨m', ⟨hm', hstable⟩⟩ := hc m this
      use m'; constructor
      · trans; assumption; assumption
      · constructor
        · obtain ⟨hlt', _⟩ := hlt
          calc _ ≤ m + card U * c := hstable.1
               _ ≤ n + card U + card U * c :=
                  Nat.add_le_add_right hlt' (card U * c)
               _ ≤ n + card U * (c + 1) := by
                rw [add_assoc, add_le_add_iff_left,
                  mul_add, mul_one, le_iff_lt_or_eq]
                right
                exact Nat.add_comm (card U) (card U * c)
        · exact hstable.2

@[simp]
lemma num_of_states_card : card (HopfieldNetwork R U).State = 2 ^ card U := by
  rw [Fintype.card_congr (stateToNeurActMap_equiv')]
  have h3 : #({1,-1} : Finset R) = 2 := by
    refine Finset.card_pair ?h
    norm_cast
  rw [Fintype.card_fun]
  simp only [mem_insert, mem_singleton, Fintype.card_coe]
  exact congrFun (congrArg HPow.hPow h3) (card U)

@[simp]
lemma NeuralNetwork.initial_state_bound (useq : ℕ → U) :
  num_of_states_less (seqStates' s useq 0) ≤ 2 ^ card U := by
  rw [num_of_states_less, Fintype.card_of_subtype]
  rw [← @num_of_states_card R _ _ _]
  exact card_le_univ (states_less s); intros x; rfl

@[simp]
theorem HopfieldNet_convergence_cyclic : ∀ (useq : ℕ → U), cyclic useq →
    ∃ N, N ≤ card U * (2 ^ card U) ∧
  (s.seqStates wθ useq N).isStable wθ := fun useq hcy => by
  obtain ⟨N, ⟨_, ⟨hN1, hN2⟩⟩⟩ := num_of_states_leq_c_implies_stable_sseq_cyclic s
    useq hcy (2 ^ card U) 0 (initial_state_bound s useq)
  use N; constructor; simp only [zero_add] at hN1; assumption; assumption

/--
`HopfieldNet_stabilize_cyclic` stabilizes a Hopfield network given an initial state `s`,
a sequence of updates `useq`, and a proof `hf` that the sequence is cyclic.
It returns the state of the network after convergence.
-/
def HopfieldNet_stabilize_cyclic (s : State' wθ) (useq : ℕ → U) (hf : cyclic useq) : State' wθ :=
  (seqStates' s useq) (Nat.find (HopfieldNet_convergence_cyclic s useq hf))

/--
`HopfieldNet_conv_time_steps` calculates the number of time steps required for a Hopfield Network to converge.
-/
def HopfieldNet_conv_time_steps (wθ : Params (HopfieldNetwork R U)) (s : State' wθ)
    (useq : ℕ → U) (hf : cyclic useq) : ℕ :=
  (Nat.find (HopfieldNet_convergence_cyclic s useq hf))

lemma HopfieldNet_cyclic_converg (wθ : Params (HopfieldNetwork R U)) (s : State' wθ)
  (useq : ℕ → U) (hf : cyclic useq) :
    (HopfieldNet_stabilize_cyclic s useq hf).isStable wθ :=
  (Nat.find_spec (HopfieldNet_convergence_cyclic s useq hf)).2

lemma patterns_pairwise_orthogonal {m : ℕ}
  (ps : Fin m → (HopfieldNetwork R U).State)
  (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0) :
  ∀ (j : Fin m),
    ((Hebbian ps).w).mulVec (ps j).act
      = ((card U : R) - (m : R)) • (ps j).act := by
  intros k
  ext t
  unfold Hebbian
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [mulVec, dotProduct]
  simp only [sub_apply, smul_apply, smul_eq_mul, Pi.natCast_def, Pi.mul_apply, Pi.sub_apply]
  rw [Finset.sum_apply]
  simp only [Finset.sum_apply]
  unfold dotProduct at horth
  have : ∀ i j, (dotProduct (ps i).act (ps j).act) = if i ≠ j then 0 else (card U : R) := by
    intros i j
    by_cases h : i ≠ j
    · specialize horth h
      simp_all only [ne_eq, not_false_eq_true, reduceIte, Nat.cast_zero]
      assumption
    · simp only [Decidable.not_not] at h
      nth_rw 1 [h]
      simp only [ite_not, Nat.cast_ite, Nat.cast_zero]
      refine eq_ite_iff.mpr ?_
      left
      constructor
      · assumption
      · unfold dotProduct
        have hact : ∀ i, ((ps j).act i) = 1 ∨  ((ps j).act i) = -1 := fun i => act_one_or_neg_one i
        have hact1 : ∀ i, ((ps j).act i) * ((ps j).act i) = 1 := fun i => mul_self_eq_one_iff.mpr (hact i)
        calc _ = ∑ i, (ps j).act i * (ps j).act i := rfl
             _ = ∑ i, 1 * 1 := by simp_rw [hact1]; rw [mul_one]
             _ = (card U : R) := by
                  -- sum of 1 over all i in U is card U, cast to R
                  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat]
  simp only [dotProduct, ite_not, Nat.cast_ite, Nat.cast_zero] at this
  conv => enter [1,2]; ext l; rw [sub_mul]; rw [sum_mul]; conv => enter [1,2]; ext i; rw [mul_assoc]
  rw [Finset.sum_sub_distrib]
  nth_rw 1 [sum_comm]
  calc _= ∑ y : Fin m, (ps y).act t * ∑ x , ((ps y).act x * (ps k).act x)
          - ∑ x , (m : R) * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _= ∑ y : Fin m, (ps y).act t *  (if y ≠ k then 0 else (card U : R)) -
            ∑ x , (m : R) * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _ = (((card U : R) - (m : R)) * (ps k).act t)  := ?_
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]
    exact fun x _ => (mul_sum univ (fun i => (ps x).act i * (ps k).act i) ((ps x).act t)).symm
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]; intros i _
    simp_all only [reduceIte, implies_true, mem_univ, mul_ite, mul_zero, ite_not, Nat.cast_ite, Nat.cast_zero]
  · simp only [ite_not, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, reduceIte]
    conv => enter [1,2,2]; ext k; rw [mul_assoc]
    rw [← mul_sum, mul_comm]
    simp only [one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, reduceIte]
    exact (sub_mul (card U : R) (m : R) ((ps k).act t)).symm

lemma stateisStablecondition {m : ℕ}
  (ps : Fin m → (HopfieldNetwork R U).State)
  (s : (HopfieldNetwork R U).State) (c : R) (hc : 0 < c)
  (hw : ∀ u, ((Hebbian ps).w).mulVec s.act u = c * s.act u) : s.isStable (Hebbian ps) := by
  intros u
  unfold State.Up
  simp only [reduceIte, Fin.isValue]
  rw [HNfnet_eq]
  simp_rw [mulVec, dotProduct] at hw u
  refine ite_eq_iff.mpr ?_
  cases' s.act_one_or_neg_one u with h1 h2
  · left; rw [h1]; constructor
    · rw [hw, le_iff_lt_or_eq]; left; rwa [h1, mul_one]
    · rfl
  · right; rw [h2]; constructor
    · change ¬ 0 ≤ _
      rw [le_iff_lt_or_eq]
      simp only [Left.neg_pos_iff, zero_eq_neg, not_or, not_lt]
      constructor
      · rw [le_iff_lt_or_eq]; left;
        simpa only [hw, h2, mul_neg, mul_one, Left.neg_neg_iff]
      · simp_all only [List.length_nil, Nat.succ_eq_add_one,
        Nat.reduceAdd, mul_neg, mul_one, Fin.isValue, zero_eq_neg]
        exact ne_of_gt hc
    · rfl
  exact (Hebbian ps).hw u u fun a => a rfl

lemma Hebbian_stable {m : ℕ}
  (hm : m < card U) (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m)
    (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0):
  isStable (Hebbian ps) (ps j) := by
  unfold isStable
  have := patterns_pairwise_orthogonal (ps := ps) horth j
  have hmn0 : 0 < ((card U : R) - (m : R)) := by
    have : (m : R) < (card U : R) := by exact_mod_cast hm
    exact sub_pos.mpr this
  apply stateisStablecondition (ps := ps) (s := (ps j)) (((card U : R) - (m : R))) hmn0
  · intros u; rw [funext_iff] at this; exact this u
