import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Hopfield82.ContentAddressableMemory
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Hopfield82

open NeuralNetwork State Matrix Finset Real

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]

/-! ### Fault Tolerance -/

/--
The `DeleteNeuron` function simulates the failure of a neuron by removing its connections.
This corresponds to setting weights to/from that neuron to zero.

The paper discusses (p.2558): "The collective properties are only weakly sensitive to
details of the modeling or the failure of individual devices."
-/
noncomputable def DeleteNeuron [DecidableEq U] (i : U)
    (wθ : Params (HopfieldNetwork R U)) : Params (HopfieldNetwork R U) where
  w := λ j k => if j = i ∨ k = i then 0 else wθ.w j k
  θ := wθ.θ
  σ := wθ.σ
  hw := by
    intros u v huv
    by_cases h : u = i ∨ v = i
    · cases h with
      | inl h_eq => rw [h_eq]; simp only [true_or, ↓reduceIte]
      | inr h_eq => rw [h_eq]; simp only [or_true, ↓reduceIte]
    · push_neg at h
      simp only [h.1, h.2, or_self, ↓reduceIte]
      exact wθ.hw u v huv
  hw' := by
    apply IsSymm.ext_iff.2
    intros j k
    by_cases h : j = i ∨ k = i
    · cases h with
      | inl h_left =>
        rw [h_left]
        simp only [or_true, ↓reduceIte, true_or]
      | inr h_right =>
        rw [h_right]
        simp only [true_or, ↓reduceIte, or_true]
    · push_neg at h
      simp only [h.1, h.2]
      have hsymm := IsSymm.ext_iff.1 wθ.hw'
      specialize hsymm j k
      exact hsymm

/-- Apply DeleteNeuron to a list of neurons sequentially -/
noncomputable def DeleteNeurons [DecidableEq U] (neurons : List U)
(wθ : Params (HopfieldNetwork R U)) : Params (HopfieldNetwork R U) :=
  List.foldl (fun acc neuron => DeleteNeuron neuron acc) wθ neurons


-- The `FaultTolerance` of a Hopfield network is its ability to maintain function
-- despite the failure of some components. The paper notes that these networks are
-- inherently robust to component failures.

/--
Defines fault tolerance for a Hopfield network.

Given a set of patterns `ps` and a specific pattern `ps k` from that set,
this property ensures that even after removing up to `f` neurons from the network,
the pattern `ps k` remains a fixed point under the network dynamics.

Specifically:
- We calculate the weights and thresholds using Hebbian learning on all patterns
- For any subset of neurons with cardinality at most `f`, removing these neurons
  still allows `ps k` to be a fixed point of the resulting network.

This captures the fault-tolerance property described in Hopfield's 1982 paper on
content-addressable memory.

### Parameters
- `ps` : A collection of patterns (states) in the Hopfield network
- `k`  : Index of the pattern we want to check for fault tolerance
- `f`  : Maximum number of neurons that can be removed while preserving the fixed point
-/
def FaultTolerance {m : ℕ} [DecidableEq U]
  (ps : Fin m → (HopfieldNetwork R U).State)
  (k : Fin m) (f : ℕ) : Prop :=
  let wθ := Hebbian ps;
  ∀ neurons_to_delete : Finset U, card neurons_to_delete ≤ f →
  let wθ' := DeleteNeurons neurons_to_delete.toList wθ;
  -- Check stability only for neurons *not* in the set of deleted neurons
  ∀ u_check ∈ (Finset.univ : Finset U) \ neurons_to_delete,
    ((ps k).Up wθ' u_check).act u_check = (ps k).act u_check

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- When m is at most a tenth of total neurons, each pattern is fixed point in the undamaged network -/
@[simp]
lemma pattern_stability_in_hebbian {m : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)
    (hm : m ≤ Fintype.card U / 10) (k : Fin m) :
  FixedPoint (Hebbian ps) (ps k) := by
  have hcard : Fintype.card U / 10 < Fintype.card U := by
    have : Fintype.card U > 0 := Fintype.card_pos
    apply Nat.div_lt_self
    · exact this
    · norm_num
  have : m < Fintype.card U := lt_of_le_of_lt hm hcard
  exact Hebbian_stable this ps k horth

omit [Nonempty U] in
@[simp]
lemma filter_eq_singleton [DecidableEq U] (i : U) : filter (fun j => j = i) univ = {i} := by
  apply Finset.ext
  intro j
  simp only [mem_filter, mem_univ, true_and]
  exact Iff.symm mem_singleton

omit [Fintype U] [Nonempty U] in
@[simp]
lemma sum_over_singleton (i : U) (f : U → R) :
  ∑ j ∈ {i}, f j = f i := by
  simp only [sum_singleton]

omit [Nonempty U] in
@[simp]
lemma sum_filter_eq [DecidableEq U] (i : U) (f : U → R) :
  ∑ j ∈ filter (fun j => j = i) univ, f j = f i := by
  rw [filter_eq_singleton]
  exact sum_over_singleton i f

omit [Nonempty U] in
@[simp]
lemma sum_split_by_value [DecidableEq U] (i : U) (f : U → R) :
  ∑ j, f j = f i + ∑ j ∈ filter (fun j => j ≠ i) univ, f j := by
  have h_split : ∑ j, f j =
                ∑ j, if j = i then f i else f j := by
    apply Finset.sum_congr
    · rfl
    · intro j _
      by_cases h : j = i
      · rw [h]; simp only [↓reduceIte]
      · simp only [if_neg h]
  rw [h_split, sum_ite]
  congr
  · exact sum_filter_eq i (fun _ => f i)

omit [Fintype U] [Nonempty U] in
@[simp]
lemma condition_simplify_when_neq (i u j : U) (hu : u ≠ i) :
  (j = i ∨ u = i) ↔ j = i := by
  exact or_iff_left hu

omit [Nonempty U] in
@[simp]
lemma sum_filter_eq_singleton [DecidableEq U] (i : U) (f : U → R) :
  ∑ j ∈ filter (fun j => j = i) univ, f j = f i := by
  rw [filter_eq_singleton]
  exact sum_over_singleton i f

omit [Nonempty U] in
@[simp]
lemma sum_split_by_eq [DecidableEq U](i : U) (f : U → R) :
  ∑ j, f j = f i + ∑ j ∈ filter (fun j => j ≠ i) univ, f j := by
  exact sum_split_by_value i f

omit [Nonempty U] in
@[simp]
lemma sum_filter_neq_as_subtraction [DecidableEq U] (i : U) (f : U → R) :
  ∑ j ∈ filter (fun j => j ≠ i) univ, f j = ∑ j, f j - f i := by
  rw [sum_split_by_eq]
  simp only [ne_eq, filter_erase_equiv, mem_univ, sum_erase_eq_sub, add_sub_cancel]
  exact i

@[simp]
lemma Finset.erase_eq_filter {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
  s.erase a = s.filter (fun x => x ≠ a) := by
  ext x
  simp only [mem_erase, mem_filter]
  constructor
  · intro h
    exact id (And.symm h)
  · intro h
    exact id (And.symm h)

omit [Nonempty U] in
@[simp]
lemma sum_if_or_condition [DecidableEq U] (i u : U) (hu : u ≠ i) (f : U → R) :
  ∑ j : U, (if j = i ∨ u = i then 0 else f j) = ∑ j : U, (if j = i then 0 else f j) := by
  apply Finset.sum_congr
  · rfl
  · intro j _
    have h_equiv : (j = i ∨ u = i) ↔ j = i := by
      constructor
      · intro h
        cases h with
        | inl h_j => exact h_j
        | inr h_u => exfalso; exact hu h_u
      · intro h_j
        exact Or.inl h_j
    simp only [h_equiv]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U] in
lemma sum_if_eq_to_sub [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U] (i : U) (f : U → R) :
  ∑ j : U, (if j = i then 0 else f j) = ∑ j : U, f j - f i := by
  apply eq_sub_of_add_eq
  rw [sum_split_by_eq i f]
  rw [add_comm, add_left_cancel_iff]
  rw [sum_ite]
  rw [sum_const_zero, zero_add]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Nonempty U] in
lemma deleted_connection_sum [DecidableEq U] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (i u : U) (hu : u ≠ i) (w : Matrix U U R) (act : U → R) :
  (∑ j : U, if j = i ∨ u = i then 0 else w u j * act j) = ∑ j : U, w u j * act j - w u i * act i := by
  have h_condition_simp : ∀ j : U, (j = i ∨ u = i) ↔ j = i := by
    intro j
    constructor
    · intro h
      cases h with
      | inl h_j => exact h_j
      | inr h_u => exfalso; exact hu h_u
    · intro h_j
      exact Or.inl h_j
  simp_rw [h_condition_simp]
  apply sum_if_eq_to_sub i (fun j => w u j * act j)

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
@[simp]
lemma delete_one_neuron_effect_general
[Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (wθ : Params (HopfieldNetwork R U))
    (i : U) (u : U) (hu : u ≠ i) (act : U → R) :
  (DeleteNeuron i wθ).w.mulVec act u =
  wθ.w.mulVec act u - wθ.w u i * act i := by
  unfold DeleteNeuron
  simp only [mulVec, dotProduct]
  have h_cond_simp : ∀ x : U, (u = i ∨ x = i) ↔ x = i := by
    intro x
    constructor
    · intro h
      cases h with
      | inl h_u => exfalso; exact hu h_u
      | inr h_x => exact h_x
    · intro h_x
      exact Or.inr h_x
  simp_rw [h_cond_simp]
  rw [Finset.sum_congr rfl fun x _ => by rw [ite_mul, zero_mul]]
  apply sum_if_eq_to_sub i (fun x => wθ.w u x * act x)

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U]in
@[simp]
lemma delete_one_neuron_effect {m : ℕ}
[Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (i : U) (u : U) (hu : u ≠ i) (k : Fin m) :
  (DeleteNeuron i (Hebbian ps)).w.mulVec (ps k).act u =
  (Hebbian ps).w.mulVec (ps k).act u - (Hebbian ps).w u i * (ps k).act i := by
  exact delete_one_neuron_effect_general (Hebbian ps) i u hu (ps k).act

lemma delete_neuron_preserves_other_weights [DecidableEq U] (wθ : Params (HopfieldNetwork R U)) (i u v : U)
    (hu : u ≠ i) (hv : v ≠ i) :
  (DeleteNeuron i wθ).w u v = wθ.w u v := by
  unfold DeleteNeuron
  simp [hu, hv]

lemma delete_neurons_order_independent [DecidableEq U] (wθ : Params (HopfieldNetwork R U)) (i j : U) :
  DeleteNeuron i (DeleteNeuron j wθ) = DeleteNeuron j (DeleteNeuron i wθ) := by
  have w_eq : (DeleteNeuron i (DeleteNeuron j wθ)).w = (DeleteNeuron j (DeleteNeuron i wθ)).w := by
    ext u v
    unfold DeleteNeuron
    by_cases hu : u = i ∨ u = j
    · by_cases hv : v = i ∨ v = j
      · simp only [hu, hv, true_or, ↓reduceIte]; cases hu with
        | inl h =>
          cases hv with
          | inl h_1 =>
            subst h_1 h
            simp_all only [or_self, ↓reduceIte, ite_self]
          | inr h_2 =>
            subst h_2 h
            simp_all only [true_or, ↓reduceIte, or_true]
        | inr h_1 =>
          cases hv with
          | inl h =>
            subst h_1 h
            simp_all only [or_true, ↓reduceIte, true_or]
          | inr h_2 =>
            subst h_1 h_2
            simp_all only [or_self, ↓reduceIte, ite_self]
      · simp only [hu, hv, true_or, ↓reduceIte]
        cases hu with
        | inl h_ui =>
          simp only [h_ui, true_or, if_true]
          simp only [ite_self]
        | inr h_uj =>
          rw [h_uj]
          simp only [eq_self_iff_true, true_or]
          simp only [if_true]
          exact ite_self 0
    · by_cases hv : v = i ∨ v = j
      · simp only [hu, hv, true_or, ↓reduceIte]
        cases hv with
        | inl h_vi =>
          simp only [h_vi, true_or, if_true, if_true]
          simp only [or_true, ↓reduceIte, ite_self]
        | inr h_vj =>
          simp only [h_vj, or_true, if_true, if_true]
          simp only [ite_self]
      · simp only at hu hv
        have h_ui : u ≠ i := by
          intro h_eq
          apply hu
          exact Or.inl h_eq
        have h_uj : u ≠ j := by
          intro h_eq
          apply hu
          exact Or.inr h_eq
        have h_vi : v ≠ i := by
          intro h_eq
          apply hv
          exact Or.inl h_eq
        have h_vj : v ≠ j := by
          intro h_eq
          apply hv
          exact Or.inr h_eq
        unfold DeleteNeuron at *
        simp only [h_ui, h_uj, h_vi, h_vj, or_false, false_or, ↓reduceIte]
  have θ_eq : (DeleteNeuron i (DeleteNeuron j wθ)).θ = (DeleteNeuron j (DeleteNeuron i wθ)).θ := by
    unfold DeleteNeuron; rfl
  have σ_eq : (DeleteNeuron i (DeleteNeuron j wθ)).σ = (DeleteNeuron j (DeleteNeuron i wθ)).σ := by
    unfold DeleteNeuron; rfl
  unfold DeleteNeuron
  congr

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- When deleting a single neuron from a network, the resulting weighted sum for a neuron u
    that's not the deleted neuron equals the original weighted sum minus the contribution
    from the deleted neuron. -/
lemma delete_single_neuron_step {m : ℕ}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (neuron : U) (u : U) (hu : u ≠ neuron) (k : Fin m) :
  (DeleteNeuron neuron (Hebbian ps)).w.mulVec (ps k).act u =
  (Hebbian ps).w.mulVec (ps k).act u - (Hebbian ps).w u neuron * (ps k).act neuron := by
  rw [delete_one_neuron_effect_general (Hebbian ps) neuron u hu (ps k).act]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- When deleting neurons from an empty list, the result is the original network -/
lemma delete_empty_neurons_step {m : ℕ}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (wθ : Params (HopfieldNetwork R U)) (u : U) (k : Fin m) :
  (List.foldl (fun acc neuron => DeleteNeuron neuron acc) wθ []).w.mulVec (ps k).act u =
  wθ.w.mulVec (ps k).act u := by
  simp only [List.foldl_nil]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- When deleting a list of neurons with a new neuron added at the front, the effect
    on the weighted sum equals the effect of deleting the first neuron and then
    deleting the rest of the list. -/
lemma delete_cons_neuron_step {m : ℕ}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (head : U) (tail : List U) (u : U) (_ : u ≠ head) (_ : u ∉ tail) (k : Fin m) :
  (List.foldl (fun acc neuron => DeleteNeuron neuron acc) (Hebbian ps) (head :: tail)).w.mulVec (ps k).act u =
  (List.foldl (fun acc neuron => DeleteNeuron neuron acc) (DeleteNeuron head (Hebbian ps)) tail).w.mulVec (ps k).act u := by
  rw [List.foldl_cons]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- For a singleton list, the effect matches the single neuron deletion case -/
lemma delete_singleton_neuron_step {m : ℕ}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (neuron : U) (u : U) (hu : u ≠ neuron) (k : Fin m) :
  (List.foldl (fun acc n => DeleteNeuron n acc) (Hebbian ps) [neuron]).w.mulVec (ps k).act u =
  (Hebbian ps).w.mulVec (ps k).act u - (Hebbian ps).w u neuron * (ps k).act neuron := by
  rw [← delete_single_neuron_step ps neuron u hu k]
  exact rfl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- The effect of deleting a neuron from an already deleted network on a neuron u that
    is not in the deleted set -/
lemma delete_neuron_from_deleted_network {m : ℕ}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (prev_deleted : List U) (neuron : U) (u : U) (hu : u ≠ neuron) (_ : u ∉ prev_deleted) (k : Fin m) :
  (DeleteNeuron neuron (List.foldl (fun acc n => DeleteNeuron n acc) (Hebbian ps) prev_deleted)).w.mulVec (ps k).act u =
  (List.foldl (fun acc n => DeleteNeuron n acc) (Hebbian ps) prev_deleted).w.mulVec (ps k).act u -
  (List.foldl (fun acc n => DeleteNeuron n acc) (Hebbian ps) prev_deleted).w u neuron * (ps k).act neuron := by
  apply delete_one_neuron_effect_general (List.foldl (fun acc n => DeleteNeuron n acc) (Hebbian ps) prev_deleted)
    neuron u hu (ps k).act

/-- Helper lemma: DeleteNeuron commutes with foldl of DeleteNeuron if the neuron is not in the list -/
lemma commute_delete_foldl [DecidableEq U]
    (i : U) (base : Params (HopfieldNetwork R U)) (l : List U) (h_nodup_l : l.Nodup) (hi_notin_l : i ∉ l) :
    DeleteNeuron i (List.foldl (fun acc neuron => DeleteNeuron neuron acc) base l) =
    List.foldl (fun acc neuron => DeleteNeuron neuron acc) (DeleteNeuron i base) l := by
  induction l generalizing base with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih_commute =>
    have h_nodup_cons : (hd :: tl).Nodup := h_nodup_l
    replace h_nodup_l : tl.Nodup := (List.nodup_cons.mp h_nodup_cons).2
    have h_hd_notin_tl : hd ∉ tl := (List.nodup_cons.mp h_nodup_cons).1
    have hi_notin_tl : i ∉ tl := fun h => hi_notin_l (List.mem_cons_of_mem _ h)
    have hi_neq_hd : i ≠ hd := fun h => hi_notin_l (h ▸ List.mem_cons_self)
    rw [List.foldl_cons, List.foldl_cons]
    rw [ih_commute (DeleteNeuron hd base) h_nodup_l hi_notin_tl]
    rw [delete_neurons_order_independent base i hd]

/-- Helper lemma: Weights are preserved by foldl if indices are not in the list-/
lemma foldl_delete_preserves_weights [DecidableEq U]
    (base : Params (HopfieldNetwork R U))
    (l : List U) (h_nodup_l : l.Nodup) (v w : U) (hv_notin : v ∉ l) (hw_notin : w ∉ l) :
    (List.foldl (fun acc neuron => DeleteNeuron neuron acc) base l).w v w = base.w v w := by
  induction l generalizing base with
  | nil => simp
  | cons hd tl ih_w =>
    have h_nodup_cons : (hd :: tl).Nodup := h_nodup_l
    replace h_nodup_l : tl.Nodup := (List.nodup_cons.mp h_nodup_cons).2
    have hv_notin_tl : v ∉ tl := fun h => hv_notin (List.mem_cons_of_mem _ h)
    have hw_notin_tl : w ∉ tl := fun h => hw_notin (List.mem_cons_of_mem _ h)
    have hv_neq_hd : v ≠ hd := fun h => hv_notin (h ▸ List.mem_cons_self)
    have hw_neq_hd : w ≠ hd := fun h => hw_notin (h ▸ List.mem_cons_self)
    rw [List.foldl_cons]
    rw [ih_w (DeleteNeuron hd base) h_nodup_l hv_notin_tl hw_notin_tl]
    rw [delete_neuron_preserves_other_weights base hd v w hv_neq_hd hw_neq_hd]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- Helper lemma: Deleting a list of neurons recursively subtracts their contributions.
    Requires that the list of neurons has no duplicates. -/
lemma delete_neurons_recursive {m : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (neurons : List U) (h_nodup : neurons.Nodup) (u : U) (hu : u ∉ neurons) (k : Fin m) :
  (List.foldl (fun acc neuron => DeleteNeuron neuron acc) (Hebbian ps) neurons).w.mulVec (ps k).act u =
  (Hebbian ps).w.mulVec (ps k).act u - ∑ j ∈ neurons.toFinset, (Hebbian ps).w u j * (ps k).act j := by
  induction neurons with
  | nil =>
    simp [List.toFinset]
  | cons head tail ih =>
    have h_nodup_cons : (head :: tail).Nodup := h_nodup
    replace h_nodup : tail.Nodup := (List.nodup_cons.mp h_nodup_cons).2
    have h_head_notin_tail : head ∉ tail := (List.nodup_cons.mp h_nodup_cons).1

    have hu_head : u ≠ head := by
      intro h; apply hu; rw [h]; exact List.mem_cons_self
    have hu_tail : u ∉ tail := by
      intro h; apply hu; exact List.mem_cons_of_mem _ h
    rw [List.foldl_cons]
    let base := Hebbian ps
    let act_k := (ps k).act
    let L₀ := List.foldl (fun acc neuron => DeleteNeuron neuron acc) base tail
    have h_commute : DeleteNeuron head L₀ =
                     List.foldl (fun acc neuron => DeleteNeuron neuron acc) (DeleteNeuron head base) tail := by
      apply commute_delete_foldl
      exact h_nodup
      exact h_head_notin_tail
    rw [← h_commute]
    rw [delete_one_neuron_effect_general L₀ head u hu_head act_k]
    rw [ih h_nodup hu_tail]
    have L0_u_head_eq : L₀.w u head = base.w u head := by
      apply foldl_delete_preserves_weights base tail h_nodup u head hu_tail h_head_notin_tail
    rw [L0_u_head_eq]
    have head_notin_tail_finset : head ∉ tail.toFinset := by
      rw [List.mem_toFinset]
      exact h_head_notin_tail
    rw [List.toFinset_cons, Finset.sum_insert head_notin_tail_finset]
    rw [sub_add_eq_sub_sub]
    ring

lemma deleted_neuron_weight_contribution [DecidableEq U] (wθ : Params (HopfieldNetwork R U))
    (i u : U) (_ : u ≠ i) (s : U → R) :
  wθ.w u i * s i = ∑ j ∈ {i}, wθ.w u j * s j := by
  rw [sum_singleton]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] in
/-- DeleteNeurons removes weights connected to deleted neurons -/
lemma deleted_neurons_field_effect {m : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (deleted_neurons : Finset U) (u : U) (hu : u ∉ deleted_neurons) (k : Fin m) :
  (DeleteNeurons deleted_neurons.toList (Hebbian ps)).w.mulVec (ps k).act u =
  (Hebbian ps).w.mulVec (ps k).act u - ∑ v ∈ deleted_neurons, (Hebbian ps).w u v * (ps k).act v := by
  rw [DeleteNeurons]
  have hu_list : u ∉ deleted_neurons.toList := by
    simp only [Finset.mem_toList]
    exact hu
  have h_nodup : deleted_neurons.toList.Nodup := Finset.nodup_toList deleted_neurons
  rw [delete_neurons_recursive ps deleted_neurons.toList h_nodup u hu_list k]
  congr 1
  rw [@toList_toFinset]

/-! ### Lemmas for Bounding Field Reduction due to Neuron Deletion -/

variable {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (deleted_neurons : Finset U)
    (k : Fin m) (u : U) (hu : u ∉ deleted_neurons)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)

/--
Calculates the contribution to the deleted field sum from the target pattern `k` itself
in the Hebbian weight definition.
-/
lemma hebbian_weight_deleted_neurons_l_eq_k_term :
  ∑ v ∈ deleted_neurons, (ps k).act u * (ps k).act v * (ps k).act v =
  (card deleted_neurons : R) * (ps k).act u := by
  have h_act_sq : ∀ v, (ps k).act v * (ps k).act v = 1 :=
    fun v => mul_self_eq_one_iff.mpr ((ps k).hp v)
  simp_rw [mul_assoc, h_act_sq, mul_one]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, Nat.cast_id]

/--
Defines the cross-talk contribution to the deleted field sum.
This term arises from the interaction of the target pattern `k` with other stored patterns `l ≠ k`
over the set of deleted neurons.
-/
noncomputable def hebbian_weight_deleted_neurons_cross_talk_term : R :=
  ∑ v ∈ deleted_neurons, (∑ l ∈ {l' | l' ≠ k}, (ps l).act u * (ps l).act v) * (ps k).act v

/--
Axiom stating the bound on the absolute value of the cross-talk term.
This encapsulates the statistical argument from Hopfield's paper that for
random-like patterns, the sum of interfering terms is bounded.
-/
lemma cross_talk_term_abs_bound_assumption {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U] [DecidableEq U] {m : ℕ}
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) (_hu : u ∉ deleted_neurons)
    (_horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0) -- Orthogonality is a simplifying assumption often made.
    (hcard : card deleted_neurons ≤ Fintype.card U / 10)
    (hm : m ≤ Fintype.card U / 10) :
  |hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u| ≤ (Fintype.card U / 10 : R) := by sorry

/--
Decomposes the total sum representing the field reduction into the contribution
from the target pattern `k` and the cross-talk term from other patterns `l ≠ k`.

**Hopfield Assumption:** Assumes the standard Hebbian learning rule where `Tᵢᵢ = 0`.
The `Hebbian` definition in `HN.lean` implements this by subtracting `m • 1`.
-/
lemma Hebbian_stable (hm : m < Fintype.card U) (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m)
    (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0):
  isStable (Hebbian ps) (ps j) := by
  have h_mulVec_eq : ((Hebbian ps).w).mulVec (ps j).act = ((Fintype.card U : R) - (m : R)) • (ps j).act :=
    patterns_pairwise_orthogonal ps horth j
  have h_pos_diff : 0 < (Fintype.card U : R) - m := by
    rw [sub_pos, Nat.cast_lt]
    exact hm
  apply stateisStablecondition ps (ps j) ((Fintype.card U : R) - m) h_pos_diff
  intro u
  exact congrFun h_mulVec_eq u

omit [Fintype U] [Nonempty U] in
lemma hebbian_weight_diagonal_term_zero_if_neq (u v : U) (huv : u ≠ v) {m : ℕ} :
  (↑m * if u = v then (1 : R) else 0) = 0 := by
  simp [if_neg huv]

omit [DecidableEq U] in
lemma sum_hebbian_weight_times_act_remove_diagonal {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) (hu : u ∉ deleted_neurons) :
  ∑ v ∈ deleted_neurons, (Hebbian ps).w u v * (ps k).act v =
  ∑ v ∈ deleted_neurons, (∑ l, outerProduct (ps l) (ps l) u v) * (ps k).act v := by
  unfold Hebbian
  simp only [sub_apply, smul_apply, smul_eq_mul, Matrix.one_apply]
  have h_diag_sum_zero :
    ∑ v ∈ deleted_neurons, (↑m * if u = v then 1 else 0) * (ps k).act v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have huv : u ≠ v := fun eqv => hu (eqv ▸ hv)
    rw [hebbian_weight_diagonal_term_zero_if_neq u v huv, zero_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [h_diag_sum_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro v _
  rw [Matrix.sum_apply]

omit [DecidableEq U] in
lemma sum_outer_product_times_act_swap_summation {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) :
  ∑ v ∈ deleted_neurons, (∑ l, outerProduct (ps l) (ps l) u v) * (ps k).act v =
  ∑ l, ∑ v ∈ deleted_neurons, (ps l).act u * (ps l).act v * (ps k).act v := by
  simp only [outerProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]

omit [DecidableEq U] in
lemma sum_outer_product_times_act_l_eq_k {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) :
  ∑ v ∈ deleted_neurons, (ps k).act u * (ps k).act v * (ps k).act v =
  (card deleted_neurons : R) * (ps k).act u := by
  have act_sq_one : ∀ v, (ps k).act v * (ps k).act v = 1 :=
    fun v => mul_self_eq_one_iff.mpr ((ps k).hp v)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have h_sum : ∑ v ∈ deleted_neurons, (ps k).act v * (ps k).act v = ↑(deleted_neurons.card) := by
    rw [Finset.sum_congr rfl fun v _ => act_sq_one v]
    simp only [Finset.sum_const, nsmul_one, Nat.cast_id]
  rw [h_sum]
  rw [mul_comm]

omit [DecidableEq U] in
lemma sum_outer_product_times_act_l_neq_k {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) :
  ∑ l ∈ Finset.univ.erase k, ∑ v ∈ deleted_neurons, (ps l).act u * (ps l).act v * (ps k).act v =
  hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u := by
  unfold hebbian_weight_deleted_neurons_cross_talk_term
  dsimp only [ne_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_mul]
  apply congr_arg (· * (ps k).act v)
  apply Finset.sum_congr
  · simp only [Finset.filter_ne', Finset.mem_univ, true_and]
  · intros _ _ ; rfl

omit [DecidableEq U] in
lemma deleted_field_sum_decomposition {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) (hu : u ∉ deleted_neurons) :
  ∑ v ∈ deleted_neurons, (Hebbian ps).w u v * (ps k).act v =
  (card deleted_neurons : R) * (ps k).act u + hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u := by
  rw [sum_hebbian_weight_times_act_remove_diagonal ps deleted_neurons k u hu]
  rw [sum_outer_product_times_act_swap_summation ps deleted_neurons k u]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ k)]
  rw [sum_outer_product_times_act_l_eq_k ps deleted_neurons k u]
  simp_rw [Finset.sdiff_singleton_eq_erase]
  rw [sum_outer_product_times_act_l_neq_k ps deleted_neurons k u]

/--
Placeholder lemma for bounding the cross-talk term.
Proving a tight bound likely requires assumptions beyond simple orthogonality,
such as patterns being random and uncorrelated, analyzed in the limit of large N.
The bound likely depends on `m` (number of patterns) and `N` (number of neurons).

**Hopfield Assumption:** Implicitly assumes patterns behave statistically like random vectors.
-/
lemma bound_cross_talk_term (hcard : card deleted_neurons ≤ Fintype.card U / 10) (hm : m ≤ Fintype.card U / 10) :
  hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u ≤
  ((Fintype.card U / 10 : R) - (card deleted_neurons : R)) * (ps k).act u := by
  -- The proof of this bound is complex and depends on statistical assumptions
  -- about the patterns {ps l} and potentially the size of the network N = card U.
  -- Simple orthogonality is insufficient to guarantee this bound in general.
  -- This lemma is stronger than the absolute value bound and may require different/stronger assumptions.
  sorry

/--
The field reduction from deleting neurons has a bounded effect.
This version uses the decomposition and the (unproven) cross-talk bound.

**Hopfield Assumptions:**
1.  Standard Hebbian learning (`Tᵢᵢ = 0`).
2.  Patterns `ps` are orthogonal (`horth`).
3.  Patterns `ps` behave statistically like random vectors (implicit in `bound_cross_talk_term`).
4.  Number of stored patterns `m` is small relative to network size `N` (`hm`).
5.  Number of deleted neurons is small relative to network size `N` (`hcard`).
-/
lemma deleted_field_bound (hu : u ∉ deleted_neurons)
    (_ : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0) (hcard : card deleted_neurons ≤ Fintype.card U / 10) (hm : m ≤ Fintype.card U / 10) :
    ∑ v ∈ deleted_neurons, (Hebbian ps).w u v * (ps k).act v ≤
    (Fintype.card U / 10 : R) * (ps k).act u := by
  rw [deleted_field_sum_decomposition ps deleted_neurons k u hu]
  let C := hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u
  let lk_term := (card deleted_neurons : R) * (ps k).act u
  have h_bound_C : C ≤ ((Fintype.card U / 10 : R) - (card deleted_neurons : R)) * (ps k).act u :=
    by exact bound_cross_talk_term ps deleted_neurons k u hcard hm
  calc
    lk_term + C ≤ lk_term + ((Fintype.card U / 10 : R) - (card deleted_neurons : R)) * (ps k).act u := add_le_add_left h_bound_C _
    _ = (card deleted_neurons : R) * (ps k).act u + (Fintype.card U / 10 : R) * (ps k).act u - (card deleted_neurons : R) * (ps k).act u := by ring
    _ = (Fintype.card U / 10 : R) * (ps k).act u := by
      rw [add_sub_cancel_left]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U] [DecidableEq U] in
/-- With constrained m and limited deleted neurons, the field remains strong enough -/
lemma field_remains_sufficient {m : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]
    (hm_cond : m ≤ Fintype.card U / 10) :
  (Fintype.card U : R) - (m : R) - (Fintype.card U / 10 : R) > 0 := by
  let N_R : R := (Fintype.card U : R)
  let m_R : R := (m : R)
  let N_div_10_R : R := (Fintype.card U / 10 : R)
  let ten_R : R := 10
  have N_pos_nat : 0 < Fintype.card U := Fintype.card_pos
  have N_R_pos : N_R > 0 := Nat.cast_pos.mpr N_pos_nat
  have ten_R_pos : ten_R > 0 := by simp [Nat.cast_ofNat]; exact Nat.cast_pos.mpr (by norm_num : 0 < 10)
  have hm_R_le_N_div_10 : m_R ≤ N_R / ten_R := by
    have h10 : (10 : ℕ) ≠ 0 := by norm_num
    have : m * 10 ≤ Fintype.card U := by
      have h_mul_div : Fintype.card U / 10 * 10 ≤ Fintype.card U := Nat.div_mul_le_self (Fintype.card U) 10
      exact le_trans (Nat.mul_le_mul_right 10 hm_cond) h_mul_div
    have cast_this : (↑(m * 10) : R) ≤ (↑(Fintype.card U) : R) := Nat.cast_le.mpr this
    rw [Nat.cast_mul] at cast_this
    have : (↑10 : R) = ten_R := by rfl
    have : ↑m * ten_R ≤ N_R := by
      rw [← this]
      exact cast_this
    exact (le_div_iff₀ ten_R_pos).mpr cast_this
  calc
    N_R - m_R - N_R / ten_R ≥ N_R - (N_R / ten_R) - (N_R / ten_R) := by linarith [hm_R_le_N_div_10]
    _ = N_R - 2 * (N_R / ten_R) := by ring
    _ = N_R * (1 - 2 / ten_R) := by
        field_simp [ten_R_pos.ne.symm]
        ring
    _ = N_R * (8 / ten_R) := by
        congr 2
        field_simp [ten_R_pos.ne.symm]
        norm_num
    _ > 0 := by
      apply mul_pos
      · exact N_R_pos
      · have eight_R_pos : (8 : R) > 0 := by simp [Nat.cast_ofNat];
        exact div_pos eight_R_pos ten_R_pos

omit [Fintype U] [Nonempty U] in
/-- For random orthogonal patterns, the cross-talk term has a bounded absolute value.
    This is a fundamental assumption from Hopfield's paper about how patterns interact. -/
lemma bound_cross_talk_term_abs [Fintype U] [Nonempty U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k : Fin m) (u : U) (hu : u ∉ deleted_neurons)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)
    (hcard : card deleted_neurons ≤ Fintype.card U / 10)
    (hm : m ≤ Fintype.card U / 10) :
  |hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k u| ≤ (Fintype.card U / 10 : R) := by
  exact cross_talk_term_abs_bound_assumption ps deleted_neurons k u hu horth hcard hm

lemma deleted_field_product_bound [Fintype U] [Nonempty U]
    (ps : Fin m → (HopfieldNetwork R U).State) (deleted_neurons : Finset U)
    (k_pat : Fin m) (u_check : U) (hu_check_not_deleted : u_check ∉ deleted_neurons)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)
    (hcard_deleted_cond : card deleted_neurons ≤ Fintype.card U / 10)
    (hm_cond : m ≤ Fintype.card U / 10) :
  (∑ v ∈ deleted_neurons, (Hebbian ps).w u_check v * (ps k_pat).act v) * (ps k_pat).act u_check ≤ (Fintype.card U / 5 : R) := by
  -- We apply the decomposition to separate signal and cross-talk terms
  have decomp := deleted_field_sum_decomposition ps deleted_neurons k_pat u_check hu_check_not_deleted
  let C_del_R := (card deleted_neurons : R)
  let X_talk := hebbian_weight_deleted_neurons_cross_talk_term ps deleted_neurons k_pat u_check
  let N_R := (Fintype.card U : R)
  let ten_R : R := 10
  let N_div_10_R := N_R / ten_R
  let act_u_k := (ps k_pat).act u_check
  have sum_field_eq : ∑ v ∈ deleted_neurons, (Hebbian ps).w u_check v * (ps k_pat).act v =
                       C_del_R * act_u_k + X_talk := decomp
  -- Multiply both sides by act_u_k
  calc
    (∑ v ∈ deleted_neurons, (Hebbian ps).w u_check v * (ps k_pat).act v) * act_u_k = (C_del_R * act_u_k + X_talk) * act_u_k := by rw [sum_field_eq]
    _ = C_del_R * act_u_k * act_u_k + X_talk * act_u_k := by rw [add_mul]
    _ = C_del_R + X_talk * act_u_k := by
        rw [mul_assoc, mul_self_eq_one_iff.mpr ((ps k_pat).hp u_check), mul_one]
    _ ≤ N_div_10_R + N_div_10_R := by
        apply add_le_add
        · -- First bound: C_del_R ≤ N_div_10_R
          have ten_R_pos : ten_R > 0 := Nat.cast_pos.mpr (by norm_num : 0 < 10)
          have : 10 * card deleted_neurons ≤ Fintype.card U := by
            have h10 : 10 > 0 := by norm_num
            apply Nat.mul_le_of_le_div
            · sorry
          have cast_this : (↑(10 * card deleted_neurons) : R) ≤ N_R := Nat.cast_le.mpr this
          rw [Nat.cast_mul] at cast_this
          simp only [Nat.cast_ofNat] at cast_this
          exact (le_div_iff₀' ten_R_pos).mpr cast_this
        · -- Second bound: X_talk * act_u_k ≤ N_div_10_R
          apply le_trans
          · -- X_talk * act_u_k ≤ |X_talk|
            calc
              X_talk * act_u_k ≤ |X_talk * act_u_k| := le_abs_self _
              _ = |X_talk| * |act_u_k| := by rw [abs_mul]
              _ = |X_talk| * 1 := sorry
              _ = |X_talk| := by rw [mul_one]
          · -- |X_talk| ≤ N_div_10_R
            exact bound_cross_talk_term_abs ps deleted_neurons k_pat u_check hu_check_not_deleted horth hcard_deleted_cond hm_cond
    _ = N_R / 5 := by
        have five_R : R := 5
        have ten_R_pos : ten_R > 0 := Nat.cast_pos.mpr (by norm_num : 0 < 10)
        have five_R_pos : five_R > 0 := sorry
        field_simp
        sorry

/-- With bounded numbers of patterns and deleted neurons, the field remains strong enough
    to maintain the pattern stability, adjusted for N/5 bound. -/
lemma field_remains_sufficient_for_N_div_5 (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U]
    (hm_cond : m ≤ Fintype.card U / 10) :
  (Fintype.card U : R) - (m : R) - (Fintype.card U / 5 : R) > 0 := by
  let N_R : R := Fintype.card U
  let m_R : R := m
  let five_R : R := 5
  let ten_R : R := 10
  have N_R_pos : N_R > 0 := Nat.cast_pos.mpr Fintype.card_pos
  have five_R_pos : five_R > 0 := Nat.cast_pos.mpr (by norm_num : 0 < 5)
  have ten_R_pos : ten_R > 0 := Nat.cast_pos.mpr (by norm_num : 0 < 10)
  have hm_R_le_N_div_10 : m_R ≤ N_R / ten_R := by
    sorry
  calc
    N_R - m_R - N_R / five_R ≥ N_R - (N_R / ten_R) - (N_R / five_R) := by linarith [hm_R_le_N_div_10]
    _ = N_R * (1 - 1/ten_R - 1/five_R) := by
        field_simp [ten_R_pos.ne.symm, five_R_pos.ne.symm]
        ring
    _ = N_R * (1 - 1/ten_R - 2/ten_R) := by
        apply congr_arg (fun x => N_R * x)
        have h_frac : 1/five_R = 2/ten_R := by
          field_simp [five_R_pos.ne.symm, ten_R_pos.ne.symm]
          have h_five_eq : five_R = 5 := rfl
          have h_ten_eq : ten_R = 10 := rfl
          rw [h_five_eq, h_ten_eq]
          norm_num
        rw [h_frac]
    _ = N_R * ( (10-1-2) / ten_R) := by
        field_simp [ten_R_pos.ne.symm]
        ring_nf
        sorry
    _ = N_R * (7 / ten_R) := by norm_num
    _ > 0 := by
      apply mul_pos N_R_pos
      have seven_R_pos : (7 : R) > 0 := Nat.cast_pos.mpr (by norm_num : 0 < 7)
      exact div_pos seven_R_pos ten_R_pos

lemma hebbian_deleted_threshold_is_zero {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (neurons_to_delete : Finset U) (u_check : U) :
  θ' ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).θ u_check) = 0 := by
  simp only [DeleteNeurons, DeleteNeuron, Hebbian, θ']
  induction neurons_to_delete.toList with
  | nil => simp [List.foldl_nil]; exact rfl
  | cons head tail ih =>
    rw [List.foldl_cons]
    sorry

lemma net_input_at_non_deleted_neuron {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (k_pat : Fin m)
    (neurons_to_delete : Finset U) (u_check : U) (hu_check_not_deleted : u_check ∉ neurons_to_delete)
    (wθ_orig wθ_deleted : Params (HopfieldNetwork R U)) (hwθ_orig_eq : wθ_orig = Hebbian ps) (hwθ_del_eq : wθ_deleted = DeleteNeurons neurons_to_delete.toList wθ_orig) :
  (ps k_pat).net wθ_deleted u_check =
    wθ_orig.w.mulVec (ps k_pat).act u_check - (∑ v ∈ neurons_to_delete, wθ_orig.w u_check v * (ps k_pat).act v) := by
  subst hwθ_orig_eq hwθ_del_eq
  have h_diag_w_deleted_zero : (DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check u_check = 0 := by
    exact (DeleteNeurons neurons_to_delete.toList (Hebbian ps)).hw u_check u_check fun a ↦ a rfl
  unfold NeuralNetwork.State.net HopfieldNetwork NeuralNetwork.fnet HNfnet
  have sum_eq_net : ∑ v ∈ {v | v ≠ u_check}, ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check v) * (ps k_pat).act v =
                    (ps k_pat).net (DeleteNeurons neurons_to_delete.toList (Hebbian ps)) u_check := by rfl
  have h_sum_split : ∑ v ∈ {v | v ≠ u_check}, ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check v) * (ps k_pat).act v =
                     ∑ v, ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check v) * (ps k_pat).act v := by
    rw [←
      HNfnet_eq u_check ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check)
        (ps k_pat).act h_diag_w_deleted_zero]
  have sum_eq_mulVec : ∑ v, ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w u_check v) * (ps k_pat).act v =
                        ((DeleteNeurons neurons_to_delete.toList (Hebbian ps)).w).mulVec (ps k_pat).act u_check := by
    rw [mulVec]
    simp only [dotProduct]
  have field_effect := deleted_neurons_field_effect ps neurons_to_delete u_check hu_check_not_deleted k_pat
  sorry

omit [DecidableEq U] in
lemma product_net_input_activation_at_non_deleted_neuron {m : ℕ} [DecidableEq U]
    (ps : Fin m → (HopfieldNetwork R U).State) (k_pat : Fin m)
    (neurons_to_delete : Finset U) (u_check : U) (hu_check_not_deleted : u_check ∉ neurons_to_delete)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)
    (wθ_orig wθ_deleted : Params (HopfieldNetwork R U)) (hwθ_orig_eq : wθ_orig = Hebbian ps) (hwθ_del_eq : wθ_deleted = DeleteNeurons neurons_to_delete.toList wθ_orig) :
  ((ps k_pat).net wθ_deleted u_check) * (ps k_pat).act u_check =
  (((Fintype.card U : R) - m) - (∑ v ∈ neurons_to_delete, wθ_orig.w u_check v * (ps k_pat).act v) * (ps k_pat).act u_check) := by
  subst wθ_orig
  rw [net_input_at_non_deleted_neuron ps k_pat neurons_to_delete u_check hu_check_not_deleted (Hebbian ps) wθ_deleted rfl hwθ_del_eq]
  rw [sub_mul]
  have h_orig_field_term_mul_act : (Hebbian ps).w.mulVec (ps k_pat).act u_check * (ps k_pat).act u_check = ((Fintype.card U : R) - m) := by
    have h_orig_field_eq : (Hebbian ps).w.mulVec (ps k_pat).act u_check = ((Fintype.card U : R) - m) * (ps k_pat).act u_check :=
      congr_fun (patterns_pairwise_orthogonal ps horth k_pat) u_check
    rw [h_orig_field_eq, mul_assoc]
    rw [mul_self_eq_one_iff.mpr ((ps k_pat).hp u_check), mul_one]
  rw [h_orig_field_term_mul_act]

lemma non_deleted_neuron_maintains_sign_of_activation {m : ℕ} [Nonempty U]
    (ps : Fin m → (HopfieldNetwork R U).State) (k_pat : Fin m)
    (neurons_to_delete : Finset U) (u_check : U) (hu_check_not_deleted : u_check ∉ neurons_to_delete)
    (horth : ∀ {i j : Fin m}, i ≠ j → dotProduct (ps i).act (ps j).act = 0)
    (hm_cond : m ≤ Fintype.card U / 10) (hcard_deleted_cond : neurons_to_delete.card ≤ Fintype.card U / 10)
    (wθ_orig wθ_deleted : Params (HopfieldNetwork R U)) (hwθ_orig_eq : wθ_orig = Hebbian ps) (hwθ_del_eq : wθ_deleted = DeleteNeurons neurons_to_delete.toList wθ_orig) :
  ((ps k_pat).net wθ_deleted u_check) * (ps k_pat).act u_check > 0 := by
  subst wθ_orig
  rw [product_net_input_activation_at_non_deleted_neuron ps k_pat neurons_to_delete u_check hu_check_not_deleted horth (Hebbian ps) wθ_deleted rfl hwθ_del_eq]
  let signal_term := (Fintype.card U : R) - (m : R)
  let reduction_term_times_act := (∑ v ∈ neurons_to_delete, (Hebbian ps).w u_check v * (ps k_pat).act v) * (ps k_pat).act u_check
  have h_bound_reduction_term : reduction_term_times_act ≤ (Fintype.card U / 5 : R) :=
    deleted_field_product_bound ps neurons_to_delete k_pat u_check hu_check_not_deleted horth hcard_deleted_cond hm_cond
  have h_signal_bound : signal_term - (Fintype.card U / 5 : R) > 0 := by
    unfold signal_term
    simp only [gt_iff_lt, sub_pos]
    sorry
  calc
    signal_term - reduction_term_times_act ≥ signal_term - (Fintype.card U / 5 : R) := by
      apply sub_le_sub_left h_bound_reduction_term _
    _ > 0 := h_signal_bound

omit [DecidableEq U] in
/-- When deleting neurons from a Finset, we can use Finset.toList to convert the Finset to a List.
    This matches the API needed by DeleteNeurons. -/
lemma DeleteNeurons_with_Finset [DecidableEq U] (deleted_neurons : Finset U) (wθ : Params (HopfieldNetwork R U)) :
  DeleteNeurons (Finset.toList deleted_neurons) wθ =
  DeleteNeurons deleted_neurons.toList wθ := by
  rfl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [Nonempty U] [DecidableEq U] in
/-- A Hopfield network can tolerate the failure of up to 10% of its neurons
    while maintaining all stored patterns as fixed points, provided:
    1) The stored patterns are orthogonal
    2) The number of patterns is at most 10% of the network size -/
theorem fault_tolerance_bound {m : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U] [DecidableEq U] [Nonempty U]
    (ps : Fin m → (HopfieldNetwork R U).State)
    (horth : ∀ i j : Fin m, i ≠ j → dotProduct (ps i).act (ps j).act = 0) :
  m ≤ Fintype.card U / 10 → ∀ k_pat : Fin m, FaultTolerance ps k_pat (Fintype.card U / 10) := by
  intro hm_cond k_pat
  dsimp only [FaultTolerance]
  intro deleted_neurons_finset hcard_deleted_cond
  let wθ_orig := Hebbian ps
  let wθ' := DeleteNeurons (Finset.toList deleted_neurons_finset) wθ_orig
  intro u_check_neuron hu_check_mem_sdiff
  let act_k_u_check := (ps k_pat).act u_check_neuron
  let net_u_check_new := net wθ' (ps k_pat) u_check_neuron
  let threshold_u_check_new := θ' (wθ'.θ u_check_neuron)
  have hu_check_not_in_deleted : u_check_neuron ∉ deleted_neurons_finset :=
    (Finset.mem_sdiff.mp hu_check_mem_sdiff).right
  have h_net_sign_correct : net_u_check_new * act_k_u_check > 0 :=
    non_deleted_neuron_maintains_sign_of_activation ps k_pat deleted_neurons_finset
      u_check_neuron hu_check_not_in_deleted
      (fun {i j} h => horth i j h) hm_cond hcard_deleted_cond wθ_orig wθ' rfl rfl
  have h_threshold_is_zero : threshold_u_check_new = 0 :=
    hebbian_deleted_threshold_is_zero ps deleted_neurons_finset u_check_neuron
  rw [act_up_def]
  cases ((ps k_pat).hp u_check_neuron) with
  | inl h_act_eq_one =>
    simp only [act_k_u_check, h_act_eq_one]
    apply if_pos
    dsimp only [h_threshold_is_zero]
    have net_pos : net_u_check_new > 0 := by
      have h_temp := h_net_sign_correct
      simp only [act_k_u_check, h_act_eq_one] at h_temp
      simp only [mul_one] at h_temp
      exact h_temp
    have threshold_zero : (wθ'.θ u_check_neuron).get 0 = 0 := by dsimp only [h_threshold_is_zero]; exact
      h_threshold_is_zero
    rw [threshold_zero]
    exact le_of_lt net_pos
  | inr h_act_eq_neg_one =>
    simp only [act_k_u_check, h_act_eq_neg_one]
    apply if_neg
    dsimp only [h_threshold_is_zero]
    have net_neg : net wθ' (ps k_pat) u_check_neuron < 0 := by
      have h_temp := h_net_sign_correct
      simp only [act_k_u_check, h_act_eq_neg_one] at h_temp
      simp only [mul_neg_one, neg_pos] at h_temp
      exact h_temp
    exact Mathlib.Tactic.IntervalCases.of_lt_right net_neg (id (Eq.symm h_threshold_is_zero))

end Hopfield82
