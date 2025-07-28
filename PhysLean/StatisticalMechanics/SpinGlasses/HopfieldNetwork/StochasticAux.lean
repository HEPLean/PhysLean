import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Core
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Exponential

/- Several helper lemmas to support proofs of correctness, such as:
Lemmas (`energy_decomposition`, `weight_symmetry`, `energy_sum_split`) connecting the local
parameters (weights, biases) to the global energy function. -/

open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
   [Fintype U] [Nonempty U]

/-- The probability of selecting a specific neuron in the uniform distribution is 1/|U| -/
lemma uniform_neuron_selection_prob (u : U) :
  let p := λ _ => (1 : ENNReal) / (Fintype.card U : ENNReal)
  let neuron_pmf := PMF.ofFintype p (by
    rw [Finset.sum_const, Finset.card_univ]
    rw [ENNReal.div_eq_inv_mul]
    simp only [mul_one]
    have h_card_ne_zero : (Fintype.card U : ENNReal) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Fintype.card_ne_zero
    have h_card_ne_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card U)
    rw [← ENNReal.mul_inv_cancel h_card_ne_zero h_card_ne_top]
    simp only [nsmul_eq_mul])
  neuron_pmf u = (1 : ENNReal) / (Fintype.card U : ENNReal) := by
  intro p neuron_pmf
  simp only [PMF.ofFintype_apply, one_div, neuron_pmf, p]

/-- Uniform neuron selection gives a valid PMF -/
lemma uniform_neuron_selection_prob_valid :
    let p := λ (_ : U) => (1 : ENNReal) / (Fintype.card U : ENNReal)
  ∑ a ∈ Finset.univ, p a = 1 := by
  intro p
  rw [Finset.sum_const, Finset.card_univ]
  have h_card_pos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr inferInstance
  have h_card_ne_zero : (Fintype.card U : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact ne_of_gt h_card_pos
  have h_card_top : (Fintype.card U : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card U)
  rw [ENNReal.div_eq_inv_mul]
  rw [nsmul_eq_mul]
  simp only [mul_one]
  rw [ENNReal.mul_inv_cancel h_card_ne_zero h_card_top]

variable [DecidableEq U] (wθ : Params (HopfieldNetwork R U))
  (s : (HopfieldNetwork R U).State)
/-- Decompose energy into weight component and bias component -/
@[simp]
lemma energy_decomposition :
  s.E wθ = s.Ew wθ + s.Eθ wθ := by
  rw [NeuralNetwork.State.E]
  --rw [← @add_neg_eq_iff_eq_add]; exact add_neg_eq_of_eq_add rfl

/-- Weight matrix is symmetric in a Hopfield network -/
lemma weight_symmetry (v1 v2 : U) :
  wθ.w v1 v2 = wθ.w v2 v1 := (congrFun (congrFun (id (wθ.hw').symm) v1) v2)

/-- Energy sum can be split into terms with u and terms without u -/
lemma energy_sum_split (u : U):
  ∑ v : U, ∑ v2 ∈ {v2 | v2 ≠ v}, wθ.w v v2 * s.act v * s.act v2 =
    (∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act u * s.act v2) +
    (∑ v ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v}, wθ.w v v2 * s.act v * s.act v2) := by
  rw [← sum_erase_add _ _ (mem_univ u)]
  simp only [ne_eq, mem_univ, sum_erase_eq_sub, sub_add_cancel, add_sub_cancel]

/-- When states differ at exactly one site, we can identify that site -/
@[simp]
lemma single_site_difference (s s' : (HopfieldNetwork R U).State)
  (h : s ≠ s' ∧ ∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∃! u : U, s.act u ≠ s'.act u := by
  obtain ⟨s_neq, hu_all⟩ := h
  obtain ⟨u, hu⟩ := hu_all
  have diff_at_u : s.act u ≠ s'.act u := by {
    by_contra h_eq
    have all_same : ∀ v, s.act v = s'.act v := by {
      intro v
      by_cases hv : v = u
      { rw [hv, h_eq]}
      { exact hu v hv }}
    have s_eq : s = s' := ext all_same
    exact s_neq s_eq}
  use u
  constructor
  { exact diff_at_u }
  { intros v h_diff
    by_contra h_v
    have eq_v : s.act v = s'.act v := by {
      by_cases hv : v = u
      { rw [hv]; exact hu u fun a ↦ h_diff (hu v h_v) }
      { exact hu v hv }}
    exact h_diff eq_v }

/-- States that are equal at all sites are equal -/
lemma state_equality_from_sites
  (s s' : (HopfieldNetwork R U).State)
  (h : ∀ u : U, s.act u = s'.act u) : s = s' := by
  apply NeuralNetwork.ext
  exact h

/-- Function to set a specific neuron state -/
def NN.State.updateNeuron (u : U) (val : R)
  (hval : (HopfieldNetwork R U).pact val) : (HopfieldNetwork R U).State :=
{ act := fun u' => if u' = u then val else s.act u',
  hp := by
    intro u'
    by_cases h : u' = u
    · simp only [h, ↓reduceIte]
      exact hval
    · simp only [h, ↓reduceIte]
      exact s.hp u' }

/-- The updateNeuron function only changes the specified neuron, leaving others unchanged -/
@[simp]
lemma updateNeuron_preserves
  (s : (HopfieldNetwork R U).State) (v w : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  w ≠ v → (NN.State.updateNeuron s v val hval).act w = s.act w := by
  intro h_neq
  unfold NN.State.updateNeuron
  exact if_neg h_neq

/-- For states differing at only one site, that site must be u -/
@[simp]
lemma single_site_difference_unique
  (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_diff : s ≠ s') :
  ∃! v : U, s.act v ≠ s'.act v := by
  use u
  constructor
  · by_contra h_eq
    have all_equal : ∀ v, s.act v = s'.act v := by
      intro v
      by_cases hv : v = u
      · rw [hv]
        exact h_eq
      · exact h v hv
    exact h_diff (ext all_equal)
  · intro v hv
    by_contra h_neq
    have v_diff_u : v ≠ u := by
      by_contra h_eq
      rw [h_eq] at hv
      contradiction
    exact hv (h v v_diff_u)

/-- Given a single-site difference, the destination state is
     an update of the source state -/
lemma single_site_is_update
  (s s' : (HopfieldNetwork R U).State) (u : U)
  (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
  apply NeuralNetwork.ext
  intro v
  by_cases hv : v = u
  · rw [hv]
    exact Eq.symm (if_pos rfl)
  · rw [← h v hv]
    exact Eq.symm (if_neg hv)

/-- When updating a neuron with a value that equals one of the
    standard values (1 or -1), the result equals the standard update -/
@[simp]
lemma update_neuron_equiv
  (s : (HopfieldNetwork R U).State) (u : U) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  val = 1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u 1 (Or.inl rfl) := by
  intro h_val
  apply NeuralNetwork.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)
  · exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)

/-- Updates with different activation values produce different states -/
@[simp]
lemma different_activation_different_state
  (s : (HopfieldNetwork R U).State) (u : U) :
  NN.State.updateNeuron s u 1 (Or.inl rfl) ≠
  NN.State.updateNeuron s u (-1) (Or.inr rfl) := by
  intro h_contra
  have h_values :
    (NN.State.updateNeuron s u 1 (Or.inl rfl)).act u =
    (NN.State.updateNeuron s u (-1) (Or.inr rfl)).act u := by
    congr
  unfold NN.State.updateNeuron at h_values
  simp at h_values
  have : (1 : R) ≠ -1 := by
    simp only [ne_eq]
    norm_num
  exact this h_values

/-- Two neuron updates at the same site are equal if and only if
    their new values are equal -/
lemma update_neuron_eq_iff
  (s : (HopfieldNetwork R U).State) (u : U) (val₁ val₂ : R)
  (hval₁ : (HopfieldNetwork R U).pact val₁) (hval₂ : (HopfieldNetwork R U).pact val₂) :
  NN.State.updateNeuron s u val₁ hval₁ = NN.State.updateNeuron s u val₂ hval₂ ↔ val₁ = val₂ := by
  constructor
  · intro h
    have h_act : (NN.State.updateNeuron s u val₁ hval₁).act u = (NN.State.updateNeuron s u val₂ hval₂).act u := by
      rw [h]
    unfold NN.State.updateNeuron at h_act
    simp at h_act
    exact h_act
  · intro h_val
    subst h_val
    apply NeuralNetwork.ext
    intro v
    by_cases hv : v = u
    · subst hv; unfold NN.State.updateNeuron; exact rfl
    · unfold NN.State.updateNeuron; exact rfl

/-- Determines when a boolean-indexed update equals a specific update -/
@[simp]
lemma bool_update_eq_iff
  (s : (HopfieldNetwork R U).State) (u : U) (b : Bool) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  (if b then NN.State.updateNeuron s u 1 (Or.inl rfl)
   else NN.State.updateNeuron s u (-1) (Or.inr rfl)) =
  NN.State.updateNeuron s u val hval ↔
  (b = true ∧ val = 1) ∨ (b = false ∧ val = -1) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, update_neuron_eq_iff,
      false_and, true_and, false_or]
    constructor
    · intro h
      exact id (Eq.symm h)
    · intro h_cases
      cases h_cases
      trivial
  · simp only [↓reduceIte, update_neuron_eq_iff, true_and, Bool.true_eq_false,
      false_and, or_false]
    constructor
    · intro h
      exact id (Eq.symm h)
    · intro h_cases
      cases h_cases
      ·exact rfl

/-- When filtering a PMF with binary support to states matching a given state's update,
    the result reduces to a singleton if the update site matches -/
lemma pmf_filter_update_neuron
  (s : (HopfieldNetwork R U).State) (u : U) (val : R)
  (hval : (HopfieldNetwork R U).pact val) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (Or.inr rfl)
  filter (fun b => f b = NN.State.updateNeuron s u val hval) univ =
    if val = 1 then {true} else
    if val = -1 then {false} else ∅ := by
  intro f
  by_cases h1 : val = 1
  · simp only [h1]
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    rw [@bool_update_eq_iff]
    simp only [and_true, ↓reduceIte, mem_singleton, or_iff_left_iff_imp, and_imp]
    cases b
    · simp only [Bool.false_eq_true, imp_false, forall_const]
      norm_num
    · simp only [Bool.true_eq_false, implies_true]
  · by_cases h2 : val = -1
    · simp only [h1, h2]
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      rw [@bool_update_eq_iff]
      simp only [and_true, ↓reduceIte]
      cases b
      · simp only [Bool.false_eq_true, false_and, or_true, true_iff]
        norm_num
      · simp only [true_and, Bool.true_eq_false, or_false]
        norm_num
    · simp only [h1, h2]
      ext b
      simp only [mem_filter, mem_univ, true_and]
      rw [@bool_update_eq_iff]
      simp only [h1, and_false, h2, or_self, ↓reduceIte, not_mem_empty]

/-- For a PMF over binary values mapped to states, the probability of a specific state
    equals the probability of its corresponding binary value -/
lemma pmf_map_binary_state
  (s : (HopfieldNetwork R U).State) (u : U) (b : Bool) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (Or.inr rfl)
  PMF.map f (PMF.ofFintype p h_sum) (f b) = p b := by
  intro f
  simp only [PMF.map_apply]
  have h_inj : ∀ b₁ b₂ : Bool, b₁ ≠ b₂ → f b₁ ≠ f b₂ := by
    intro b₁ b₂ hneq
    unfold f
    cases b₁ <;> cases b₂
    · contradiction
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq]
      apply Ne.symm
      exact different_activation_different_state s u
    · dsimp only [↓dreduceIte, Bool.false_eq_true, ne_eq]
      have h_values_diff : (1 : R) ≠ (-1 : R) := by
        simp only [ne_eq]
        norm_num
      exact (update_neuron_eq_iff s u 1 (-1)
        (Or.inl rfl) (Or.inr rfl)).not.mpr h_values_diff
    · contradiction
  have h_unique : ∀ b' : Bool, f b' = f b ↔ b' = b := by
    intro b'
    by_cases h : b' = b
    · constructor
      · intro _
        exact h
      · intro _
        rw [h]
    · have : f b' ≠ f b := h_inj b' b h
      constructor
      · intro h_eq
        contradiction
      · intro h_eq
        contradiction
  have h_filter : (∑' (b' : Bool), if f b = f b' then (PMF.ofFintype p h_sum) b' else 0) =
                 (PMF.ofFintype p h_sum) b := by
    rw [tsum_fintype]
    have h_iff : ∀ b' : Bool, f b = f b' ↔ b = b' := by
      intro b'
      constructor
      · intro h_eq
        by_contra h_neq
        have h_different : f b ≠ f b' := by
          apply h_inj
          exact h_neq
        contradiction
      · intro h_eq
        rw [h_eq]
    have h_eq : ∑ b' : Bool, ite (f b = f b') ((PMF.ofFintype p h_sum) b') 0 =
                ∑ b' : Bool, ite (b = b') ((PMF.ofFintype p h_sum) b') 0 := by
      apply Finset.sum_congr rfl
      intro b' _
      have hcond : (f b = f b') ↔ (b = b') := h_iff b'
      simp only [hcond]
    rw [h_eq]
    simp [h_eq, Finset.sum_ite_eq]
  rw [@tsum_bool]
  simp only [PMF.ofFintype_apply]
  cases b
  · have h_true_neq : f false ≠ f true := by
      apply h_inj
      simp only [ne_eq, Bool.false_eq_true, not_false_eq_true]
    simp only [h_true_neq, if_true, if_false, add_zero]
  · have h_false_neq : f true ≠ f false := by
      apply h_inj
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true]
    simp only [h_false_neq, if_true, if_false, zero_add]

/-- A specialized version of the previous lemma for the case where the state is an update with new_val = 1 -/
lemma pmf_map_update_one
  (s : (HopfieldNetwork R U).State) (u : U) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (Or.inr rfl)
  PMF.map f (PMF.ofFintype p h_sum) (NN.State.updateNeuron s u 1 (Or.inl rfl)) = p true := by
  intro f
  apply pmf_map_binary_state s u true p h_sum

/-- A specialized version for the case where the state is an update with new_val = -1 -/
lemma pmf_map_update_neg_one
  (s : (HopfieldNetwork R U).State) (u : U) (p : Bool → ENNReal) (h_sum : ∑ b, p b = 1) :
  let f : Bool → (HopfieldNetwork R U).State := λ b =>
    if b then NN.State.updateNeuron s u 1 (Or.inl rfl)
    else NN.State.updateNeuron s u (-1) (Or.inr rfl)
  PMF.map f (PMF.ofFintype p h_sum) (NN.State.updateNeuron s u (-1) (Or.inr rfl)) = p false := by
  intro f
  apply pmf_map_binary_state s u false p h_sum

/-- Expresses a ratio of exponentials in terms of the sigmoid function format.
-/
@[simp]
lemma exp_ratio_to_sigmoid (x : ℝ) :
  Real.exp x / (Real.exp x + Real.exp (-x)) = 1 / (1 + Real.exp (-2 * x)) := by
  have h_denom : Real.exp x + Real.exp (-x) = Real.exp x * (1 + Real.exp (-2 * x)) := by
    have rhs_expanded : Real.exp x * (1 + Real.exp (-2 * x)) =
         Real.exp x + Real.exp x * Real.exp (-2 * x) := by
      rw [mul_add, mul_one]
    have exp_identity : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr
      ring
    rw [rhs_expanded, exp_identity]
  rw [h_denom, div_mul_eq_div_div]
  have h_exp_ne_zero : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  field_simp

/-- Local field is the weighted sum of incoming activations -/
lemma local_field_eq_weighted_sum
  (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
  s.net wθ u = ∑ v ∈ univ.erase u, wθ.w u v * s.act v := by
  unfold NeuralNetwork.State.net
  unfold NeuralNetwork.fnet HopfieldNetwork
  simp only [ne_eq]
  have sum_filter_eq : ∑ v ∈ filter (fun v => v ≠ u) univ, wθ.w u v * s.act v =
                       ∑ v ∈ univ.erase u, wθ.w u v * s.act v := by
    apply Finset.sum_congr
    · ext v
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
    · intro v _
      simp_all only [mem_erase, ne_eq, mem_univ, and_true]
      --rw [@OrderedCommSemiring.mul_comm]
  exact sum_filter_eq

@[simp]
lemma gibbs_bool_to_state_map_positive
  (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  val = 1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u 1 (Or.inl rfl) := by
  intro h_val
  apply NeuralNetwork.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · rw [h_v]
    exact ite_congr rfl (fun a ↦ h_val) (congrFun rfl)
  · simp only [h_v, if_neg]
    exact rfl

@[simp]
lemma gibbs_bool_to_state_map_negative
  (s : (HopfieldNetwork R U).State) (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  val = -1 → NN.State.updateNeuron s u val hval =
    NN.State.updateNeuron s u (-1) (Or.inr rfl) := by
  intro h_val
  apply NeuralNetwork.ext
  intro v
  unfold NN.State.updateNeuron
  by_cases h_v : v = u
  · rw [h_v]
    dsimp only; exact congrFun (congrArg (ite (u = u)) h_val) (s.act u)
  · dsimp only [h_v]; exact congrFun (congrArg (ite (v = u)) h_val) (s.act v)

/-- When states differ at exactly one site, the later state can be expressed as
    an update of the first state at that site -/
lemma single_site_transition_as_update
  (s s' : (HopfieldNetwork R U).State) (u : U)
  (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
  apply NeuralNetwork.ext
  intro v
  by_cases hv : v = u
  · rw [hv]
    unfold NN.State.updateNeuron
    exact Eq.symm (if_pos rfl)
  · unfold NN.State.updateNeuron
    rw [← h v hv]
    exact Eq.symm (if_neg hv)

/-- When states differ at exactly one site, the later state can be expressed as
    an update of the first state at that site -/
@[simp]
lemma single_site_difference_as_update (s s' : (HopfieldNetwork R U).State) (u : U)
  (h_diff_at_u : s.act u ≠ s'.act u) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
  apply NeuralNetwork.ext
  intro v
  by_cases hv : v = u
  · rw [hv]
    unfold NN.State.updateNeuron
    simp only [if_pos rfl]
    have _ := h_diff_at_u
    exact rfl
  · unfold NN.State.updateNeuron
    simp only [if_neg hv]
    exact Eq.symm (h_same_elsewhere v hv)
