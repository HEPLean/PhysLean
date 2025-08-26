/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.TwoState
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.toCanonicalEnsemble
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.DetailedBalanceGen
import Mathlib.Probability.Kernel.Composition.Prod

/-! ### Concrete Hopfield Energy and Fintype Instances
-/



/-!
Reintroduce (and simplify) a `Matrix.quadraticForm` helper and the update lemma
used later in the Hopfield energy flip relation proof (removed upstream).
-/
namespace Matrix

open scoped Classical Finset Set BigOperators

variable {ι} [DecidableEq ι] [CommRing R]

/-- Decomposition of an updated vector as original plus a single–site bump. -/
lemma update_decomp (x : ι → R) (i : ι) (v : R) :
  Function.update x i v =
    fun j => x j + (if j = i then v - x i else 0) := by
  funext j; by_cases hji : j = i
  · subst hji; simp
  · simp [hji, Function.update_of_ne hji, add_comm]

/-- Auxiliary single–site perturbation (Kronecker bump). -/
def singleBump (i : ι) (δ : R) : ι → R := fun j => if j = i then δ else 0

lemma update_eq_add_bump (x : ι → R) (i : ι) (v : R) :
    Function.update x i v = (fun j => x j + singleBump i (v - x i) j) := by
  simp [singleBump, update_decomp]

variable [Fintype ι]

/-- Column-sum split: separate the i-th term from the rest (unordered finite type). -/
lemma sum_split_at
    (f : ι → R) (i : ι) :
  (∑ j, f j) = f i + ∑ j ∈ (Finset.univ.erase i), f j := by
  classical
  have : (Finset.univ : Finset ι) = {i} ∪ Finset.univ.erase i := by
    ext j; by_cases hji : j = i <;> simp [hji]
  have hDisj : Disjoint ({i} : Finset ι) (Finset.univ.erase i) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hj'
    have : j = i := by simpa using Finset.mem_singleton.mp hj
    simp [this] at hj'
  calc
    (∑ j, f j)
        = ∑ j ∈ ({i} ∪ Finset.univ.erase i), f j := by rw [← this]
    _ = (∑ j ∈ ({i} : Finset ι), f j) + ∑ j ∈ Finset.univ.erase i, f j := by
          simp [Finset.sum_union hDisj, add_comm, add_left_comm, add_assoc]
    _ = f i + ∑ j ∈ Finset.univ.erase i, f j := by simp

/-- Quadratic form xᵀ M x written via `mulVec`. -/
def quadraticForm (M : Matrix ι ι R) (x : ι → R) : R :=
  ∑ j, x j * (M.mulVec x) j

/-- Effect of a single-site bump on mulVec (only the i-th column contributes). -/
lemma mulVec_update_single
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
    ∀ j, (M.mulVec (Function.update x i v)) j
        = (M.mulVec x) j + M j i * (v - x i) := by
  classical
  intro j
  have hUpd : Function.update x i v = fun k => if k = i then v else x k := by
    funext k; by_cases hki : k = i
    · subst hki; simp
    · simp [Function.update_of_ne hki, hki]
  unfold Matrix.mulVec dotProduct
  have hSplitUpd :=
    sum_split_at (R:=R) (ι:=ι) (f:=fun k => M j k * (if k = i then v else x k)) i
  have hSplitOrig :=
    sum_split_at (R:=R) (ι:=ι) (f:=fun k => M j k * x k) i
  have hOthers :
      (∑ k ∈ Finset.univ.erase i, M j k * (if k = i then v else x k))
        = ∑ k ∈ Finset.univ.erase i, M j k * x k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rcases Finset.mem_erase.mp hk with ⟨hki, _⟩
    simp [hki]
  have hLeft :
      (∑ k, M j k * (Function.update x i v k))
        = M j i * v + ∑ k ∈ Finset.univ.erase i, M j k * x k := by
    rw [hUpd, hSplitUpd, if_pos rfl, hOthers]
  have hRightBase :
      (∑ k, M j k * x k)
        = M j i * x i + ∑ k ∈ Finset.univ.erase i, M j k * x k := by
    simp only [hSplitOrig]
  have hSplitv : M j i * v = M j i * x i + M j i * (v - x i) := by
    rw [@mul_sub]; rw [@add_sub_cancel]
  calc
    (∑ k, M j k * (Function.update x i v k))
        = M j i * v + ∑ k ∈ Finset.univ.erase i, M j k * x k := hLeft
    _ = (M j i * x i + M j i * (v - x i)) + ∑ k ∈ Finset.univ.erase i, M j k * x k := by
          rw [hSplitv]
    _ = (M j i * x i + ∑ k ∈ Finset.univ.erase i, M j k * x k) + M j i * (v - x i) := by
          ac_rfl
    _ = (∑ k, M j k * x k) + M j i * (v - x i) := by
          rw [hRightBase]

/- Raw single–site quadratic form update (no diagonal assumption).
Produces a δ-linear part plus a δ² * M i i remainder term.

  Q(update x i v) - Q x
    = (v - x i) * ((∑ j, x j * M j i) + (M.mulVec x) i)
      + (v - x i)^2 * M i i
-/
lemma quadraticForm_update_point
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) (j : ι) :
  let δ : R := v - x i
  (Function.update x i v) j * (M.mulVec (Function.update x i v)) j
      - x j * (M.mulVec x) j
    =
    δ * (x j * M j i + (if j = i then (M.mulVec x) i else 0))
      + (δ * δ) * (if j = i then M j i else 0) := by
  classical
  intro δ
  have hMv :
      (M.mulVec (Function.update x i v)) j =
        (M.mulVec x) j + M j i * (v - x i) := by
    simpa using
      (mulVec_update_single (M:=M) (x:=x) (i:=i) (v:=v) j : _)
  by_cases hji : j = i
  · have hUpd_i : (Function.update x i v) i = v := by simp
    have hMv_i :
        (M.mulVec (Function.update x i v)) i =
          (M.mulVec x) i + M i i * (v - x i) := by
      simpa [hji] using hMv
    have hOnSite :
        (v * (((M.mulVec x) i) + M i i * (v - x i)) - (x i) * ((M.mulVec x) i))
          =
        (v - x i) * ((x i) * M i i + (M.mulVec x) i)
          + (v - x i) * (v - x i) * M i i := by
      ring
    aesop
  · have hUpd_off : (Function.update x i v) j = x j := by
      simp [Function.update, hji]
    have hIf1 : (if j = i then (M.mulVec x) i else 0) = 0 := by
      simp [hji]
    have hIf2 : (if j = i then M j i else 0) = 0 := by
      simp [hji]
    have hOffSite :
        (x j) * (((M.mulVec x) j) + M j i * (v - x i))
          - (x j) * ((M.mulVec x) j)
          =
        (v - x i) * ((x j) * M j i) := by
      ring
    simpa [hMv, hUpd_off, hIf1, hIf2, δ] using hOffSite

/-- Core raw single–site quadratic form update (separated into a standalone lemma).
Produces a δ-linear part plus a δ² * M i i remainder term. -/
lemma quadraticForm_update_sum
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
    (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
      + (v - x i) * (v - x i) * M i i := by
  classical
  set δ : R := v - x i
  have hPoint :=
    quadraticForm_update_point (M:=M) (x:=x) (i:=i) (v:=v)
  have hDiff :
      quadraticForm M (Function.update x i v) - quadraticForm M x
        =
      ∑ j,
        ((Function.update x i v) j * (M.mulVec (Function.update x i v)) j
          - x j * (M.mulVec x) j) := by
    unfold quadraticForm
    simp [Finset.sum_sub_distrib]
  have hExpand :
      (∑ j,
        ((Function.update x i v) j * (M.mulVec (Function.update x i v)) j
          - x j * (M.mulVec x) j))
        =
      ∑ j, (δ * (x j * M j i + if j = i then (M.mulVec x) i else 0)
              + (δ * δ) * (if j = i then M j i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hPoint, δ]
  have hSplit :
      (∑ j, (δ * (x j * M j i + if j = i then (M.mulVec x) i else 0)
              + (δ * δ) * (if j = i then M j i else 0)))
        =
      (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
        +
      (∑ j, (δ * δ) * (if j = i then M j i else 0)) := by
    simp [Finset.sum_add_distrib]
  have hSum_if1 :
      (∑ j : ι, (if j = i then (M.mulVec x) i else 0))
        = (M.mulVec x) i := by
    classical
    have hfilter : (Finset.univ.filter (fun j : ι => j = i)) = {i} := by
      ext j; by_cases hji : j = i <;> simp [hji]
    calc
      (∑ j : ι, (if j = i then (M.mulVec x) i else 0))
          = ∑ j ∈ Finset.univ.filter (fun j => j = i), (M.mulVec x) i := by
              aesop
      _ = (M.mulVec x) i := by
              simp [hfilter]
  have hSum_if2 :
      (∑ j : ι, (if j = i then M j i else 0)) = M i i := by
    classical
    have hfilter : (Finset.univ.filter (fun j : ι => j = i)) = {i} := by
      ext j; by_cases hji : j = i <;> simp [hji]
    calc
      (∑ j : ι, (if j = i then M j i else 0))
          = ∑ j ∈ Finset.univ.filter (fun j => j = i), M j i := by
              aesop
      _ = M i i := by
              simp [hfilter]
  have hPart1 :
      (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
        =
      δ * ((∑ j, x j * M j i) + (M.mulVec x) i) := by
    have :
        (∑ j, δ * (x j * M j i + if j = i then (M.mulVec x) i else 0))
          = δ * ∑ j, (x j * M j i + if j = i then (M.mulVec x) i else 0) := by
          simp [Finset.mul_sum]
    simp [this, Finset.sum_add_distrib, hSum_if1, add_comm, add_left_comm, add_assoc]
  have hPart2 :
      (∑ j, (δ * δ) * (if j = i then M j i else 0))
        = (δ * δ) * M i i := by
    have :
        (∑ j, (δ * δ) * (if j = i then M j i else 0))
          = (δ * δ) * ∑ j, (if j = i then M j i else 0) := by
          simp [Finset.mul_sum]
    simp [this, hSum_if2]
  calc
    quadraticForm M (Function.update x i v) - quadraticForm M x
        = _ := hDiff
    _ = _ := hExpand
    _ = _ := hSplit
    _ = δ * ((∑ j, x j * M j i) + (M.mulVec x) i)
          + (δ * δ) * M i i := by
          aesop
    _ = (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
        + (v - x i) * (v - x i) * M i i := by
          simp [δ, mul_comm, mul_left_comm, mul_assoc]


/-- Raw single–site quadratic form update (no diagonal assumption).
Old name kept; proof now delegates to `quadraticForm_update_sum`. -/
lemma quadraticForm_update_raw
    (M : Matrix ι ι R) (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
    (v - x i) * ( (∑ j, x j * M j i) + (M.mulVec x) i )
      + (v - x i) * (v - x i) * M i i :=
  quadraticForm_update_sum (M:=M) (x:=x) (i:=i) (v:=v)

/-- Version with only the i-th diagonal entry zero. -/
lemma quadraticForm_update_single_index
    {M : Matrix ι ι R} (i : ι) (hii : M i i = 0)
    (x : ι → R) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
  (v - x i) *
    ( (M.mulVec x) i
      + ∑ j ∈ (Finset.univ.erase i), x j * M j i ) := by
  classical
  have hRaw := quadraticForm_update_raw (M:=M) (x:=x) (i:=i) (v:=v)
  have hDiag0 : (v - x i) * (v - x i) * M i i = 0 := by simp [hii]
  have h1 :
      quadraticForm M (Function.update x i v) - quadraticForm M x
        =
      (v - x i) * ((∑ j, x j * M j i) + (M.mulVec x) i) := by
    simpa [hDiag0, add_comm, add_left_comm, add_assoc] using hRaw
  have hSplit :
      (∑ j, x j * M j i)
        = x i * M i i + ∑ j ∈ (Finset.univ.erase i), x j * M j i := by
    have := sum_split_at (f:=fun j => x j * M j i) i
    simp [add_comm, add_left_comm, add_assoc]
  have hErase :
      (∑ j, x j * M j i)
        = ∑ j ∈ (Finset.univ.erase i), x j * M j i := by
    simp_rw [hSplit, hii]; ring_nf
  simp_rw [h1, hErase, add_comm]


/-- Original (stronger) version assuming all diagonal entries vanish (kept for backwards compatibility). -/
lemma quadraticForm_update_single
    {M : Matrix ι ι R} (hDiag : ∀ j, M j j = 0)
    (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    =
  (v - x i) *
    ( (M.mulVec x) i
      + ∑ j ∈ (Finset.univ.erase i), x j * M j i ) :=
  quadraticForm_update_single_index (M:=M) (x:=x) (i:=i) (v:=v) (hii:=hDiag i)
/--
Optimized symmetric / zero–diagonal update for the quadratic form.
This is the version used in the Hopfield flip energy relation.
-/
lemma quadratic_form_update_diag_zero
    {M : Matrix ι ι R} (hSymm : M.IsSymm) (hDiag : ∀ j, M j j = 0)
    (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (Function.update x i v) - quadraticForm M x
    = (v - x i) * 2 * (M.mulVec x) i := by
  classical
  have hBase := quadraticForm_update_single (R:=R) (M:=M) hDiag x i v
  have hSwap :
      ∑ j ∈ (Finset.univ.erase i), x j * M j i
        = ∑ j ∈ (Finset.univ.erase i), M i j * x j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [Matrix.IsSymm.apply hSymm, mul_comm]
  have hMulVec :
      (M.mulVec x) i = ∑ j ∈ (Finset.univ.erase i), M i j * x j := by
    unfold Matrix.mulVec dotProduct
    classical
    have : (Finset.univ : Finset ι) = {i} ∪ Finset.univ.erase i := by
      ext j; by_cases hj : j = i <;> simp [hj]
    rw [this, Finset.sum_union]; simp [Finset.disjoint_singleton_left, hDiag]
    rw [← this]
    simp
  simp_rw [hBase, hSwap, hMulVec]; simp [two_mul, add_comm, add_left_comm, add_assoc, mul_add,
        mul_comm, mul_left_comm, mul_assoc]

end Matrix

open Finset Matrix NeuralNetwork State TwoState
--variable [Fintype ι] [DecidableEq ι]  [CommRing R]


variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- We need these helper lemmas about updPos/updNeg which were not in the prompt's snippet but are essential.
namespace TwoState

variable {R U σ : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U]
variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]

@[simp]
lemma updPos_act_at_u (s : NN.State) (u : U) :
    (updPos (NN:=NN) s u).act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
  simp [updPos, Function.update_self]

lemma updPos_act_noteq (s : NN.State) (u v : U) (h : v ≠ u) :
    (updPos (NN:=NN) s u).act v = s.act v := by
  simp [updPos, Function.update_self h]
  aesop

@[simp]
lemma updNeg_act_at_u (s : NN.State) (u : U) :
    (updNeg (NN:=NN) s u).act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) := by
  simp [updNeg, Function.update_self]

lemma updNeg_act_noteq (s : NN.State) (u v : U) (h : v ≠ u) :
    (updNeg (NN:=NN) s u).act v = s.act v := by
  simp [updNeg, Function.update_self h]
  aesop

-- Also need strict inequalities for logisticProb for detailed balance ratios.
lemma logisticProb_pos (x : ℝ) : 0 < logisticProb x := by
  unfold logisticProb
  have hden : 0 < 1 + Real.exp (-x) := by
    have hx : 0 < Real.exp (-x) := Real.exp_pos _
    linarith
  simpa using (one_div_pos.mpr hden)

lemma logisticProb_lt_one (x : ℝ) : logisticProb x < 1 := by
  unfold logisticProb
  apply (div_lt_one (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _)))).mpr
  simp; exact Real.exp_pos _

/-- Symmetry: logisticProb (-x) = 1 - logisticProb x. -/
lemma logisticProb_neg (x : ℝ) : logisticProb (-x) = 1 - logisticProb x := by
  unfold logisticProb
  have h1 : 1 / (1 + Real.exp x) = Real.exp (-x) / (1 + Real.exp (-x)) := by
    have hden : (1 + Real.exp x) ≠ 0 :=
      (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _))).ne'
    calc
      1 / (1 + Real.exp x)
          = (1 * Real.exp (-x)) / ((1 + Real.exp x) * Real.exp (-x)) := by
              field_simp [hden]
      _ = Real.exp (-x) / (Real.exp (-x) + 1) := by
              simp [mul_add, add_comm, add_left_comm, add_assoc, Real.exp_neg, mul_comm]
              ring_nf; rw [mul_eq_mul_left_iff]; simp
      _ = Real.exp (-x) / (1 + Real.exp (-x)) := by simp [add_comm]
  have h2 : Real.exp (-x) / (1 + Real.exp (-x)) = 1 - 1 / (1 + Real.exp (-x)) := by
    have hden : (1 + Real.exp (-x)) ≠ 0 :=
      (add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (Real.exp_pos _))).ne'
    field_simp [hden]
  aesop

end TwoState

/-!
# Concrete Energy Specification for Hopfield Networks (SymmetricBinary)

This section defines the standard Hopfield energy function and proves it satisfies
the `EnergySpec'` requirements for the `SymmetricBinary` architecture.
We leverage `Matrix.quadraticForm` for an elegant definition and proof.
-/

namespace HopfieldEnergy

open Finset Matrix NeuralNetwork TwoState
open scoped Classical

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/--
The standard Hopfield energy function (Hamiltonian) for SymmetricBinary networks.
E(s) = -1/2 * sᵀ W s + θᵀ s
-/
noncomputable def hamiltonian
    (p : Params (SymmetricBinary R U)) (s : (SymmetricBinary R U).State) : R :=
  let quad : R := ∑ i : U, s.act i * (p.w.mulVec s.act i)
  let θ_vec := fun i : U => (p.θ i).get fin0
  (- (1/2 : R) * quad) + ∑ i : U, θ_vec i * s.act i

/--
Proof of the fundamental Flip Energy Relation for the SymmetricBinary network.
ΔE = E(s⁺) - E(s⁻) = -2 * Lᵤ.
This leverages Mathlib's `Matrix.quadratic_form_update_diag_zero`.
-/
lemma hamiltonian_flip_relation (p : Params (SymmetricBinary R U)) (s : (SymmetricBinary R U).State) (u : U) :
    let sPos := updPos (NN:=SymmetricBinary R U) s u
    let sNeg := updNeg (NN:=SymmetricBinary R U) s u
    let L := s.net p u - (p.θ u).get fin0
    (hamiltonian p sPos - hamiltonian p sNeg) = - (2 : R) * L := by
  intro sPos sNeg L
  unfold hamiltonian
  let θ_vec := fun i => (p.θ i).get fin0

  -- 1. Analyze the Quadratic Term Difference (ΔE_quad).
  have h_quad_diff :
    (- (1/2 : R) * Matrix.quadraticForm p.w sPos.act) - (- (1/2 : R) * Matrix.quadraticForm p.w sNeg.act) =
    - (2 : R) * (p.w.mulVec s.act u) := by

    rw [← mul_sub]
    -- We analyze Q(sPos) - Q(sNeg). sPos has 1 at u, sNeg has -1 at u.

    -- Express sPos as an update of sNeg.
    have h_sPos_from_sNeg : sPos.act = Function.update sNeg.act u 1 := by
      ext i
      by_cases hi : i = u
      · subst hi
        -- At site u, sPos.act u is σ_pos which is definitionally 1 for SymmetricBinary.
        simp_rw [sPos, sNeg, updPos, updNeg, Function.update]
        aesop
      · simp [sPos, sNeg, updPos, updNeg, Function.update, hi]
    rw [h_sPos_from_sNeg]
    -- Apply the identity for updating a quadratic form with W symmetric and W_uu=0.
    -- Q(update(x, k, v)) - Q(x) = (v - x_k) * 2 * (W x)_k.
    rw [Matrix.quadratic_form_update_diag_zero (p.hw'.1) (p.hw'.2)]
    -- Here v=1, x=sNeg.act, k=u. sNeg.act u = -1.
    have h_sNeg_u : sNeg.act u = -1 := updNeg_act_at_u s u
    rw [h_sNeg_u]
    -- (1 - (-1)) * 2 * (W sNeg.act)_u = 4 * (W sNeg.act)_u.
    simp only [sub_neg_eq_add, one_add_one_eq_two]
    ring_nf
    -- Relate (W sNeg.act)_u back to s. Since W_uu=0, the activation at u doesn't matter.
    have h_W_sNeg_eq_W_s : p.w.mulVec sNeg.act u = p.w.mulVec s.act u := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      by_cases h_eq : j = u
      · simp [h_eq, p.hw'.2 u]  -- W_uu = 0
      · rw [updNeg_act_noteq s u j h_eq]

    rw [h_W_sNeg_eq_W_s]
  -- 2. Linear term difference
  have h_linear_diff :
      dotProduct θ_vec sPos.act - dotProduct θ_vec sNeg.act
        = (2 : R) * θ_vec u := by
    rw [← dotProduct_sub]
    -- Only coordinate u differs (-1 → 1), so the difference vector is 2·e_u.
    have h_diff_vec :
        sPos.act - sNeg.act = Pi.single u (2 : R) := by
      ext v
      by_cases hv : v = u
      · subst hv
        -- At site u: 1 - (-1) = 2 (for SymmetricBinary)
        simp [sPos, sNeg, updPos, updNeg,
              TwoState.SymmetricBinary, instTwoStateSymmetricBinary,
              Pi.single, sub_eq_add_neg, one_add_one_eq_two]
      · -- Off site: unchanged, difference 0
        simp [sPos, sNeg, updPos, updNeg, Pi.single, hv, sub_eq_add_neg]
    rw [h_diff_vec, dotProduct_single]
    simp [mul_comm]

  -- 3. Combine the terms.
  erw [add_sub_add_comm, h_quad_diff, h_linear_diff]
  -- Relate (W s.act)_u to L = net(s) - θ_u. We need to show net(s) = (W s.act)_u.
  have h_net_eq_W_s : s.net p u = p.w.mulVec s.act u := by
    unfold State.net SymmetricBinary fnet Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro v _
    split_ifs with h_ne
    · aesop
    · -- Case v = u (since ¬ (v ≠ u)): the net integrand is 0; the mulVec term is W u u * s.act u = 0.
      have hv : v = u := by
        classical
        by_contra hvne
        exact h_ne hvne
      subst hv
      have hdiag : p.w v v = 0 := p.hw'.2 v
      simp [hdiag]

  rw [← h_net_eq_W_s]
  -- Goal: -2 * net + 2 * θ = -2 * (net - θ).
  ring

/-- The concrete Energy Specification for the SymmetricBinary Hopfield Network. -/
noncomputable def symmetricBinaryEnergySpec : EnergySpec' (SymmetricBinary R U) where
  E := hamiltonian
  localField := fun p s u => s.net p u - (p.θ u).get fin0
  localField_spec := by intros; rfl
  flip_energy_relation := by
    intro f p s u
    have h_rel := hamiltonian_flip_relation p s u
    have h_scale : scale (NN:=SymmetricBinary R U) f = f 2 := scale_binary f
    simp_rw [h_rel, map_mul, map_neg]
    rw [h_scale]

end HopfieldEnergy

/-!
# Fintype Instance for Real-valued Binary States

The bridge to `CanonicalEnsemble` requires `[Fintype NN.State]`. For `SymmetricBinary ℝ U`,
we must formally establish that the subtype restricted to {-1, 1} activations is finite.
-/

namespace SymmetricBinaryFintype
variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Helper type representing the finite set {-1, 1} in ℝ. -/
def BinarySetReal := {x : ℝ // x = 1 ∨ x = -1}

/-- Decidable equality inherited from `ℝ` (classical). -/
noncomputable instance : DecidableEq BinarySetReal := by
  classical
  infer_instance

noncomputable instance : Fintype BinarySetReal :=
  Fintype.ofList
    [⟨1, Or.inl rfl⟩, ⟨-1, Or.inr rfl⟩]
    (by
      intro x
      classical
      rcases x.property with h | h
      · simp_rw [← h]; exact List.mem_cons_self
      · simp_rw [← h]; exact List.mem_of_getLast? rfl)

/-- Equivalence between the State space of SymmetricBinary ℝ U and (U → BinarySetReal). -/
noncomputable def stateEquivBinarySet : (TwoState.SymmetricBinary ℝ U).State ≃ (U → BinarySetReal) where
  toFun s := fun u => ⟨s.act u, s.hp u⟩
  invFun f := {
    act := fun u => (f u).val,
    hp := fun u => (f u).property
  }
  left_inv s := by ext u; simp
  right_inv f := by ext u; simp

-- The required Fintype instance.
noncomputable instance : Fintype (TwoState.SymmetricBinary ℝ U).State :=
  Fintype.ofEquiv (U → BinarySetReal) stateEquivBinarySet.symm

end SymmetricBinaryFintype

/-!
# Detailed Balance and the Boltzmann Distribution

This section establishes that the Gibbs update kernel is reversible with respect to the
Boltzmann distribution derived from the associated Canonical Ensemble. This holds generically
for any exclusive two-state network with an EnergySpec'.
-/

namespace HopfieldBoltzmann

open CanonicalEnsemble ProbabilityTheory TwoState PMF
open scoped Classical

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))

variable (p : Params NN) (T : Temperature)

/-- The Canonical Ensemble obtained from params `p` (builds a local Hamiltonian instance from `spec`). -/
noncomputable def CEparams (p : Params NN) : CanonicalEnsemble NN.State :=
  let _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
    IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
  hopfieldCE (U:=U) (σ:=σ) NN p

/-- Boltzmann probability of state `s` at temperature `T`. -/
noncomputable def P (p : Params NN) (T : Temperature) (s : NN.State) : ℝ :=
  (CEparams (NN:=NN) (spec:=spec) p).probability T s

omit [Nonempty U] [Nonempty NN.State] in
@[simp] lemma energy_eq_spec (p : Params NN) (s : NN.State) :
    let _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
      IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
    IsHamiltonian.energy (NN:=NN) p s = spec.E p s := by
  rfl

open scoped ENNReal Temperature Constants CanonicalEnsemble

omit [Fintype U] [DecidableEq U] [Nonempty U] [TwoStateNeuralNetwork NN] [TwoStateExclusive NN] in
/-- General canonical-ensemble probability ratio identity (finite state case). -/
lemma CE_probability_ratio
    (𝓒 : CanonicalEnsemble NN.State) [𝓒.IsFinite] (T : Temperature)
    (s s' : NN.State) :
    𝓒.probability T s' / 𝓒.probability T s =
      Real.exp (-(T.β : ℝ) * (𝓒.energy s' - 𝓒.energy s)) := by
  classical
  unfold CanonicalEnsemble.probability
  set Z := 𝓒.mathematicalPartitionFunction T
  have hZpos := mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
  have hZne : Z ≠ 0 := hZpos.ne'
  have hcancel :
      (Real.exp (-(T.β : ℝ) * 𝓒.energy s') / Z) /
        (Real.exp (-(T.β : ℝ) * 𝓒.energy s) / Z)
        =
      Real.exp (-(T.β : ℝ) * 𝓒.energy s') /
        Real.exp (-(T.β : ℝ) * 𝓒.energy s) := by
    have hc :
        (Real.exp (-(T.β : ℝ) * 𝓒.energy s') * Z⁻¹) /
          (Real.exp (-(T.β : ℝ) * 𝓒.energy s) * Z⁻¹)
          =
        Real.exp (-(T.β : ℝ) * 𝓒.energy s') /
          Real.exp (-(T.β : ℝ) * 𝓒.energy s) := by
      have hZinv_ne : Z⁻¹ ≠ 0 := inv_ne_zero hZne
      simp; ring_nf; rw [mul_inv_cancel_right₀ hZinv_ne (Real.exp (-(↑T.β * 𝓒.energy s')))]
    simpa [div_eq_mul_inv] using hc
  simp [Z, hcancel]
  have hratio :
      Real.exp (-(T.β : ℝ) * 𝓒.energy s') /
        Real.exp (-(T.β : ℝ) * 𝓒.energy s)
        =
      Real.exp (-(T.β : ℝ) * 𝓒.energy s' - (-(T.β : ℝ) * 𝓒.energy s)) := by
    simpa using
      (Real.exp_sub (-(T.β : ℝ) * 𝓒.energy s')
                    (-(T.β : ℝ) * 𝓒.energy s)).symm
  have hexp :
      -(T.β : ℝ) * 𝓒.energy s' - (-(T.β : ℝ) * 𝓒.energy s)
        = -(T.β : ℝ) * (𝓒.energy s' - 𝓒.energy s) := by
    ring
  aesop

omit [Nonempty U] in
/-- Ratio of Boltzmann probabilities P(s')/P(s) = exp(-β(E(s')-E(s))). -/
lemma boltzmann_ratio (s s' : NN.State) :
    P (NN:=NN) (spec:=spec) p T s' / P (NN:=NN) (spec:=spec) p T s =
      Real.exp (-(T.β : ℝ) * (spec.E p s' - spec.E p s)) := by
  classical
  have _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
    IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
  set 𝓒 := CEparams (NN:=NN) (spec:=spec) p
  have instFin : 𝓒.IsFinite := by
    dsimp [𝓒, CEparams]  -- unfolds to `hopfieldCE`
    infer_instance
  have h := CE_probability_ratio (NN:=NN) (𝓒:=𝓒) (T:=T) s s'
  simpa [P, 𝓒,
        energy_eq_spec (NN:=NN) (spec:=spec) (p:=p) (s:=s),
        energy_eq_spec (NN:=NN) (spec:=spec) (p:=p) (s:=s'),
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

-- Define the transition probability K(s→s') in ℝ.
noncomputable def Kbm (u : U) (s s' : NN.State) : ℝ :=
  ((TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) s').toReal

-- Helper lemmas to evaluate K explicitly.

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
/-- Pointwise evaluation at `updPos` (ENNReal helper). -/
private lemma gibbsUpdate_apply_updPos
    (f : ℝ →+* ℝ) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN:=NN) f p T s u) (updPos (s:=s) (u:=u))
      = ENNReal.ofReal (probPos (NN:=NN) f p T s u) := by
  classical
  unfold gibbsUpdate
  set pPos : ℝ := probPos (NN:=NN) f p T s u
  set pPosE : ENNReal := ENNReal.ofReal pPos
  have h_le_real : pPos ≤ 1 := probPos_le_one (NN:=NN) f p T s u
  have h_le : pPosE ≤ 1 := by
    aesop
  have hne : updPos (NN:=NN) s u ≠ updNeg (NN:=NN) s u := by
    intro h
    have h' := congrArg (fun st => st.act u) h
    simp [updPos, updNeg] at h'
    exact TwoStateNeuralNetwork.h_pos_ne_neg (NN:=NN) h'
  simp [pPos, pPosE,
        PMF.bernoulli_bind_pure_apply_left_of_ne (α:=NN.State) h_le hne]

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
/-- Pointwise evaluation at `updNeg` (ENNReal helper). -/
private lemma gibbsUpdate_apply_updNeg
    (f : ℝ →+* ℝ) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN:=NN) f p T s u) (updNeg (s:=s) (u:=u))
      = ENNReal.ofReal (1 - probPos (NN:=NN) f p T s u) := by
  classical
  unfold gibbsUpdate
  set pPos : ℝ := probPos (NN:=NN) f p T s u
  set pPosE : ENNReal := ENNReal.ofReal pPos
  have h_le_real : pPos ≤ 1 := probPos_le_one (NN:=NN) f p T s u
  have h_le : pPosE ≤ 1 := by
    simpa [pPosE, ENNReal.ofReal_one] using h_le_real
  have h_nonneg : 0 ≤ pPos := probPos_nonneg (NN:=NN) f p T s u
  have hne : updPos (NN:=NN) s u ≠ updNeg (NN:=NN) s u := by
    intro h
    have h' := congrArg (fun st => st.act u) h
    simp [updPos, updNeg] at h'
    exact TwoStateNeuralNetwork.h_pos_ne_neg (NN:=NN) h'
  have h_eval :=
    PMF.bernoulli_bind_pure_apply_right_of_ne (α:=NN.State) h_le hne
  have hsub : ENNReal.ofReal (1 - pPos) = 1 - pPosE := by
    simp [pPosE, ENNReal.ofReal_one]
    ring_nf
    rw [ENNReal.sub_eq_sInf, ENNReal.ofReal_sub 1 h_nonneg,
      ENNReal.sub_eq_sInf, ENNReal.ofReal_one]
  simp [pPos, pPosE, h_eval, hsub]

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
lemma Kbm_apply_updPos (u : U) (s : NN.State) :
    Kbm NN p T u s (updPos (NN:=NN) s u) = TwoState.probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
  let f := RingHom.id ℝ
  unfold Kbm; rw [gibbsUpdate_apply_updPos NN f]
  exact ENNReal.toReal_ofReal (probPos_nonneg f p T s u)

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
lemma Kbm_apply_updNeg (u : U) (s : NN.State) :
    Kbm NN p T u s (updNeg (NN:=NN) s u) = 1 - TwoState.probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
  let f := RingHom.id ℝ
  unfold Kbm; rw [gibbsUpdate_apply_updNeg NN f]
  have h_nonneg : 0 ≤ 1 - probPos (NN:=NN) f p T s u := sub_nonneg.mpr (probPos_le_one f p T s u)
  exact ENNReal.toReal_ofReal h_nonneg

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
lemma Kbm_apply_other (u : U) (s s' : NN.State)
    (h_pos : s' ≠ updPos (NN:=NN) s u) (h_neg : s' ≠ updNeg (NN:=NN) s u) :
    Kbm NN p T u s s' = 0 := by
  unfold Kbm gibbsUpdate
  let f := RingHom.id ℝ
  let pPosE := ENNReal.ofReal (TwoState.probPos (NN:=NN) f p T s u)
  have h_le : pPosE ≤ 1 := by simp [pPosE, TwoState.probPos_le_one]
  have h_K := PMF.bernoulli_bind_pure_apply_other h_le h_pos h_neg
  simp [h_K]
  aesop

/-- Helper: (1 - logistic(x)) / logistic(x) = exp(-x). -/
lemma one_sub_logistic_div_logistic (x : ℝ) :
  (1 - logisticProb x) / logisticProb x = Real.exp (-x) := by
  have h_pos := logisticProb_pos x
  rw [div_eq_iff h_pos.ne']
  unfold logisticProb
  have h_den_pos : 0 < 1 + Real.exp (-x) := by apply add_pos_of_pos_of_nonneg zero_lt_one; exact (Real.exp_pos _).le
  field_simp [h_den_pos.ne']

end HopfieldBoltzmann
