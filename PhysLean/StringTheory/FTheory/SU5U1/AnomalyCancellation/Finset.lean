/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.FiveBar
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Ten
/-!

# Finsets containing the anomaly coefficients

This file contains the construction of
a finiset which carries the anomaly coefficients for
a multiset of hypercharge fluxes and a multiset of hypercharges,
not necessarily paired.

-/
namespace FTheory

namespace SU5U1
namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-!

## Auxillary results

Related to zips and projections of multisets.

-/

lemma zip_perm_orderedInsert (l : ℤ) : (r ls : List ℤ) → (h : r.length = (l :: ls).length ) →
    ∃ (r' : List ℤ), r'.Perm r ∧ (r'.zip (l :: ls)).Perm (r.zip (ls.orderedInsert LE.le l))
  | rs, [] => by
    aesop
  | [], l2 :: ls => by
    aesop
  | r ::  [], l2 :: ls => by
    aesop
  | r :: r1 :: [], l2 :: ls => by
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, right_eq_add,
      List.length_eq_zero_iff, List.orderedInsert]
    intro h
    subst h
    simp only [List.orderedInsert]
    split_ifs
    · use [r, r1]
    · use [r1, r]
      constructor
      · exact List.Perm.swap r r1 []
      · simp
        exact List.Perm.swap (r, l2) (r1, l) []
  | r2 :: r1 :: rs, l2 :: ls => by
    intro h
    simp only [List.orderedInsert]
    split_ifs
    · use  r2 :: r1 :: rs
    · have ih := zip_perm_orderedInsert l (r1 :: rs) ls (by simp_all)
      obtain ⟨r', h1, h2⟩ := ih
      have h' : ((r2 :: r1 :: rs).zip (l2 :: List.orderedInsert LE.le l ls)).Perm
          ((r2, l2) :: (r'.zip (l :: ls))) := by
        simp only [List.zip_cons_cons, List.perm_cons]
        exact id (List.Perm.symm h2)
      have hn :  ∃ r'' : List ℤ,
          r''.Perm (r2 :: r') ∧ (r''.zip (l :: l2 :: ls)).Perm
          ((r2, l2) :: (r'.zip (l :: ls))) := by
        induction r' with
        | nil =>  simp at h1
        | cons rx r' ih' =>
          use rx :: r2 :: r'
          constructor
          · exact List.Perm.swap r2 rx r'
          · simp
            exact List.Perm.swap (r2, l2) (rx, l) (r'.zip ls)
      obtain ⟨r'', h3, h4⟩ := hn
      use  r''
      constructor
      · trans (r2 :: r')
        · exact h3
        · exact List.Perm.cons r2 h1
      · trans ((r2, l2) :: (r'.zip (l :: ls)))
        · exact h4
        · exact id (List.Perm.symm h')

lemma zip_perm_insertionSort : (r l3 : List ℤ) → (h : r.length = l3.length ) →
    ∃ (r' : List ℤ), r'.Perm r ∧ (r'.zip l3).Perm (r.zip (l3.insertionSort LE.le))
  | [], [] => by
    simp
  | [], l :: ls => by
    simp
  | r :: rs, [] => by
    simp
  | r :: rs, l :: ls => by
    intro h
    simp only [List.insertionSort]
    have h1 := zip_perm_orderedInsert l (r :: rs) (List.insertionSort LE.le ls) (by simp_all)
    obtain ⟨r1, h2, h3⟩ := h1
    have h2 : ∃ r2 : List ℤ, r2.Perm r1 ∧ (r2.zip (l :: ls)).Perm
        (r1.zip (l :: List.insertionSort LE.le ls)) := by
      induction r1 with
      | nil =>  simp
      | cons rx r1 ih' =>
        -- r2  perm rx :: r1
        have hlenrsr1 : r1.length = rs.length := by
          simpa using List.Perm.length_eq h2
        obtain ⟨r2, h4, h5⟩ := zip_perm_insertionSort r1 ls (by simp at h; omega)
        use rx :: r2
        constructor
        · exact List.Perm.cons rx h4
        · simp
          exact h5
    obtain ⟨r2, h4, h5⟩ := h2
    use r2
    constructor
    · exact List.Perm.trans h4 h2
    · exact List.Perm.trans h5 h3

lemma zip_perm (l1 l2 l3 : List ℤ) (hp : l2.Perm l3) (hl : l2.length = l1.length) :
    ∃ (r : List ℤ), r.Perm l1 ∧ (l1.zip l2).Perm (r.zip l3) := by
  have hl' : (l2.insertionSort LE.le) = (l3.insertionSort LE.le) := by
    apply List.eq_of_perm_of_sorted (r := LE.le)
    · trans l2
      · exact List.perm_insertionSort LE.le l2
      trans l3
      · exact hp
      · exact List.Perm.symm (List.perm_insertionSort LE.le l3)
    · exact List.sorted_insertionSort LE.le l2
    · exact List.sorted_insertionSort LE.le l3
  have h1 : ((l1.zip l2).insertionSort (fun x y => x.2 ≤ y.2)).unzip.1.Perm l1 := by
    simp only [List.unzip_fst]
    trans  (List.map Prod.fst ( (l1.zip l2)))
    · refine List.Perm.map Prod.fst ?_
      exact List.perm_insertionSort (fun x y => x.2 ≤ y.2) (l1.zip l2)
    · rw [← List.unzip_fst]
      rw [List.unzip_zip]
      (expose_names; exact id (Eq.symm hl))
  have h2 : ((l1.zip l2).insertionSort (fun x y => x.2 ≤ y.2)).unzip.2 =
      l2.insertionSort LE.le := by
    simp only [List.unzip_snd]
    have h1 := List.map_insertionSort (r := (fun x y => x.2 ≤ y.2)) (s := LE.le) Prod.snd
      (l1.zip l2) (by aesop)
    rw [h1]
    rw [← List.unzip_snd]
    rw [List.unzip_zip]
    (expose_names; exact id (Eq.symm hl))
  have h3 : ∃ (r : List ℤ), l1.Perm r ∧ (l1.zip l2).Perm (r.zip (l3.insertionSort LE.le)) := by
    use ((l1.zip l2).insertionSort (fun x y => x.2 ≤ y.2)).unzip.1
    rw [← hl', ← h2, List.zip_unzip]
    constructor
    · exact id (List.Perm.symm h1)
    · exact List.Perm.symm (List.perm_insertionSort (fun x y => x.2 ≤ y.2) (l1.zip l2))
  obtain ⟨r, h4, h5⟩ := h3
  have h4 : ∃ (r' : List ℤ), r'.Perm r ∧ (r'.zip l3).Perm (r.zip (l3.insertionSort LE.le)) := by
    have := List.Perm.length_eq hp
    have := List.Perm.length_eq h4
    exact zip_perm_insertionSort r l3 (by omega)
  obtain ⟨r2, h6, h7⟩ := h4
  use r2
  constructor
  · exact List.Perm.trans h6 (id (List.Perm.symm h4))
  · exact List.Perm.trans h5 (id (List.Perm.symm h7))

lemma mem_multiSetPairs_of_proj {S T : Multiset ℤ} (hlen : S.card = T.card)
    (X : Multiset (ℤ × ℤ)) :
    (∃ (l l2 : List ℤ), l.Perm (Multiset.sort LE.le S) ∧
    l2.Perm (Multiset.sort LE.le T) ∧ X.toList.Perm (l.zip l2)) ↔
    X.map Prod.fst = S ∧ X.map Prod.snd = T := by
  constructor
  · intro h
    obtain ⟨l, l2, h1, h2, h3⟩ := h
    constructor
    · trans Multiset.ofList (List.map Prod.fst X.toList)
      · rw [← Multiset.map_coe]
        simp
      trans Multiset.ofList S.toList
      swap
      · simp
      refine Multiset.coe_eq_coe.mpr ?_
      trans (List.map Prod.fst (l.zip l2))
      · apply List.Perm.map Prod.fst
        exact h3
      rw [← List.unzip_fst, List.unzip_zip]
      simp only
      trans (Multiset.sort LE.le S)
      · exact h1
      rw [← Multiset.coe_eq_coe]
      simp only [Multiset.sort_eq, Multiset.coe_toList]
      have hL1 := List.Perm.length_eq h1
      have hL2 := List.Perm.length_eq h2
      simp at hL1 hL2
      omega
    · trans Multiset.ofList (List.map Prod.snd X.toList)
      · rw [← Multiset.map_coe]
        simp
      trans Multiset.ofList T.toList
      swap
      · simp
      refine Multiset.coe_eq_coe.mpr ?_
      trans (List.map Prod.snd (l.zip l2))
      · apply List.Perm.map Prod.snd
        exact h3
      rw [← List.unzip_snd, List.unzip_zip]
      simp only
      trans (Multiset.sort LE.le T)
      · exact h2
      rw [← Multiset.coe_eq_coe]
      simp only [Multiset.sort_eq, Multiset.coe_toList]
      have hL1 := List.Perm.length_eq h1
      have hL2 := List.Perm.length_eq h2
      simp at hL1 hL2
      omega
  · intro h
    use (List.map Prod.fst X.toList), (List.map Prod.snd X.toList)
    constructor
    · rw [← Multiset.coe_eq_coe]
      simp only [Multiset.sort_eq]
      rw [← Multiset.map_coe]
      simpa using h.1
    constructor
    · rw [← Multiset.coe_eq_coe]
      simp only [Multiset.sort_eq]
      rw [← Multiset.map_coe]
      simpa using h.2
    · rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]

lemma mem_list_of_prod_fst_snd (S T : Multiset ℤ) (hlen : S.card = T.card) (l : List ℤ) (hTl : T = ↑l) (X : Multiset (ℤ × ℤ))
    (hS : X.map Prod.fst = S) (hT : X.map Prod.snd = T) :
    X ∈ S.lists.dedup.map (fun l2 => l2.zip l) := by
  simp
  have h1 := (mem_multiSetPairs_of_proj hlen X).mpr (by simp_all)
  obtain ⟨r1, r2, hr1, hr2, hrP⟩ := h1
  have hr2' : r2.Perm l := by
    trans (Multiset.sort LE.le T)
    · exact hr2
    rw [← @Multiset.coe_eq_coe, ← hTl]
    simp
  have hr1len : r1.length = S.card := by simp [List.Perm.length_eq hr1]
  have hr2len : r2.length = T.card := by simp [List.Perm.length_eq hr2]
  obtain ⟨j1, hjP, hjP2⟩ := zip_perm r1 r2 l hr2' (by omega)
  use j1
  constructor
  · simpa [← Multiset.coe_eq_coe] using (hjP.trans hr1).symm
  · simpa [← Multiset.coe_eq_coe] using (hrP.trans hjP2).symm

/-!

## Hypercharge flux lists

-/

-- The reason this is needed is that `S.lists` does not work well with decide.
-- #eval ([-1, -2, 1, 1, 1] : List ℤ).permutations.dedup
def hyperchargeFluxLists (N : Multiset ℤ) : Multiset (List ℤ) :=
  if N = {-1, -1, -1, 1, 2} then
     {[1, -1, -1, -1, 2], [-1, 1, -1, -1, 2], [-1, -1, 1, -1, 2], [-1, -1, -1, 1, 2],
    [1, -1, -1, 2, -1], [-1, 1, -1, 2, -1], [-1, -1, 1, 2, -1], [-1, -1, -1, 2, 1],
    [1, -1, 2, -1, -1], [-1, 1, 2, -1, -1], [-1, -1, 2, 1, -1], [-1, -1, 2, -1, 1],
    [1, 2, -1, -1, -1], [-1, 2, 1, -1, -1], [-1, 2, -1, 1, -1], [-1, 2, -1, -1, 1],
    [2, 1, -1, -1, -1], [2, -1, 1, -1, -1], [2, -1, -1, 1, -1], [2,-1, -1, -1, 1]}
  else if  N = {-1, -1, 0, 1, 1} then
    {[1, -1, -1, 0, 1], [-1, 1, -1, 0, 1], [-1, -1, 1, 0, 1], [-1, -1, 0, 1, 1], [1, -1, 0, -1, 1],
    [-1, 1, 0, -1, 1], [-1, 0, 1, -1, 1], [-1, 0, -1, 1, 1], [1, 0, -1, -1, 1], [0, 1, -1, -1, 1],
    [0, -1, 1, -1, 1], [0, -1, -1, 1, 1], [-1, 1, 1, 0, -1], [1, 1, -1, 0, -1], [1, -1, 1, 0, -1],
    [1, 1, 0, -1, -1], [1, -1, 0, 1, -1], [-1, 1, 0, 1, -1],  [-1, 0, 1, 1, -1], [1, 0, -1, 1, -1],
    [0, -1, 1, 1, -1], [1, 0, 1, -1, -1], [0, 1, 1, -1, -1], [0, 1, -1, 1, -1], [1, 1, -1, -1, 0],
    [1, -1, -1, 1, 0], [-1, -1, 1, 1, 0], [1, -1, 1, -1, 0], [-1, 1, 1, -1, 0], [-1, 1, -1, 1, 0]}
  else if N = {-1, -2, 1, 1, 1} then
    {[1, 1, 1, -2, -1], [-2, 1, 1, 1, -1], [1, 1, -2, 1, -1], [1, -2, 1, 1, -1], [-1, 1, 1, 1, -2],
    [1, -1, 1, 1, -2], [1, 1, 1, -1, -2], [1, 1, -1, 1, -2], [-1, 1, 1, -2, 1], [1, 1, -1, -2, 1],
    [1, -1, 1, -2, 1], [1, 1, -2, -1, 1], [1, -1, -2, 1, 1], [-1, 1, -2, 1, 1], [-1, -2, 1, 1, 1],
    [1, -2, -1, 1, 1], [-2, -1, 1, 1, 1], [1, -2, 1, -1, 1], [-2, 1, 1, -1, 1], [-2, 1, -1, 1, 1]}
  else if N = {-3, 1, 1, 1} then {[1, 1, -3, 1], [-3, 1, 1, 1], [1, -3, 1, 1], [1, 1, 1, -3]}
  else if N = {-2, -1, 1, 2} then
    {[-2, -1, 1, 2], [-1, -2, 1, 2], [1, -1, -2, 2], [-1, 1, -2, 2], [1, -2, -1, 2], [-2, 1, -1, 2],
    [2, 1, -1, -2], [1, 2, -1, -2], [1, -1, 2, -2], [2, -1, 1, -2], [-1, 2, 1, -2], [-1, 1, 2, -2],
    [2, -2, -1, 1], [-2, 2, -1, 1], [-2, -1, 2, 1], [2, -1, -2, 1], [-1, 2, -2, 1], [-1, -2, 2, 1],
    [2, -2, 1, -1], [-2, 2, 1, -1], [-2, 1, 2, -1], [2, 1, -2, -1], [1, 2, -2, -1], [1, -2, 2, -1]}
  else if N = {-2, 0, 1, 1} then
    {[1, 1, 0, -2], [1, 0, 1, -2], [0, 1, 1, -2], [1, -2, 0, 1], [-2, 1, 0, 1], [-2, 0, 1, 1],
    [1, 0, -2, 1], [0, 1, -2, 1], [0, -2, 1, 1], [-2, 1, 1, 0], [1, 1, -2, 0], [1, -2, 1, 0]}
  else if N = {-1, -1, -1, 3} then
    {[-1, -1, -1, 3], [3, -1, -1, -1], [-1, 3, -1, -1], [-1, -1, 3, -1]}
  else if N = {-1, -1, 0, 2} then {[-1, -1, 0, 2], [0, -1, -1, 2], [-1, 0, -1, 2], [2, -1, -1, 0],
    [-1, 2, -1, 0], [-1, -1, 2, 0], [2, -1, 0, -1],
    [-1, 2, 0, -1], [-1, 0, 2, -1], [2, 0, -1, -1], [0, 2, -1, -1], [0, -1, 2, -1]}
  else if N = {-1, -1, 1, 1} then {[1, -1, -1, 1], [-1, 1, -1, 1], [-1, -1, 1, 1], [-1, 1, 1, -1],
    [1, 1, -1, -1], [1, -1, 1, -1]}
  else if N = {0, 0, -1, 1}  then  {[0, 0, -1, 1], [-1, 0, 0, 1], [0, -1, 0, 1], [1, 0, 0, -1],
    [0, 1, 0, -1], [0, 0, 1, -1], [1, 0, -1, 0], [0, 1, -1, 0], [0, -1, 1, 0], [1, -1, 0, 0],
    [-1, 1, 0, 0], [-1, 0, 1, 0]}
  else if N = {-3, 1, 2} then {[-3, 1, 2], [1, -3, 2], [2, 1, -3], [1, 2, -3],
    [2, -3, 1], [-3, 2, 1]}
  else if N = {-2, -1, 3} then {[-2, -1, 3], [-1, -2, 3], [3, -1, -2], [-1, 3, -2], [3, -2, -1],
    [-2, 3, -1]}
  else if N = {-2, 0, 2} then {[-2, 0, 2], [0, -2, 2], [2, 0, -2], [0, 2, -2], [2, -2, 0],
    [-2, 2, 0]}
  else if N = {-2, 1, 1} then {[1, 1, -2], [1, -2, 1], [-2, 1, 1]}
  else if N = {-1, -1, 2} then {[-1, -1, 2], [2, -1, -1], [-1, 2, -1]}
  else if N = {-1, 0, 1} then {[-1, 0, 1], [0, -1, 1], [1, 0, -1], [0, 1, -1], [1, -1, 0],
    [-1, 1, 0]}
  else if N = {0, 0, 0} then {[0 ,0, 0]}
  else if N = {-3, 3} then {[-3, 3], [3, -3]}
  else if N = {-2, 2} then {[-2, 2], [2, -2]}
  else if N = {-1, 1} then {[-1, 1], [1, -1]}
  else if N = {0, 0} then {[0, 0]}
  else if N = {0} then {[0]}
  else ∅

lemma hyperchargeFlux_lists_eq_hyperchargeFluxLists (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    (𝓜.quantaBarFiveMatter.map QuantaBarFive.N).lists.dedup =
    hyperchargeFluxLists (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) := by
  have h2 := 𝓜.quantaBarFiveMatter_N_mem he h3 h3L
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) = N at *
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.nodup_dedup N.lists
  · revert N
    decide
  intro l
  rw [Multiset.mem_dedup, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe]
  constructor
  · intro hNl
    have hlen : l.length = N.card := by
      rw [← Multiset.coe_card, ← hNl]
    match l with
    | [] =>
      rw [List.length_nil] at hlen
      subst hNl
      apply False.elim
      revert h2
      decide
    | q1 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add] at hlen
      revert hNl; revert q1;  revert N
      decide
    | q1 :: q2 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2;
      revert N
      decide
    | q1 :: q2 :: q3 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      have hq4 : q4 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: q5 :: []  =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      have hq4 : q4 ∈ N.dedup := by simp [hNl]
      have hq5 : q5 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4; revert q5
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: l =>
      simp at hlen
      have hn : 6 ≤ N.card := by omega
      clear hlen hNl
      apply False.elim
      revert N
      decide
  · revert l
    revert N
    decide

-- {0, 0, 0}, {1, -1, 0}, {0, 0}, {-1, 1}, {0}
-- The reason this is needed is that `S.lists` does not work well with decide.
-- #eval ([-1, 1, 0] : List ℤ).permutations.dedup
def hyperchargeFluxListsTen (N : Multiset ℤ) : Multiset (List ℤ) :=
  if N = {0, 0, 0} then {[0, 0, 0]}
  else if  N = {1, -1, 0} then {[-1, 1, 0], [1, -1, 0], [0, 1, -1], [1, 0, -1],
    [0, -1, 1], [-1, 0, 1]}
  else if N = {0, 0} then {[0, 0]}
  else if N = {-1, 1} then {[-1, 1], [1, -1]}
  else if N = {0} then {[0]}
  else ∅


lemma hyperchargeFlux_lists_eq_hyperchargeFluxListsTen (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles)  :
    (𝓜.quantaTen.map QuantaBarFive.N).lists.dedup =
    hyperchargeFluxListsTen (𝓜.quantaTen.map QuantaBarFive.N) := by
  have h2 := 𝓜.quantaTen_N_mem he h3
  generalize (𝓜.quantaTen.map QuantaTen.N) = N at *
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.nodup_dedup N.lists
  · revert N
    decide
  intro l
  rw [Multiset.mem_dedup, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe]
  constructor
  · intro hNl
    have hlen : l.length = N.card := by
      rw [← Multiset.coe_card, ← hNl]
    match l with
    | [] =>
      rw [List.length_nil] at hlen
      subst hNl
      apply False.elim
      revert h2
      decide
    | q1 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add] at hlen
      revert hNl; revert q1;  revert N
      decide
    | q1 :: q2 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2;
      revert N
      decide
    | q1 :: q2 :: q3 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: l =>
      simp at hlen
      have hn : 4 ≤ N.card := by omega
      clear hlen hNl
      apply False.elim
      revert N
      decide
  · revert l
    revert N
    decide

/-!

## Charge multisets to lists

-/


def fiveChargeMultisetToList (I : CodimensionOneConfig) (S : Multiset ℤ) : List ℤ :=
  I.allowedBarFiveChargesList.flatMap (fun x => List.replicate (S.count x) x)

def tenChargeMultisetToList (I : CodimensionOneConfig) (S : Multiset ℤ) : List ℤ :=
  I.allowedTenChargesList.flatMap (fun x => List.replicate (S.count x) x)

lemma fiveChargeMultisetToList_mem_iff {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}:
    a ∈ fiveChargeMultisetToList I S ↔ (a ∈ S ∧ a ∈ I.allowedBarFiveCharges) := by
  simp [fiveChargeMultisetToList]
  aesop

lemma tenChargeMultisetToList_mem_iff {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}:
    a ∈ tenChargeMultisetToList I S ↔ (a ∈ S ∧ a ∈ I.allowedTenCharges) := by
  simp [tenChargeMultisetToList]
  aesop

lemma fiveChargeMultisetToList_count {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}
    (hmem : a ∈  I.allowedBarFiveCharges) :
    (fiveChargeMultisetToList I S).count a = S.count a := by
  by_cases hS : a ∈ S
  · have hmem : a ∈ (fiveChargeMultisetToList I S) := by
      rw [fiveChargeMultisetToList_mem_iff]
      exact ⟨hS, hmem⟩
    simp [fiveChargeMultisetToList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x S) x) =
        fun x => if a = x then Multiset.count x S else 0 := by
      funext x
      simp
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : List.count a I.allowedBarFiveChargesList = 1 := by
      refine List.count_eq_one_of_mem ?_ ?_
      exact CodimensionOneConfig.allowedBarFiveChargesList_nodup I
      rw [fiveChargeMultisetToList_mem_iff] at hmem
      simpa using hmem.2
    rw [hc]
    simp
    intro a' ha' hx
    simp [ha']
    omega
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [fiveChargeMultisetToList_mem_iff]
      simp_all

lemma tenChargeMultisetToList_count {I : CodimensionOneConfig} {S : Multiset ℤ} {a : ℤ}
    (hmem : a ∈  I.allowedTenCharges) :
    (tenChargeMultisetToList I S).count a = S.count a := by
  by_cases hS : a ∈ S
  · have hmem : a ∈ (tenChargeMultisetToList I S) := by
      rw [tenChargeMultisetToList_mem_iff]
      exact ⟨hS, hmem⟩
    simp [tenChargeMultisetToList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x S) x) =
        fun x => if a = x then Multiset.count x S else 0 := by
      funext x
      simp
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : List.count a I.allowedTenChargesList = 1 := by
      refine List.count_eq_one_of_mem ?_ ?_
      exact CodimensionOneConfig.allowedTenChargesList_nodup I
      rw [tenChargeMultisetToList_mem_iff] at hmem
      simpa using hmem.2
    rw [hc]
    simp
    intro a' ha' hx
    simp [ha']
    omega
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [tenChargeMultisetToList_mem_iff]
      simp_all

lemma coe_fiveChargeMultisetToList_of_all_mem (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedBarFiveCharges) :
    ↑(fiveChargeMultisetToList I S) = S := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ I.allowedBarFiveCharges
  · simp
    rw [fiveChargeMultisetToList_count ha]
  · rw [Multiset.count_eq_zero_of_not_mem, Multiset.count_eq_zero_of_not_mem]
    · aesop
    · simp [fiveChargeMultisetToList_mem_iff]
      aesop

lemma coe_tenChargeMultisetToList_of_all_mem (I : CodimensionOneConfig) (S : Multiset ℤ)
    (hs : ∀ s ∈ S, s ∈ I.allowedTenCharges) :
    ↑(tenChargeMultisetToList I S) = S := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ I.allowedTenCharges
  · simp
    rw [tenChargeMultisetToList_count ha]
  · rw [Multiset.count_eq_zero_of_not_mem, Multiset.count_eq_zero_of_not_mem]
    · aesop
    · simp [tenChargeMultisetToList_mem_iff]
      aesop

lemma quantaBarFiveMatter_NQ_mem (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map (fun x => (x.N, x.q)) ∈
    (hyperchargeFluxLists (𝓜.quantaBarFiveMatter.map QuantaBarFive.N)).map
    (fun l => (l.zip (fiveChargeMultisetToList I (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)) :
      Multiset (ℤ × ℤ))) := by
  rw [← 𝓜.hyperchargeFlux_lists_eq_hyperchargeFluxLists he h3 h3L]
  refine mem_list_of_prod_fst_snd (Multiset.map QuantaBarFive.N 𝓜.quantaBarFiveMatter)
    ((𝓜.quantaBarFiveMatter.map QuantaBarFive.q)) (by simp)
      (fiveChargeMultisetToList I (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter)) (?_)
      (Multiset.map (fun x => (x.N, x.q)) 𝓜.quantaBarFiveMatter) (by simp) (by simp)
  symm
  refine
    coe_fiveChargeMultisetToList_of_all_mem I (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter) ?_
  intro s hs
  apply 𝓜.quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges
  exact Multiset.mem_toFinset.mpr hs

lemma quantaTen_NQ_mem (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map (fun x => (x.N, x.q)) ∈
    (hyperchargeFluxListsTen (𝓜.quantaTen.map QuantaTen.N)).map
    (fun l => (l.zip (tenChargeMultisetToList I (𝓜.quantaTen.map QuantaTen.q)) :
      Multiset (ℤ × ℤ))) := by
  rw [← 𝓜.hyperchargeFlux_lists_eq_hyperchargeFluxListsTen he h3]
  refine mem_list_of_prod_fst_snd (Multiset.map QuantaTen.N 𝓜.quantaTen)
    ((𝓜.quantaTen.map QuantaTen.q)) (by simp)
      (tenChargeMultisetToList I (Multiset.map QuantaTen.q 𝓜.quantaTen)) (?_)
      (Multiset.map (fun x => (x.N, x.q)) 𝓜.quantaTen) (by simp) (by simp)
  symm
  refine
    coe_tenChargeMultisetToList_of_all_mem I (Multiset.map QuantaTen.q 𝓜.quantaTen) ?_
  intro s hs
  apply 𝓜.quantaTen_map_q_subset_allowedTenCharges
  exact Multiset.mem_toFinset.mpr hs

/-!

## Anomaly free sets

-/

def fiveAnomalyFreeSet (I : CodimensionOneConfig) (N Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  ((hyperchargeFluxLists N).map
      (fun l => (l.zip (fiveChargeMultisetToList I Q) : Multiset (ℤ × ℤ)))).map
    fun N => ((N.map fun x => (x.2 * x.1)).sum,
      (N.map fun x => (x.2 * x.2 * x.1)).sum)

lemma fiveAnomalyCoefficient_mem_fiveAnomalyFreeSet
    (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.fiveAnomalyCoefficient ∈ fiveAnomalyFreeSet I (𝓜.quantaBarFiveMatter.map QuantaBarFive.N)
      (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) := by
  rw [fiveAnomalyFreeSet]
  rw [Multiset.mem_map]
  use 𝓜.quantaBarFiveMatter.map (fun x => (x.N, x.q))
  constructor
  · exact 𝓜.quantaBarFiveMatter_NQ_mem he h3 h3L
  · rw [fiveAnomalyCoefficient]
    congr 1
    · simp
    · simp

def fiveAnomalyFreeSetCharge (I : CodimensionOneConfig) (Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  if Q.card = 5 then
    (fiveAnomalyFreeSet I {-1, -1, -1, 1, 2} Q ∪ fiveAnomalyFreeSet I {-1, -1, 0, 1, 1} Q ∪
      fiveAnomalyFreeSet I {-1, -2, 1, 1, 1} Q).dedup
  else if Q.card = 4 then
    (fiveAnomalyFreeSet I {-3, 1, 1, 1} Q ∪ fiveAnomalyFreeSet I {-2, -1, 1, 2} Q ∪
      fiveAnomalyFreeSet I {-2, 0, 1, 1} Q ∪ fiveAnomalyFreeSet I {-1, -1, -1, 3} Q ∪
      fiveAnomalyFreeSet I {-1, -1, 0, 2} Q ∪ fiveAnomalyFreeSet I {-1, -1, 1, 1} Q ∪
      fiveAnomalyFreeSet I {0, 0, -1, 1} Q).dedup
  else if Q.card = 3 then
    (fiveAnomalyFreeSet I {-3, 1, 2} Q ∪ fiveAnomalyFreeSet I {-2, -1, 3} Q ∪
      fiveAnomalyFreeSet I {-2, 0, 2} Q ∪ fiveAnomalyFreeSet I {-2, 1, 1} Q ∪
      fiveAnomalyFreeSet I {-1, -1, 2} Q ∪ fiveAnomalyFreeSet I {-1, 0, 1} Q ∪
      fiveAnomalyFreeSet I {0, 0, 0} Q).dedup
  else if Q.card = 2 then
    (fiveAnomalyFreeSet I {-3, 3} Q ∪ fiveAnomalyFreeSet I {-2, 2} Q ∪
      fiveAnomalyFreeSet I {-1, 1} Q ∪ fiveAnomalyFreeSet I {0, 0} Q).dedup
  else if Q.card = 1 then
    (fiveAnomalyFreeSet I {0} Q).dedup
  else ∅

lemma fiveAnomalyCoefficient_mem_fiveAnomalyFreeSetCharge
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.fiveAnomalyCoefficient ∈ fiveAnomalyFreeSetCharge I
      (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) := by
  have hN := 𝓜.quantaBarFiveMatter_N_mem he h3 h3L
  have  hN2 := 𝓜.fiveAnomalyCoefficient_mem_fiveAnomalyFreeSet he h3 h3L
  rw [fiveAnomalyFreeSetCharge]
  have hcard : (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter).card =
      (Multiset.map QuantaBarFive.N 𝓜.quantaBarFiveMatter).card := by
    simp
  rw [hcard]
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) = N at *
  fin_cases hN
  all_goals simp_all


def tenAnomalyFreeSet (I : CodimensionOneConfig) (N Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  ((hyperchargeFluxListsTen N).map
      (fun l => (l.zip (tenChargeMultisetToList I Q) : Multiset (ℤ × ℤ)))).map
    fun N => ((N.map fun x => (x.2 * x.1)).sum,
      3 * (N.map fun x => (x.2 * x.2 * x.1)).sum)

lemma tenAnomalyCoefficient_mem_tenAnomalyFreeSet
    (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.tenAnomalyCoefficient ∈ tenAnomalyFreeSet I (𝓜.quantaTen.map QuantaTen.N)
      (𝓜.quantaTen.map QuantaTen.q) := by
  rw [tenAnomalyFreeSet]
  rw [Multiset.mem_map]
  use 𝓜.quantaTen.map (fun x => (x.N, x.q))
  constructor
  · exact 𝓜.quantaTen_NQ_mem he h3
  · rw [tenAnomalyCoefficient]
    congr 1
    · simp
    · simp

def tenAnomalyFreeSetCharge (I : CodimensionOneConfig) (Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  if Q.card = 3 then
    (tenAnomalyFreeSet I {0, 0, 0} Q ∪ tenAnomalyFreeSet I {1, -1, 0} Q).dedup
  else if Q.card = 2 then
    (tenAnomalyFreeSet I {0, 0} Q ∪ tenAnomalyFreeSet I {-1, 1} Q).dedup
  else if Q.card = 1 then
    (tenAnomalyFreeSet I {0} Q).dedup
  else ∅

lemma tenAnomalyCoefficient_mem_tenAnomalyFreeSetCharge
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.tenAnomalyCoefficient ∈ tenAnomalyFreeSetCharge I
      (𝓜.quantaTen.map QuantaTen.q) := by
  have hN := 𝓜.quantaTen_N_mem he h3
  have  hN2 := 𝓜.tenAnomalyCoefficient_mem_tenAnomalyFreeSet he h3
  rw [tenAnomalyFreeSetCharge]
  have hcard : (Multiset.map QuantaTen.q 𝓜.quantaTen).card =
      (Multiset.map QuantaTen.N 𝓜.quantaTen).card := by
    simp
  rw [hcard]
  generalize (𝓜.quantaTen.map QuantaTen.N) = N at *
  fin_cases hN
  all_goals simp_all

/-!

## Anomaly free condition

-/

def AnomalyFreeCharges (I : CodimensionOneConfig) (qHd qHu : ℤ) (Q10 Q5 : Multiset ℤ) :
    Prop :=
  (0, 0) ∈ ((tenAnomalyFreeSetCharge I Q10).product (fiveAnomalyFreeSetCharge I Q5)).map
      (fun x => (x.1 + x.2  - (qHu, qHu * qHu) + (qHd, qHd * qHd)))

instance (I : CodimensionOneConfig) (qHd qHu : ℤ) (Q10 Q5 : Multiset ℤ) :
    Decidable (AnomalyFreeCharges I qHd qHu Q10 Q5) :=
  Multiset.decidableMem _ _

lemma anomalyFreeCharges_of_anomalyFree (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hU1 :  𝓜.GaugeAnomalyU1MSSM)
    (hU1U1 : 𝓜.GaugeAnomalyU1YU1U1) :
    AnomalyFreeCharges I 𝓜.qHd 𝓜.qHu (𝓜.quantaTen.map QuantaTen.q)
      (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) := by
  rw [AnomalyFreeCharges]
  simp only [Prod.mk_zero_zero, Multiset.mem_map, Multiset.mem_product,
     Prod.mk_eq_zero]
  rw [Prod.exists]
  use 𝓜.tenAnomalyCoefficient
  use 𝓜.fiveAnomalyCoefficient
  constructor
  · constructor
    · simpa using 𝓜.tenAnomalyCoefficient_mem_tenAnomalyFreeSetCharge he h3
    · simpa using 𝓜.fiveAnomalyCoefficient_mem_fiveAnomalyFreeSetCharge he h3 h3L
  · simp
    change _ = (0, 0)
    rw [← 𝓜.anomalyCoefficent_sum_of_gaugeAnomalyU1YU1U1_gaugeAnomalyU1YU1U1 hU1 hU1U1]
    ring

end MatterContent

end SU5U1

end FTheory
