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

/-- Given two multisets `S` and `T` of equal cardinality, `multiSetPairs S T` is the
  finset containing all `Multiset (ℤ × ℤ)` which project in the first element to `S`
  and the second element to `T`.

  This is defined in an executable way. -/
def multiSetPairs (S T : Multiset ℤ)  : Finset (Multiset (ℤ × ℤ)) :=
  let T'' := (S.sort LE.le).permutations.map
    (fun S => Multiset.ofList (List.zip S (T.sort LE.le)))
  T''.toFinset

def foldAppend (X : Finset (Multiset (ℤ × ℤ))) (S T : Multiset ℤ)
    (F : Finset (Multiset (ℤ × ℤ))) : Finset (Multiset (ℤ × ℤ)) :=
  ((X.product F).val.map fun x => (x.1 +  x.2)).toFinset

def multsetProd (S T : Multiset ℤ) : Finset (Multiset (ℤ × ℤ)) := by
  let S' : Finset (Multiset (ℤ × ℤ)) := ((S.product T).map fun x => {x}).toFinset
  let f' := foldAppend S' S T
  if S.card = 0 then
    exact ∅
  else
    exact foldAppend S' S T (foldAppend S' S T S')
def listPermProd (S T : List ℤ) : Finset (List (ℤ × ℤ)) :=
  (S.permutations.map (fun S => List.zip S T)).toFinset




#eval multsetProd {1, 2} {3, 4}

example : multsetProd {1, 2} {3, 4} = {{(2, 3), (1, 4)}, {(2, 4), (1, 3)}} := by



#eval multsetProd {1, 2, 3} {4,5,6, 7}
example :   (List.map (fun S => ↑(S.zip (Multiset.sort LE.le {4})))
        (Multiset.sort LE.le {1, 2, 3}).permutations).dedup.isPerm
      (List.insert {(2, 4)} (List.insert {(3, 4)} [{(1, 4)}])) := by
  decide

lemma mem_multiSetPairs_iff_mem_list {S T : Multiset ℤ} (X : Multiset (ℤ × ℤ)) :
    X ∈ multiSetPairs S T ↔ X ∈ (S.sort LE.le).permutations.map
      (fun S => Multiset.ofList (List.zip S (T.sort LE.le))) := by
  rw [multiSetPairs]
  simp

lemma mem_multiSetPairs_iff_exist_perm {S T : Multiset ℤ} (X : Multiset (ℤ × ℤ)) :
    X ∈ multiSetPairs S T ↔ ∃ (l : List ℤ), l.Perm (S.sort LE.le) ∧
      X = Multiset.ofList (List.zip l (T.sort LE.le)) := by
  rw [multiSetPairs]
  aesop

lemma mem_multiSetPairs_iff_exist_toList {S T : Multiset ℤ} (X : Multiset (ℤ × ℤ)) :
    X ∈ multiSetPairs S T ↔ ∃ (l : List ℤ), l.Perm (S.sort LE.le) ∧
      X.toList.Perm (List.zip l (T.sort LE.le)) := by
  rw [mem_multiSetPairs_iff_exist_perm]
  constructor
  · intro h
    obtain ⟨l, hp, rfl⟩ := h
    use l
    simp_all
    generalize (l.zip (Multiset.sort LE.le T)) = l
    refine List.perm_iff_count.mpr ?_
    intro a
    rw [← Multiset.coe_count]
    simp
  · intro h
    obtain ⟨l,  h1, h2⟩ := h
    use l
    simp_all
    refine Multiset.ext.mpr ?_
    intro a
    rw [List.perm_iff_count] at h2
    rw [Multiset.coe_count]
    rw [← h2 a]
    rw [← Multiset.coe_count]
    simp

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

lemma mem_multiSetPairs_iff_exist_toList_perm {S T : Multiset ℤ} (X : Multiset (ℤ × ℤ))
    (hlen : S.card = T.card) :
    X ∈ multiSetPairs S T ↔ ∃ (l l2 : List ℤ), l.Perm (S.sort LE.le) ∧ l2.Perm (T.sort LE.le) ∧
    X.toList.Perm (List.zip l l2) := by
  rw [mem_multiSetPairs_iff_exist_perm]
  constructor
  · intro h
    obtain ⟨l, hp, rfl⟩ := h
    use l, (T.sort LE.le)
    simp_all
    generalize (l.zip (Multiset.sort LE.le T)) = l
    refine List.perm_iff_count.mpr ?_
    intro a
    rw [← Multiset.coe_count]
    simp
  · intro h
    obtain ⟨l, l2, h1, h2, h3⟩ := h
    have hL1 := List.Perm.length_eq h1
    have hL2 := List.Perm.length_eq h2
    simp at hL1 hL2
    obtain ⟨r, h1, h2⟩ := zip_perm l l2 (Multiset.sort LE.le T) (by simp_all) (by omega)
    use r
    constructor
    · (expose_names; exact List.Perm.trans h1 h1_1)
    · rw [Multiset.coe_eq_coe.mpr (id (List.Perm.symm h2))]
      trans Multiset.ofList X.toList
      · simp
      exact Multiset.coe_eq_coe.mpr h3

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
  else if N = {-3, 1, 1, 1} then
    {[1, 1, -3, 1], [-3, 1, 1, 1], [1, -3, 1, 1], [1, 1, 1, -3]}
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
  else if N = {-1, -1, 0, 2} then
    {[-1, -1, 0, 2], [0, -1, -1, 2], [-1, 0, -1, 2], [2, -1, -1, 0], [-1, 2, -1, 0], [-1, -1, 2, 0],
    [2, -1, 0, -1],
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


lemma test :  ({-1, -1, -1, 1, 2} : Multiset ℤ).lists.dedup = {
    [1, -1, -1, -1, 2], [-1, 1, -1, -1, 2], [-1, -1, 1, -1, 2], [-1, -1, -1, 1, 2],
    [1, -1, -1, 2, -1], [-1, 1, -1, 2, -1], [-1, -1, 1, 2, -1], [-1, -1, -1, 2, 1],
    [1, -1, 2, -1, -1], [-1, 1, 2, -1, -1], [-1, -1, 2, 1, -1], [-1, -1, 2, -1, 1],
    [1, 2, -1, -1, -1], [-1, 2, 1, -1, -1], [-1, 2, -1, 1, -1], [-1, 2, -1, -1, 1],
    [2, 1, -1, -1, -1], [2, -1, 1, -1, -1], [2, -1, -1, 1, -1], [2,-1, -1, -1, 1]} := by
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.nodup_dedup _
  · decide
  · intro l
    constructor
    · intro h
      rw [Multiset.mem_dedup, Multiset.mem_lists_iff] at h
      rw [Multiset.quot_mk_to_coe] at h
      have hlength : l.length = 5 := by
        trans (Multiset.ofList l).card
        · simp
        rw [← h]
        simp
      match l with
      | [] =>  simp at h
      | q1 :: [] => simp at hlength
      | q1 :: q2 :: [] => simp at hlength
      | q1 :: q2 :: q3 :: [] => simp at hlength
      | q1 :: q2 :: q3 :: q4 :: [] => simp at hlength
      | q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: l => simp at hlength
      | q1 :: q2 :: q3 :: q4 :: q5 :: []  =>
      have hq1 : q1 ∈ ({-1, 1, 2} : Finset ℤ) := by
        have hl : q1 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← h] at hl
        simpa using hl
      have hq2 : q2 ∈ ({-1, 1, 2} : Finset ℤ) := by
        have hl : q2 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← h] at hl
        simpa using hl
      have hq3 : q3 ∈ ({-1, 1, 2} : Finset ℤ) := by
        have hl : q3 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← h] at hl
        simpa using hl
      have hq4 : q4 ∈ ({-1, 1, 2} : Finset ℤ) := by
        have hl : q4 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← h] at hl
        simpa using hl
      have hq5 : q5 ∈ ({-1, 1, 2} : Finset ℤ) := by
        have hl : q5 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← h] at hl
        simpa using hl
      clear hlength
      revert h
      revert q1; revert q2; revert q3; revert q4; revert q5
      decide
    · rw [Multiset.mem_dedup, Multiset.mem_lists_iff]
      revert l
      decide

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
      trans (Multiset.ofList l).card
      · simp
      rw [← hNl]
    by_cases hNcard : N.card = 5
    · match l with
      | [] => simp [hNcard] at hlen
      | q1 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: l => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 :: q5 :: []  =>
      have hq1 : q1 ∈ N := by
        have hl : q1 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq2 : q2 ∈ N.dedup := by
        have hl : q2 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq3 : q3 ∈ N.dedup := by
        have hl : q3 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq4 : q4 ∈ N.dedup := by
        have hl : q4 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq5 : q5 ∈ N.dedup := by
        have hl : q5 ∈ (Multiset.ofList [q1, q2, q3, q4, q5]) := by simp
        rw [← hNl] at hl
        simpa using hl
      clear hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4; revert q5
      revert N
      decide
    by_cases hNcard : N.card = 4
    · match l with
      | [] => simp [hNcard] at hlen
      | q1 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 :: q5 ::  l => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 :: []  =>
      have hq1 : q1 ∈ N := by
        have hl : q1 ∈ (Multiset.ofList [q1, q2, q3, q4]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq2 : q2 ∈ N.dedup := by
        have hl : q2 ∈ (Multiset.ofList [q1, q2, q3, q4]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq3 : q3 ∈ N.dedup := by
        have hl : q3 ∈ (Multiset.ofList [q1, q2, q3, q4]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq4 : q4 ∈ N.dedup := by
        have hl : q4 ∈ (Multiset.ofList [q1, q2, q3, q4]) := by simp
        rw [← hNl] at hl
        simpa using hl
      clear hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4;
      revert N
      decide
    by_cases hNcard : N.card = 3
    · match l with
      | [] => simp [hNcard] at hlen
      | q1 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: q4 ::  l => simp [hNcard] at hlen
      | q1 :: q2 :: q3 :: []  =>
      have hq1 : q1 ∈ N := by
        have hl : q1 ∈ (Multiset.ofList [q1, q2, q3]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq2 : q2 ∈ N.dedup := by
        have hl : q2 ∈ (Multiset.ofList [q1, q2, q3]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq3 : q3 ∈ N.dedup := by
        have hl : q3 ∈ (Multiset.ofList [q1, q2, q3]) := by simp
        rw [← hNl] at hl
        simpa using hl
      clear hlen
      revert hNl
      revert q1; revert q2; revert q3;
      revert N
      decide
    by_cases hNcard : N.card = 2
    · match l with
      | [] => simp [hNcard] at hlen
      | q1 :: [] => simp [hNcard] at hlen
      | q1 :: q2 :: q3 ::  l => simp [hNcard] at hlen
      | q1 :: q2  :: []  =>
      have hq1 : q1 ∈ N := by
        have hl : q1 ∈ (Multiset.ofList [q1, q2]) := by simp
        rw [← hNl] at hl
        simpa using hl
      have hq2 : q2 ∈ N.dedup := by
        have hl : q2 ∈ (Multiset.ofList [q1, q2]) := by simp
        rw [← hNl] at hl
        simpa using hl
      clear hlen
      revert hNl
      revert q1; revert q2;
      revert N
      decide
    by_cases hNcard : N.card = 1
    · match l with
      | [] => simp [hNcard] at hlen
      | q1 :: q2 ::  l => simp [hNcard] at hlen
      | q1   :: []  =>
      have hq1 : q1 ∈ N := by
        have hl : q1 ∈ (Multiset.ofList [q1]) := by simp
        rw [← hNl] at hl
        simpa using hl
      clear hlen
      revert hNl
      revert q1;
      revert N
      decide
    apply False.elim
    clear hlen hNl
    revert N
    decide
  · revert l
    revert N
    decide


def chargeMultisetToList (I : CodimensionOneConfig)
    (S : Multiset ℤ) : List ℤ :=
   let x := I S
end MatterContent

end SU5U1

end FTheory
