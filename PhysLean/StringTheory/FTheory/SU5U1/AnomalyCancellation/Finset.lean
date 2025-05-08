/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.FiveBar
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
  let T'' := (S.sort LE.le).permutations.map (fun S => Multiset.ofList (List.zip S (T.sort LE.le)))
  T''.toFinset

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

lemma zip_perm (l1 l2 l3 : List ℤ)  (hp : l2.Perm l3) (hl : l2.length = l1.length):
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
    X ∈ multiSetPairs S T ↔ X.map Prod.fst = S ∧ X.map Prod.snd = T := by
  rw [mem_multiSetPairs_iff_exist_toList_perm _ hlen]
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

/-!

## fiveAnomalyCoefficient membership

-/

/-- Given a multiset `N` corresponding to hypercharge fluxes, and a multiset
  `Q` corresponding to charges for five bar matter, `anomalyCoefficientSet N Q`
  is the finset of all possible
  anomaly coefficents that can occur for this `N` and `Q`. -/
def fiveAnomalyCoefficientSet (N Q : Multiset ℤ ): Finset (ℤ × ℤ) :=
  ((multiSetPairs N Q).val.map
      fun Nq => ((Nq.map fun a => a.2 * a.1).sum,
      (Nq.map fun a => a.2 * a.2 * a.1).sum)).toFinset

lemma fiveAnomalyCoefficient_mem_anomalyCoefficientSet :
    𝓜.fiveAnomalyCoefficient ∈ fiveAnomalyCoefficientSet (𝓜.quantaBarFiveMatter.map QuantaBarFive.N)
      (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) := by
  simp [fiveAnomalyCoefficientSet]
  use 𝓜.quantaBarFiveMatter.map (fun a => (a.N, a.q))
  constructor
  · rw [mem_multiSetPairs_of_proj]
    · simp
    · simp
  · rw [fiveAnomalyCoefficient]
    simp

/-- Given a multiset `N` corresponding to hypercharge fluxes, and a multiset
  `Q` corresponding to charges for ten-dimension matter, `anomalyCoefficientSet N Q`
  is the finset of all possible
  anomaly coefficents that can occur for this `N` and `Q`. -/
def tenAnomalyCoefficientSet (N Q : Multiset ℤ ): Finset (ℤ × ℤ) :=
  ((multiSetPairs N Q).val.map
      fun Nq => ((Nq.map fun a => a.2 * a.1).sum,
     3 * (Nq.map fun a => a.2 * a.2 * a.1).sum)).toFinset

lemma tenAnomalyCoefficient_mem_anomalyCoefficientSet :
    𝓜.tenAnomalyCoefficient ∈ tenAnomalyCoefficientSet (𝓜.quantaTen.map QuantaTen.N)
      (𝓜.quantaTen.map QuantaTen.q) := by
  simp [tenAnomalyCoefficientSet]
  use 𝓜.quantaTen.map (fun a => (a.N, a.q))
  constructor
  · rw [mem_multiSetPairs_of_proj]
    · simp
    · simp
  · rw [tenAnomalyCoefficient]
    simp

/-!

## fiveAnomalyCoefficient membership for different cardinialities

-/

lemma fiveAnomalyCoefficient_mem_anomalyCoefficientSet_card_three
    (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hcard : 𝓜.quantaBarFiveMatter.card = 3):
    𝓜.fiveAnomalyCoefficient ∈
      fiveAnomalyCoefficientSet {-3, 1, 2} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {-2, -1, 3} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {-2, 0, 2} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {-2, 1, 1} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {-1, -1, 2} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {-1, 0, 1} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∪
      fiveAnomalyCoefficientSet {0, 0, 0} (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) := by
  have h1 :=  𝓜.fiveAnomalyCoefficient_mem_anomalyCoefficientSet
  have h2 := 𝓜.quantaBarFiveMatter_N_mem he h3 h3L
  have hcard' : (𝓜.quantaBarFiveMatter.map QuantaBarFive.N).card = 3 := by
    simpa using hcard
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) = N at *
  fin_cases h2
  all_goals
    simp at hcard'
  all_goals
    simp_all

end MatterContent

end SU5U1

end FTheory
