/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.HyperchargeFlux
/-!

# Multisets of anomaly cancellation coefficents

In this module we construct the multisets of anomaly cancellation coefficents
given possible pairings of hypercharge fluxes and `U(1)` charges.

-/
namespace FTheory

namespace SU5U1
namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-!

## Auxillary results

Related to zips and projections of multisets.

-/

lemma zip_perm_orderedInsert (l : ℤ) : (r ls : List ℤ) → (h : r.length = (l :: ls).length) →
    ∃ (r' : List ℤ), r'.Perm r ∧ (r'.zip (l :: ls)).Perm (r.zip (ls.orderedInsert LE.le l))
  | rs, [] => by
    aesop
  | [], l2 :: ls => by
    aesop
  | r :: [], l2 :: ls => by
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
    · use r2 :: r1 :: rs
    · have ih := zip_perm_orderedInsert l (r1 :: rs) ls (by simp_all)
      obtain ⟨r', h1, h2⟩ := ih
      have h' : ((r2 :: r1 :: rs).zip (l2 :: List.orderedInsert LE.le l ls)).Perm
          ((r2, l2) :: (r'.zip (l :: ls))) := by
        simp only [List.zip_cons_cons, List.perm_cons]
        exact id (List.Perm.symm h2)
      have hn : ∃ r'' : List ℤ,
          r''.Perm (r2 :: r') ∧ (r''.zip (l :: l2 :: ls)).Perm
          ((r2, l2) :: (r'.zip (l :: ls))) := by
        induction r' with
        | nil => simp at h1
        | cons rx r' ih' =>
          use rx :: r2 :: r'
          constructor
          · exact List.Perm.swap r2 rx r'
          · simp
            exact List.Perm.swap (r2, l2) (rx, l) (r'.zip ls)
      obtain ⟨r'', h3, h4⟩ := hn
      use r''
      constructor
      · trans (r2 :: r')
        · exact h3
        · exact List.Perm.cons r2 h1
      · trans ((r2, l2) :: (r'.zip (l :: ls)))
        · exact h4
        · exact id (List.Perm.symm h')

lemma zip_perm_insertionSort : (r l3 : List ℤ) → (h : r.length = l3.length) →
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
      | nil => simp
      | cons rx r1 ih' =>
        -- r2 perm rx :: r1
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
    trans (List.map Prod.fst ((l1.zip l2)))
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

lemma mem_list_of_prod_fst_snd (S T : Multiset ℤ) (hlen : S.card = T.card)
    (l : List ℤ) (hTl : T = ↑l) (X : Multiset (ℤ × ℤ))
    (hS : X.map Prod.fst = S) (hT : X.map Prod.snd = T) :
    X ∈ S.lists.dedup.map (fun l2 => l2.zip l) := by
  simp only [Multiset.mem_map, Multiset.mem_dedup, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe]
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

## Multisets of anomaly coefficents due to pairings.

-/

open CodimensionOneConfig

/-- Given a multiset `N` corresponding to hypercharge fluxes and a multiset `Q`
  corresponding to `U(1)` charges both for five-bar matter, the multiset of possible
  anomaly cancellation coefficents formed by possible pairings of elements of `N`
  with elements of `Q`. -/
def fiveAnomalyFreeSet (I : CodimensionOneConfig) (N Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  ((hyperchargeFluxLists N).map
      (fun l => (l.zip (fiveChargeMultisetToList I Q) : Multiset (ℤ × ℤ)))).map
    fun N => ((N.map fun x => (x.2 * x.1)).sum,
      (N.map fun x => (x.2 * x.2 * x.1)).sum)

lemma quantaBarFiveMatter_NQ_mem (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map (fun x => (x.N, x.q)) ∈
    (hyperchargeFluxLists (𝓜.quantaBarFiveMatter.map QuantaBarFive.N)).map
    (fun l => (l.zip (fiveChargeMultisetToList I 𝓜.Q5) :
      Multiset (ℤ × ℤ))) := by
  rw [← 𝓜.hyperchargeFlux_lists_eq_hyperchargeFluxLists he h3 h3L]
  refine mem_list_of_prod_fst_snd (Multiset.map QuantaBarFive.N 𝓜.quantaBarFiveMatter)
    𝓜.Q5 (by simp)
      (fiveChargeMultisetToList I (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter)) (?_)
      (Multiset.map (fun x => (x.N, x.q)) 𝓜.quantaBarFiveMatter) (by simp) (by simp)
  symm
  refine coe_fiveChargeMultisetToList_of_all_mem I
    (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter) ?_
  intro s hs
  apply 𝓜.Q5_subset_allowedBarFiveCharges
  exact Multiset.mem_toFinset.mpr hs

lemma fiveAnomalyCoefficient_mem_fiveAnomalyFreeSet
    (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.fiveAnomalyCoefficient ∈ fiveAnomalyFreeSet I (𝓜.quantaBarFiveMatter.map QuantaBarFive.N)
      𝓜.Q5 := by
  rw [fiveAnomalyFreeSet]
  rw [Multiset.mem_map]
  use 𝓜.quantaBarFiveMatter.map (fun x => (x.N, x.q))
  constructor
  · exact 𝓜.quantaBarFiveMatter_NQ_mem he h3 h3L
  · rw [fiveAnomalyCoefficient]
    congr 1
    · simp
    · simp

/-- Given a multiset `N` corresponding to hypercharge fluxes and a multiset `Q`
  corresponding to `U(1)` charges both for 10d matter, the multiset of possible
  anomaly cancellation coefficents formed by possible pairings of elements of `N`
  with elements of `Q`. -/
def tenAnomalyFreeSet (I : CodimensionOneConfig) (N Q : Multiset ℤ) :
    Multiset (ℤ × ℤ) :=
  ((hyperchargeFluxListsTen N).map
      (fun l => (l.zip (tenChargeMultisetToList I Q) : Multiset (ℤ × ℤ)))).map
    fun N => ((N.map fun x => (x.2 * x.1)).sum,
      3 * (N.map fun x => (x.2 * x.2 * x.1)).sum)

lemma quantaTen_NQ_mem (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map (fun x => (x.N, x.q)) ∈
    (hyperchargeFluxListsTen (𝓜.quantaTen.map QuantaTen.N)).map
    (fun l => (l.zip (tenChargeMultisetToList I 𝓜.Q10) :
      Multiset (ℤ × ℤ))) := by
  rw [← 𝓜.hyperchargeFlux_lists_eq_hyperchargeFluxListsTen he h3]
  refine mem_list_of_prod_fst_snd (Multiset.map QuantaTen.N 𝓜.quantaTen)
    (𝓜.Q10) (by simp)
      (tenChargeMultisetToList I (Multiset.map QuantaTen.q 𝓜.quantaTen)) (?_)
      (Multiset.map (fun x => (x.N, x.q)) 𝓜.quantaTen) (by simp) (by simp)
  symm
  refine
    coe_tenChargeMultisetToList_of_all_mem I (Multiset.map QuantaTen.q 𝓜.quantaTen) ?_
  intro s hs
  apply 𝓜.Q10_subset_allowedTenCharges
  exact Multiset.mem_toFinset.mpr hs

lemma tenAnomalyCoefficient_mem_tenAnomalyFreeSet
    (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.tenAnomalyCoefficient ∈ tenAnomalyFreeSet I (𝓜.quantaTen.map QuantaTen.N) 𝓜.Q10 := by
  rw [tenAnomalyFreeSet]
  rw [Multiset.mem_map]
  use 𝓜.quantaTen.map (fun x => (x.N, x.q))
  constructor
  · exact 𝓜.quantaTen_NQ_mem he h3
  · rw [tenAnomalyCoefficient]
    congr 1
    · simp
    · simp

/-!

## With no-exotics constraints.

-/

/--
Given a multiset `Q` corresponding to `U(1)` charges for five-bar matter, the multiset of possible
anomaly cancellation coefficents formed by possible pairings of elements of `Q`
with valid multisets of hypercharge fluxes given constraints on there been no exotics in the
spectrum.
-/
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
    𝓜.fiveAnomalyCoefficient ∈ fiveAnomalyFreeSetCharge I 𝓜.Q5 := by
  have hN := 𝓜.quantaBarFiveMatter_N_mem he h3 h3L
  have hN2 := 𝓜.fiveAnomalyCoefficient_mem_fiveAnomalyFreeSet he h3 h3L
  rw [fiveAnomalyFreeSetCharge]
  have hcard : (Multiset.map QuantaBarFive.q 𝓜.quantaBarFiveMatter).card =
      (Multiset.map QuantaBarFive.N 𝓜.quantaBarFiveMatter).card := by
    simp
  rw [hcard]
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) = N at *
  fin_cases hN
  all_goals simp_all

/--
Given a multiset `Q` corresponding to `U(1)` charges for 10d matter, the multiset of possible
anomaly cancellation coefficents formed by possible pairings of elements of `Q`
with valid multisets of hypercharge fluxes given constraints on there been no exotics in the
spectrum.
-/
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
    𝓜.tenAnomalyCoefficient ∈ tenAnomalyFreeSetCharge I 𝓜.Q10 := by
  have hN := 𝓜.quantaTen_N_mem he h3
  have hN2 := 𝓜.tenAnomalyCoefficient_mem_tenAnomalyFreeSet he h3
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

/--
For a charges `qHd` and `qHu` and a multiset of `U(1)` charges `Q10` and `Q5`, the
  condition that the there exists choices of hypercharge fluxes for the 10d and 5d
  matter which obey the no-exotics conditions and such that the anomaly cancellation
  conditions are satisfied.
-/
def AnomalyFreeCharges (I : CodimensionOneConfig) (qHd qHu : ℤ) (Q10 Q5 : Multiset ℤ) :
    Prop :=
  (0, 0) ∈ ((tenAnomalyFreeSetCharge I Q10).product (fiveAnomalyFreeSetCharge I Q5)).map
    (fun x => (x.1 + x.2 - (qHu, qHu * qHu) + (qHd, qHd * qHd)))

instance (I : CodimensionOneConfig) (qHd qHu : ℤ) (Q10 Q5 : Multiset ℤ) :
    Decidable (AnomalyFreeCharges I qHd qHu Q10 Q5) :=
  Multiset.decidableMem _ _

lemma anomalyFreeCharges_of_anomalyFree (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) (hU1 : 𝓜.GaugeAnomalyU1MSSM)
    (hU1U1 : 𝓜.GaugeAnomalyU1YU1U1) :
    AnomalyFreeCharges I 𝓜.qHd 𝓜.qHu 𝓜.Q10 𝓜.Q5 := by
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
