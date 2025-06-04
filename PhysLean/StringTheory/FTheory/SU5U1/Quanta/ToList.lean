/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.Basic
/-!

# Quanta into list

The types `FiveQuanta` and `TenQuanta` are defined as multisets, but
in some instances it is good to have them as lists. Usually turning
a multiset into a list is done using choice, and therefore is not computable.
However, in the cases when `NoExotics` and `HasNoZero` hold,
and all the charges in the `FiveQuanta` and `TenQuanta` correspond to
some `CodimensionOneConfig` then possible elements of
`FluxesFive` and `FluxesTen` are known. Thus we can use those
elements to construct a list of the fluxes from multisets, in a way which is computable.
This file provides the definitions and lemmas needed to do this.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-!

## `FiveQuanta` to lists

-/

namespace FiveQuanta

/-- The allowed elements of a `FiveQuanta` for which the underlying `FluxesFive` obeys
  `NoExotics` and `HasNoZero` and for which the charges are determined by
  a `CodimensionOneConfig`. -/
def allowedElems (I : CodimensionOneConfig) : List (ℤ × ℤ × ℤ) :=
  I.allowedBarFiveChargesList.flatMap fun x =>
    FluxesFive.allowedPairs.map (fun y => (x, y.1, y.2))

lemma mem_allowedElems_of_mem (F : FiveQuanta)
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F) : x ∈ allowedElems I := by
  simp [allowedElems]
  use x.1
  constructor
  · apply hc x.1
    simp [toCharges]
    use x.2.1, x.2.2
  · use x.2.1, x.2.2
    simp
    refine FluxesFive.mem_allowedPairs_of_mem_noExotics F.toFluxesFive hf x.2 ?_
    simp [toFluxesFive]
    use x.1

/-- A list from a `FiveQuanta` which when the underlying `FluxesFive` obeys
  `NoExotics` and `HasNoZero`, and the charges are determined by
  a `CodimensionOneConfig`, is a list whose underlying multiset is the
  `FiveQuanta`. Otherwise this list produces junk. -/
def toList (I : CodimensionOneConfig) (F : FiveQuanta) : List (ℤ × ℤ × ℤ) :=
  (allowedElems I).flatMap (fun x => List.replicate (F.count x) x)

lemma mem_allowedElems_of_mem_toList (I : CodimensionOneConfig) (F : FiveQuanta)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F.toList I) : x ∈ allowedElems I := by
  simp [toList] at h
  exact h.1

lemma snd_mem_allowedPairs_of_mem_toList (I : CodimensionOneConfig) (F : FiveQuanta)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F.toList I) : x.2 ∈ FluxesFive.allowedPairs := by
  have h1 := mem_allowedElems_of_mem_toList I F x h
  simp [allowedElems] at h1
  obtain ⟨x1, hx1, ⟨x2, x3, h2, rfl⟩⟩ := h1
  simpa using h2

lemma mem_toList_iff {I : CodimensionOneConfig} (F : FiveQuanta)
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges) {a : ℤ × ℤ × ℤ} :
    a ∈ F.toList I ↔ a ∈ F := by
  simp [toList]
  intro a_1
  obtain ⟨fst, snd⟩ := a
  exact mem_allowedElems_of_mem F hf hc (fst, snd) a_1

set_option maxRecDepth 2000 in
lemma toList_count {I : CodimensionOneConfig} {F : FiveQuanta}
    {a : ℤ × ℤ × ℤ}
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges)
    (hmema : a ∈ allowedElems I) :
    (F.toList I).count a = F.count a := by
  by_cases hS : a ∈ F
  · have hmem : a ∈ F.toList I := by
      rw [mem_toList_iff F hf hc]
      exact hS
    simp [toList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x F) x) =
        fun x => if a = x then Multiset.count x F else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : @List.count (ℤ × ℤ × ℤ) instBEqOfDecidableEq a (allowedElems I) = 1 := by
      revert hmema
      clear * -
      intro h
      revert a I
      decide
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    intro hn
    exact fun a_1 => ha' (id (Eq.symm hn))
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [mem_toList_iff F hf hc]
      simp_all

lemma coe_toList {I : CodimensionOneConfig} {F : FiveQuanta}
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges) :
    ↑(F.toList I) = F := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ allowedElems I
  · simp
    trans (F.toList I).count a
    · congr
      exact lawful_beq_subsingleton instBEqOfDecidableEq instBEqProd
    rw [toList_count hf hc ha]
  · rw [Multiset.count_eq_zero_of_not_mem, Multiset.count_eq_zero_of_not_mem]
    · by_contra hn
      exact ha (mem_allowedElems_of_mem F hf hc a hn)
    · by_contra hn
      rw [Multiset.mem_coe, mem_toList_iff F hf hc] at hn
      exact ha (mem_allowedElems_of_mem F hf hc a hn)

lemma toList_prod_fst_eq {I : CodimensionOneConfig} {F : FiveQuanta}
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges) :
    (F.toList I).map Prod.fst = I.fiveChargeMultisetToList F.toCharges := by
  simp [toList, CodimensionOneConfig.fiveChargeMultisetToList]
  rw [List.map_flatMap]
  rw [allowedElems]
  rw [List.flatMap_assoc]
  congr
  funext x
  refine List.eq_replicate_iff.mpr ?_
  constructor
  · conv_lhs =>
      enter [1, 1, a]
      rw [List.map_replicate]
    simp [toCharges]
    conv_lhs =>
      enter [1, 1]
      change fun y => Multiset.count (x, y) F
    rw [Finset.sum_list_map_count]
    trans ∑ m ∈ FluxesFive.allowedPairs.toFinset, Multiset.count (x, m) F
    · apply Finset.sum_congr
      · rfl
      intro m hm
      rw [FluxesFive.mem_allowedPairs_count_one _ hm]
      simp
    rw [Multiset.count_map]
    have h1 (m : ℤ × ℤ) :
      Multiset.count (x, m) F = Multiset.count (x, m) (Multiset.filter (fun a => x = a.1) F) := by
      exact Eq.symm (Multiset.count_filter_of_pos rfl)
    conv_lhs =>
      enter [2, m]
      rw [h1]
    rw [← Multiset.toFinset_sum_count_eq (Multiset.filter (fun a => x = a.1) F)]
    let f : ℤ × ℤ × ℤ → ℕ := fun m => Multiset.count m (Multiset.filter (fun a => x = a.1) F)
    let e : ℤ × ℤ ↪ ℤ × ℤ × ℤ := ⟨Prod.mk x, Prod.mk_right_injective x⟩
    change ∑ m ∈ FluxesFive.allowedPairs.toFinset, f (e m) =
      ∑ a ∈ (Multiset.filter (fun a => x = a.1) F).toFinset, f a
    rw [← Finset.sum_map]
    symm
    apply Finset.sum_subset
    · intro z
      simp
      intro hz hxz
      use z.2.1, z.2.2
      simp [e, hxz]
      apply snd_mem_allowedPairs_of_mem_toList I F
      rw [(mem_toList_iff F hf hc)]
      exact hz
    · intro z hz hnotme
      simp at hnotme
      simpa [f] using hnotme
  · intro b hb
    simp at hb
    obtain ⟨x1, x2, x3, ⟨hx1, rfl⟩, hx2, rfl⟩ := hb
    rfl

lemma toList_prod_snd_perm {I : CodimensionOneConfig} {F : FiveQuanta}
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges) :
    ((F.toList I).map Prod.snd).Perm (FluxesFive.toList F.toFluxesFive) := by
  rw [← Multiset.coe_eq_coe]
  rw [FluxesFive.coe_toList F.toFluxesFive hf]
  rw [show ((List.map Prod.snd (toList I F)) : Multiset _) =
      Multiset.map Prod.snd (Multiset.ofList (F.toList I)) from rfl]
  rw [coe_toList hf hc]
  rfl

end FiveQuanta

/-!

## `TenQuanta` to lists

-/

namespace TenQuanta

/-- The allowed elements of a `FiveQuanta` for which the underlying `FluxesFive` obeys
  `NoExotics` and `HasNoZero` and for which the charges are determined by
  a `CodimensionOneConfig`. -/
def allowedElems (I : CodimensionOneConfig) : List (ℤ × ℤ × ℤ) :=
  I.allowedTenChargesList.flatMap fun x =>
    FluxesTen.allowedPairs.map (fun y => (x, y.1, y.2))

lemma mem_allowedElems_of_mem {I : CodimensionOneConfig} (F : TenQuanta)
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F) : x ∈ allowedElems I := by
  simp [allowedElems]
  use x.1
  constructor
  · apply hc x.1
    simp [toCharges]
    use x.2.1, x.2.2
  · use x.2.1, x.2.2
    simp
    refine FluxesTen.mem_allowedPairs_of_mem_noExotics F.toFluxesTen hf x.2 ?_
    simp [toFluxesTen]
    use x.1

/-- A list from a `TenQuanta` which when the underlying `FluxesTen` obeys
  `NoExotics` and `HasNoZero`, and the charges are determined by
  a `CodimensionOneConfig`, is a list whose underlying multiset is the
  `TenQuanta`. Otherwise this list produces junk. -/
def toList (I : CodimensionOneConfig) (F : TenQuanta) : List (ℤ × ℤ × ℤ) :=
  (allowedElems I).flatMap (fun x => List.replicate (F.count x) x)

lemma mem_allowedElems_of_mem_toList (I : CodimensionOneConfig) (F : TenQuanta)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F.toList I) : x ∈ allowedElems I := by
  simp [toList] at h
  exact h.1

lemma snd_mem_allowedPairs_of_mem_toList (I : CodimensionOneConfig) (F : TenQuanta)
    (x : ℤ × ℤ × ℤ) (h : x ∈ F.toList I) : x.2 ∈ FluxesTen.allowedPairs := by
  have h1 := mem_allowedElems_of_mem_toList I F x h
  simp [allowedElems] at h1
  obtain ⟨x1, hx1, ⟨x2, x3, h2, rfl⟩⟩ := h1
  simpa using h2

lemma mem_toList_iff {I : CodimensionOneConfig} (F : TenQuanta)
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges) {a : ℤ × ℤ × ℤ} :
    a ∈ F.toList I ↔ a ∈ F := by
  simp [toList]
  intro a_1
  obtain ⟨fst, snd⟩ := a
  exact mem_allowedElems_of_mem F hf hc (fst, snd) a_1

set_option maxRecDepth 2000 in
lemma toList_count {I : CodimensionOneConfig} {F : TenQuanta}
    {a : ℤ × ℤ × ℤ}
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges)
    (hmema : a ∈ allowedElems I) :
    (F.toList I).count a = F.count a := by
  by_cases hS : a ∈ F
  · have hmem : a ∈ F.toList I := by
      rw [mem_toList_iff F hf hc]
      exact hS
    simp [toList]
    rw [List.count_flatMap]
    have hf : (List.count a ∘ fun x => List.replicate (Multiset.count x F) x) =
        fun x => if a = x then Multiset.count x F else 0 := by
      funext x
      simp only [Function.comp_apply]
      rw [@List.count_replicate]
      aesop
    rw [hf]
    rw [List.sum_map_eq_nsmul_single a]
    have hc : @List.count (ℤ × ℤ × ℤ) instBEqOfDecidableEq a (allowedElems I) = 1 := by
      revert hmema
      clear * -
      intro h
      revert a I
      decide
    rw [hc]
    simp only [↓reduceIte, one_nsmul]
    intro a' ha' hx
    simp [ha']
    intro hn
    exact fun a_1 => ha' (id (Eq.symm hn))
  · rw [List.count_eq_zero_of_not_mem]
    · exact (Multiset.count_eq_zero.mpr hS).symm
    · rw [mem_toList_iff F hf hc]
      simp_all

lemma coe_toList {I : CodimensionOneConfig} {F : TenQuanta}
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges) :
    ↑(F.toList I) = F := by
  refine Multiset.ext.mpr ?_
  intro a
  by_cases ha : a ∈ allowedElems I
  · simp
    trans (F.toList I).count a
    · congr
      exact lawful_beq_subsingleton instBEqOfDecidableEq instBEqProd
    rw [toList_count hf hc ha]
  · rw [Multiset.count_eq_zero_of_not_mem, Multiset.count_eq_zero_of_not_mem]
    · by_contra hn
      exact ha (mem_allowedElems_of_mem F hf hc a hn)
    · by_contra hn
      rw [Multiset.mem_coe, mem_toList_iff F hf hc] at hn
      exact ha (mem_allowedElems_of_mem F hf hc a hn)

lemma toList_prod_fst_eq {I : CodimensionOneConfig} {F : TenQuanta}
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges) :
    (F.toList I).map Prod.fst = I.tenChargeMultisetToList F.toCharges := by
  simp [toList, CodimensionOneConfig.tenChargeMultisetToList]
  rw [List.map_flatMap]
  rw [allowedElems]
  rw [List.flatMap_assoc]
  congr
  funext x
  refine List.eq_replicate_iff.mpr ?_
  constructor
  · conv_lhs =>
      enter [1, 1, a]
      rw [List.map_replicate]
    simp [toCharges]
    conv_lhs =>
      enter [1, 1]
      change fun y => Multiset.count (x, y) F
    rw [Finset.sum_list_map_count]
    trans ∑ m ∈ FluxesTen.allowedPairs.toFinset, Multiset.count (x, m) F
    · apply Finset.sum_congr
      · rfl
      intro m hm
      rw [FluxesTen.mem_allowedPairs_count_one _ hm]
      simp
    rw [Multiset.count_map]
    have h1 (m : ℤ × ℤ) :
      Multiset.count (x, m) F = Multiset.count (x, m) (Multiset.filter (fun a => x = a.1) F) := by
      exact Eq.symm (Multiset.count_filter_of_pos rfl)
    conv_lhs =>
      enter [2, m]
      rw [h1]
    rw [← Multiset.toFinset_sum_count_eq (Multiset.filter (fun a => x = a.1) F)]
    let f : ℤ × ℤ × ℤ → ℕ := fun m => Multiset.count m (Multiset.filter (fun a => x = a.1) F)
    let e : ℤ × ℤ ↪ ℤ × ℤ × ℤ := ⟨Prod.mk x, Prod.mk_right_injective x⟩
    change ∑ m ∈ FluxesTen.allowedPairs.toFinset, f (e m) =
      ∑ a ∈ (Multiset.filter (fun a => x = a.1) F).toFinset, f a
    rw [← Finset.sum_map]
    symm
    apply Finset.sum_subset
    · intro z
      simp
      intro hz hxz
      use z.2.1, z.2.2
      simp [e, hxz]
      apply snd_mem_allowedPairs_of_mem_toList I F
      rw [(mem_toList_iff F hf hc)]
      exact hz
    · intro z hz hnotme
      simp at hnotme
      simpa [f] using hnotme
  · intro b hb
    simp at hb
    obtain ⟨x1, x2, x3, ⟨hx1, rfl⟩, hx2, rfl⟩ := hb
    rfl

lemma toList_prod_snd_perm {I : CodimensionOneConfig} {F : TenQuanta}
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges) :
    ((F.toList I).map Prod.snd).Perm (FluxesTen.toList F.toFluxesTen) := by
  rw [← Multiset.coe_eq_coe]
  rw [FluxesTen.coe_toList F.toFluxesTen hf]
  rw [show ((List.map Prod.snd (toList I F)) : Multiset _) =
      Multiset.map Prod.snd (Multiset.ofList (F.toList I)) from rfl]
  rw [coe_toList hf hc]
  rfl

end TenQuanta

end SU5U1

end FTheory
