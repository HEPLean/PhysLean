/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.ToList
/-!

# Quanta from charges and fluxes

Each `FiveQuanta` or `TenQuanta` has an underlying `FluxesFive` or `FluxesTen`
and `Multiset ℤ` of charges.

In this file we define the `fromParts` function which takes a
`FluxesFive` or `FluxesTen` and a `Multiset ℤ` of charges and returns a list of
the allowed `FiveQuanta` or `TenQuanta` which can be formed from them.

We do this only in the very restrictive case when:
- `fluxes` has no exotics and has no zero fluxes
- `charges` has length less than or equal to `3` and lives in `allowedBarFiveCharges` or
  `allowedBarTenCharges` for a given `CodimensionOneConfig`.

-/

/-!

## Auxiliary Results

Computable permutations of lists of length at most 3.

-/

/-- For a list `l` of length less then three `l.lowPermutations` is the
  list of permutations of `l`. If the length of `l` is greater then three
  then this returns `[]`. This is defined so one can use `decide` with such permutations. -/
def _root_.List.lowPermutations : (l : List (ℤ × ℤ)) → List (List (ℤ × ℤ))
  | [] => [[]]
  | x :: [] => [[x]]
  | x1 :: x2 :: [] => if x1 = x2 then [[x1, x2]] else
    [[x1, x2], [x2, x1]]
  | x1 :: x2 :: x3 :: [] =>
    if x1 = x2 ∧ x2 = x3 then
      [[x1, x2, x3]]
    else if x1 = x2 then
      [[x1, x2, x3], [x1, x3, x2], [x3, x1, x2]]
    else if x2 = x3 then
      [[x1, x2, x3], [x2, x1, x3], [x2, x3, x1]]
    else if x1 = x3 then
      [[x1, x2, x3], [x2, x1, x3], [x1, x3, x2]]
    else
      [[x1, x2, x3], [x1, x3, x2], [x2, x1, x3], [x2, x3, x1], [x3, x1, x2], [x3, x2, x1]]
  | _ :: _ :: _ :: _ => []

lemma _root_.List.lowPermutations_perm_mem_of_length_le_three :
    (l l1 : List (ℤ × ℤ)) → (h : l.Perm l1) → (hl : l.length ≤ 3) → l1 ∈ l.lowPermutations
  | [], l1, h, hl => by
    simpa [List.lowPermutations] using h
  | x :: [], l1, h, hl => by
    simpa [List.lowPermutations] using h.symm
  | x1 :: x2 :: [], l, h, hl => by
    simp [List.lowPermutations]
    have hl : l.length = 2 := by
      rw [← List.Perm.length_eq h]
      simp
    rw [List.length_eq_two] at hl
    obtain ⟨y1, y2, rfl⟩ := hl
    simp [List.cons_perm_iff_perm_erase] at h
    by_cases h1 : x1 = y1
    · subst h1
      simp at h
      obtain ⟨h2', h3'⟩ := h
      subst h2'
      split
      · simp
      · simp
    · have h1 : x1 = y2 := by
        simp [h1] at h
        exact h.1
      subst h1
      simp at h
      rw [List.erase_cons] at h
      have hn : y1 ≠ x1 := by exact fun a => h1 (id (Eq.symm a))
      simp [hn] at h
      obtain ⟨h2', h3'⟩ := h
      subst h2'
      split <;> simp_all
  | x1 :: x2 :: x3 :: [], l1, h, hl => by
    simp [List.lowPermutations]
    have hl : l1.length = 3 := by
      rw [← List.Perm.length_eq h]
      simp
    rw [List.length_eq_three] at hl
    obtain ⟨y1, y2, y3, rfl⟩ := hl
    simp [List.cons_perm_iff_perm_erase] at h
    have h1 := h.1
    by_cases h1 : x1 = y1
    · subst h1
      by_cases h2 : x2 = y2
      · subst h2
        simp at h
        have h3 := h.1
        subst h3
        split_ifs
          <;> simp
      · have h2 : x2 = y3 := by
          simp [h2] at h
          exact h.1
        have h2n : y2 ≠ x2 := by
          (expose_names; exact fun a => h2_1 (id (Eq.symm a)))
        subst h2
        simp at h
        simp [List.erase_cons, h2n] at h
        have h3 := h.1
        subst h3
        split_ifs <;> simp_all
    · have h1n : y1 ≠ x1 := by
        (expose_names; exact fun a => h1 (id (Eq.symm a)))
      simp [h1n] at h
      by_cases h1 : x1 = y2
      · simp [h1] at h
        by_cases h2 : x2 = y1
        · simp [h2] at h
          have h3 := h.1
          subst h3
          split_ifs <;> simp_all
        · have h2 : x2 = y3 := by
            simp [h2] at h
            exact h.1
          have h2n : y1 ≠ x2 := by
            (expose_names; exact fun a => h2_1 (id (Eq.symm a)))
          subst h2
          simp [List.erase_cons, h2n] at h
          have h3 := h.1
          subst h3
          split_ifs <;> simp_all
      · simp_all
        expose_names
        have h2n : y2 ≠ x1 := by
          exact Ne.symm (Lean.Grind.ne_of_ne_of_eq_left h1_1 h1)
        subst h1_1 -- x1 = y3
        by_cases h2 : x2 = y1
        · subst h2
          simp [List.erase_cons, h2n] at h
          have h3 := h.1
          subst h3
          split_ifs <;> simp_all
        · have h3n : y1 ≠ x2 := by
            exact fun a => h2 (id (Eq.symm a))
          have h2 : x2 = y2 := by
            simp [List.erase_cons, h3n, h2n, h1n] at h
            exact h.2.2.2.symm
          have h3 : x3 = y1 := by
            simp [List.erase_cons, h3n, h2n, h1n] at h
            exact h.2.2.1.symm
          subst h2 h3
          split_ifs <;> simp_all

lemma _root_.List.perm_of_mem_lowPermutations_of_length_le_three :
    (l l1 : List (ℤ × ℤ)) → (h : l1 ∈ l.lowPermutations) → (hl : l.length ≤ 3) → l1.Perm l
  | [], l1, h, hl => by
    simpa [List.lowPermutations] using h
  | x :: [], l1, h, hl => by
    simp [List.lowPermutations] at h
    subst h
    simp
  | x1 :: x2 :: [], l1, h, hl => by
    simp [List.lowPermutations] at h
    split_ifs at h
    · simp_all
    · simp_all
      rcases h with rfl | rfl
      · simp
      · exact List.Perm.swap x1 x2 []
  | x1 :: x2 :: x3 :: [], l1, h, hl => by
    simp [List.lowPermutations] at h
    split_ifs at h
    · simp_all
    · simp_all
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
        exact List.Perm.swap x2 x3 []
      · trans [x2, x3, x2]
        · exact List.Perm.swap x2 x3 [x2]
        · simp
          exact List.Perm.swap x2 x3 []
    · simp_all
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · exact List.Perm.swap x1 x3 [x3]
      · trans [x3, x1, x3]
        · simp
          exact List.Perm.swap x1 x3 []
        · exact List.Perm.swap x1 x3 [x3]
    · simp_all
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · exact List.Perm.swap x3 x2 [x3]
      · trans [x3, x2, x3]
        · simp
          exact List.Perm.swap x2 x3 []
        · exact List.perm_iff_count.mpr (congrFun rfl)
    · simp_all
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      any_goals simp
      · exact List.Perm.swap x2 x3 []
      · exact List.Perm.swap x1 x2 [x3]
      · trans [x2, x1, x3]
        · simp
          exact List.Perm.swap x1 x3 []
        · exact List.Perm.swap x1 x2 [x3]
      · trans [x1, x3, x2]
        · exact List.Perm.swap x1 x3 [x2]
        · simp
          exact List.Perm.swap x2 x3 []
      · trans [x3, x1, x2]
        · simp
          exact List.Perm.swap x1 x2 []
        · trans [x1, x3, x2]
          · exact List.Perm.swap x1 x3 [x2]
          · simp
            exact List.Perm.swap x2 x3 []

lemma _root_.List.lowPermutations_empty_of_not_le_three :
    (l : List (ℤ × ℤ)) → (hl : ¬ l.length ≤ 3) → l.lowPermutations = []
| [], hl => by simp at hl
| x :: [], hl => by simp at hl
| x1 :: x2 :: [], hl => by simp at hl
| x1 :: x2 :: x3 :: [], hl => by simp at hl
| _ :: _ :: _ :: _ :: _, hl => rfl

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-!

## FiveQuanta from parts

-/

namespace FiveQuanta

/-- The list of `FiveQuanta` which arise from `charges` and `fluxes`.
  Note: This gives junk unless `charges` has length less than or equal to `3`,
  the charges correspond to a `CodimensionOneConfig`
  and `fluxes` has no exotics and no zero entries. -/
def fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesFive) :
    List FiveQuanta :=
  if charges.card ≠ fluxes.card then {} else
  let chargesList : List ℤ := I.fiveChargeMultisetToList charges
  let fluxesList : List (ℤ × ℤ) := FluxesFive.toList fluxes
  let fluxesPerms : List (List (ℤ × ℤ)) := fluxesList.lowPermutations
  fluxesPerms.map (fun l => chargesList.zip l)

lemma self_mem_fromParts_of_toCharges_toFluxesFive (I : CodimensionOneConfig) (F : FiveQuanta)
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges)
    (hcard : Multiset.card F ≤ 3) :
    F ∈ fromParts I F.toCharges F.toFluxesFive := by
  simp [fromParts]
  apply And.intro
  · simp [toCharges, toFluxesFive]
  use (F.toList I).map Prod.snd
  constructor
  · apply List.lowPermutations_perm_mem_of_length_le_three
    · exact List.Perm.symm (toList_prod_snd_perm hf hc)
    · rw [FluxesFive.toList_length F.toFluxesFive hf]
      simp [toFluxesFive]
      exact hcard
  · rw [← toList_prod_fst_eq hf hc]
    conv_rhs => rw [← coe_toList hf hc]
    congr
    exact Eq.symm (List.zip_of_prod rfl rfl)

lemma card_eq_charges_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesFive) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = charges.card := by
  intro F hF
  simp? [fromParts]  at hF says
    simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right, List.mem_map] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  simp only [Multiset.coe_card, List.length_zip]
  rw [CodimensionOneConfig.fiveChargeMultisetToList_length I charges hc]
  rw [hcard]
  have hflux : fluxes.toList.length ≤ 3 := by
    by_contra hn
    rw [List.lowPermutations_empty_of_not_le_three] at hperm
    simp at hperm
    exact hn
  have hl : l.Perm fluxes.toList := by
    apply List.perm_of_mem_lowPermutations_of_length_le_three
    · exact hperm
    · exact hflux
  have hl : l.length = fluxes.toList.length := by
    rw [List.Perm.length_eq hl]
  rw [FluxesFive.toList_length fluxes hf] at hl
  rw [hl]
  simp

lemma card_eq_fluxes_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesFive) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = fluxes.card := by
  intro F hF
  rw [card_eq_charges_card_of_mem_fromParts I charges fluxes hf hc F hF]
  simp [fromParts] at hF
  exact hF.1

lemma card_le_three_of_mem_fromPart (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesFive) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card ≤ 3 := by
  intro F hF
  rw [card_eq_fluxes_card_of_mem_fromParts I charges fluxes hf hc F hF]
  by_contra hn
  simp? [fromParts]  at hF says
    simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right, List.mem_map] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  rw [List.lowPermutations_empty_of_not_le_three] at hperm
  simp only [List.not_mem_nil] at hperm
  rw [FluxesFive.toList_length fluxes hf]
  exact hn

lemma fromParts_eq_preimage (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesFive)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges)
    (F : FiveQuanta) :
    F.toCharges = charges ∧ F.toFluxesFive = fluxes ∧ F.card ≤ 3 ↔
      F ∈ fromParts I charges fluxes := by
  constructor
  · intro ⟨h1, h2, h3⟩
    subst h1 h2
    (expose_names; exact self_mem_fromParts_of_toCharges_toFluxesFive I F hf hc h3)
  · intro h
    have F_card := card_le_three_of_mem_fromPart I charges fluxes hf hc F h
    simp only [F_card, and_true]
    have fluxes_length : fluxes.toList.length ≤ 3 := by
      (expose_names; rw [FluxesFive.toList_length fluxes hf])
      rw [← card_eq_fluxes_card_of_mem_fromParts I charges fluxes hf hc F h]
      exact F_card
    simp? [fromParts]  at h says
      simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right,
        List.mem_map] at h
    obtain ⟨hcard, l, hperm, rfl⟩ := h
    have hlflux : l.Perm fluxes.toList := by
      apply List.perm_of_mem_lowPermutations_of_length_le_three
      · exact hperm
      · exact fluxes_length
    have l_length: l.length = charges.card := by
      rw [List.Perm.length_eq hlflux]
      rw [hcard]
      (expose_names; exact FluxesFive.toList_length fluxes hf)
    constructor
    · rw [toCharges]
      trans ↑(List.map Prod.fst ((I.fiveChargeMultisetToList charges).zip l))
      · rfl
      trans ↑(I.fiveChargeMultisetToList charges)
      · congr
        apply List.map_fst_zip
        rw [CodimensionOneConfig.fiveChargeMultisetToList_length I charges hc]
        rw [l_length]
      · exact CodimensionOneConfig.coe_fiveChargeMultisetToList_of_all_mem I charges hc
    · trans ↑(List.map Prod.snd ((I.fiveChargeMultisetToList charges).zip l))
      · rfl
      trans ↑l
      · congr
        apply List.map_snd_zip
        rw [CodimensionOneConfig.fiveChargeMultisetToList_length I charges hc]
        rw [l_length]
      · trans ↑(fluxes.toList)
        swap
        · (expose_names; exact FluxesFive.coe_toList fluxes hf)
        refine Multiset.coe_eq_coe.mpr ?_
        exact hlflux

lemma fromParts_eq_preimage_of_charges_card_le_three (I : CodimensionOneConfig)
    (charges : Multiset ℤ) (fluxes : FluxesFive)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges)
    (F : FiveQuanta) (hcard : charges.card ≤ 3) :
    F.toCharges = charges ∧ F.toFluxesFive = fluxes ↔ F ∈ fromParts I charges fluxes := by
  rw [← fromParts_eq_preimage I charges fluxes hf hc F]
  simp only [and_congr_right_iff, iff_self_and]
  intro h1 h2
  have hx : Multiset.card F = charges.card := by
    rw [← h1]
    simp [toCharges]
  rw [hx]
  exact hcard

/-- The multiset of `FiveQuanta` obtained from a mutliset of charges `Multiset ℤ`,
  which have a `FluxesFive` in `FluxesFive.elemsNoExotics`. -/
def ofCharges (I : CodimensionOneConfig) (c : Multiset ℤ) : Multiset FiveQuanta :=
  FluxesFive.elemsNoExotics.bind fun f => fromParts I c f

end FiveQuanta

/-!

## TenQuanta from parts

-/

namespace TenQuanta

/-- The list of `TenQuanta` which arise from `charges` and `fluxes`.
  Note: This gives junk unless `charges` has length less than or equal to `3`,
  the charges correspond to a `CodimensionOneConfig`
  and `fluxes` has no exotics and no zero entries. -/
def fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesTen) :
    List TenQuanta :=
  if charges.card ≠ fluxes.card then {} else
  let chargesList : List ℤ := I.tenChargeMultisetToList charges
  let fluxesList : List (ℤ × ℤ) := FluxesTen.toList fluxes
  let fluxesPerms : List (List (ℤ × ℤ)) := fluxesList.lowPermutations
  fluxesPerms.map (fun l => chargesList.zip l)

lemma self_mem_fromParts_of_toCharges_toFluxesTen (I : CodimensionOneConfig) (F : TenQuanta)
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges)
    (hcard : Multiset.card F ≤ 3) :
    F ∈ fromParts I F.toCharges F.toFluxesTen := by
  simp [fromParts]
  apply And.intro
  · simp [toCharges, toFluxesTen]
  use (F.toList I).map Prod.snd
  constructor
  · apply List.lowPermutations_perm_mem_of_length_le_three
    · exact List.Perm.symm (toList_prod_snd_perm hf hc)
    · rw [FluxesTen.toList_length F.toFluxesTen hf]
      simp [toFluxesTen]
      exact hcard
  · rw [← toList_prod_fst_eq hf hc]
    conv_rhs => rw [← coe_toList hf hc]
    congr
    exact Eq.symm (List.zip_of_prod rfl rfl)

lemma card_eq_charges_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesTen) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = charges.card := by
  intro F hF
  simp? [fromParts] at hF says
    simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right, List.mem_map] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  simp only [Multiset.coe_card, List.length_zip]
  rw [CodimensionOneConfig.tenChargeMultisetToList_length I charges hc]
  rw [hcard]
  have hflux : fluxes.toList.length ≤ 3 := by
    by_contra hn
    rw [List.lowPermutations_empty_of_not_le_three] at hperm
    simp at hperm
    exact hn
  have hl : l.Perm fluxes.toList := by
    apply List.perm_of_mem_lowPermutations_of_length_le_three
    · exact hperm
    · exact hflux
  have hl : l.length = fluxes.toList.length := by
    rw [List.Perm.length_eq hl]
  rw [FluxesTen.toList_length fluxes hf] at hl
  rw [hl]
  simp

lemma card_eq_fluxes_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesTen) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = fluxes.card := by
  intro F hF
  rw [card_eq_charges_card_of_mem_fromParts I charges fluxes hf hc F hF]
  simp [fromParts] at hF
  exact hF.1

lemma card_le_three_of_mem_fromPart (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesTen) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card ≤ 3 := by
  intro F hF
  rw [card_eq_fluxes_card_of_mem_fromParts I charges fluxes hf hc F hF]
  by_contra hn
  simp [fromParts] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  rw [List.lowPermutations_empty_of_not_le_three] at hperm
  simp at hperm
  rw [FluxesTen.toList_length fluxes hf]
  exact hn

lemma fromParts_eq_preimage (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesTen)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) (F : TenQuanta) :
    F.toCharges = charges ∧ F.toFluxesTen = fluxes ∧ F.card ≤ 3 ↔
      F ∈ fromParts I charges fluxes := by
  constructor
  · intro ⟨h1, h2, h3⟩
    subst h1 h2
    (expose_names; exact self_mem_fromParts_of_toCharges_toFluxesTen I F hf hc h3)
  · intro h
    have F_card := card_le_three_of_mem_fromPart I charges fluxes hf hc F h
    simp only [F_card, and_true]
    have fluxes_length : fluxes.toList.length ≤ 3 := by
      (expose_names; rw [FluxesTen.toList_length fluxes hf])
      rw [← card_eq_fluxes_card_of_mem_fromParts I charges fluxes hf hc F h]
      exact F_card
    simp [fromParts] at h
    obtain ⟨hcard, l, hperm, rfl⟩ := h
    have hlflux : l.Perm fluxes.toList := by
      apply List.perm_of_mem_lowPermutations_of_length_le_three
      · exact hperm
      · exact fluxes_length
    have l_length: l.length = charges.card := by
      rw [List.Perm.length_eq hlflux]
      rw [hcard]
      (expose_names; exact FluxesTen.toList_length fluxes hf)
    constructor
    · rw [toCharges]
      trans ↑(List.map Prod.fst ((I.tenChargeMultisetToList charges).zip l))
      · rfl
      trans ↑(I.tenChargeMultisetToList charges)
      · congr
        apply List.map_fst_zip
        rw [CodimensionOneConfig.tenChargeMultisetToList_length I charges hc]
        rw [l_length]
      · exact CodimensionOneConfig.coe_tenChargeMultisetToList_of_all_mem I charges hc
    · trans ↑(List.map Prod.snd ((I.tenChargeMultisetToList charges).zip l))
      · rfl
      trans ↑l
      · congr
        apply List.map_snd_zip
        rw [CodimensionOneConfig.tenChargeMultisetToList_length I charges hc]
        rw [l_length]
      · trans ↑(fluxes.toList)
        swap
        · (expose_names; exact FluxesTen.coe_toList fluxes hf)
        refine Multiset.coe_eq_coe.mpr ?_
        exact hlflux

lemma fromParts_eq_preimage_of_charges_card_le_three (I : CodimensionOneConfig)
    (charges : Multiset ℤ) (fluxes : FluxesTen)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges)
    (F : TenQuanta) (hcard : charges.card ≤ 3) :
    F.toCharges = charges ∧ F.toFluxesTen = fluxes ↔ F ∈ fromParts I charges fluxes := by
  rw [← fromParts_eq_preimage I charges fluxes hf hc F]
  simp only [and_congr_right_iff, iff_self_and]
  intro h1 h2
  have hx : Multiset.card F = charges.card := by
    rw [← h1]
    simp [toCharges]
  rw [hx]
  exact hcard

/-- The multiset of `TenQuanta` obtained from a mutliset of charges `Multiset ℤ`,
  which have a `FluxesTen` in `FluxesTen.elemsNoExotics`. -/
def ofCharges (I : CodimensionOneConfig) (c : Multiset ℤ) : Multiset FiveQuanta :=
  FluxesTen.elemsNoExotics.bind fun f => fromParts I c f

end TenQuanta

end SU5U1

end FTheory
