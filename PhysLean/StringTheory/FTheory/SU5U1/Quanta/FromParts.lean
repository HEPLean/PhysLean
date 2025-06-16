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
- `charges` lives in `allowedBarFiveCharges` or
  `allowedBarTenCharges` for a given `CodimensionOneConfig`.

-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-!

## FiveQuanta from parts

-/

namespace FiveQuanta

/-- The list of `FiveQuanta` which arise from `charges` and `fluxes`.
  Note: This gives junk unless
  the charges correspond to a `CodimensionOneConfig`
  and `fluxes` has no exotics and no zero entries. -/
def fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesFive) :
    List FiveQuanta :=
  if charges.card ≠ fluxes.card then {} else
  let chargesList : List ℤ := I.fiveChargeMultisetToList charges
  let fluxesList : List (ℤ × ℤ) := FluxesFive.toList fluxes
  let fluxesPerms : List (List (ℤ × ℤ)) := fluxesList.permutations'.dedup
  fluxesPerms.map (fun l => chargesList.zip l)

lemma self_mem_fromParts_of_toCharges_toFluxesFive (I : CodimensionOneConfig) (F : FiveQuanta)
    (hf : F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedBarFiveCharges) :
    F ∈ fromParts I F.toCharges F.toFluxesFive := by
  simp [fromParts]
  apply And.intro
  · simp [toCharges, toFluxesFive]
  use (F.toList I).map Prod.snd
  constructor
  · exact (toList_prod_snd_perm hf hc)
  · rw [← toList_prod_fst_eq hf hc]
    conv_rhs => rw [← coe_toList hf hc]
    congr
    exact Eq.symm (List.zip_of_prod rfl rfl)

lemma card_eq_charges_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesFive) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = charges.card := by
  intro F hF
  simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right, List.mem_map] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  simp only [Multiset.coe_card, List.length_zip]
  rw [CodimensionOneConfig.fiveChargeMultisetToList_length I charges hc]
  rw [hcard]
  rw [List.mem_dedup] at hperm
  have hl : l.Perm fluxes.toList := List.mem_permutations'.mp hperm
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

lemma fromParts_eq_preimage (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesFive)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges)
    (F : FiveQuanta) :
    F.toCharges = charges ∧ F.toFluxesFive = fluxes ↔
      F ∈ fromParts I charges fluxes := by
  constructor
  · intro ⟨h1, h2⟩
    subst h1 h2
    exact self_mem_fromParts_of_toCharges_toFluxesFive I F hf hc
  · intro h
    simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right,
        List.mem_map] at h
    obtain ⟨hcard, l, hperm, rfl⟩ := h
    rw [List.mem_dedup] at hperm
    have hlflux : l.Perm fluxes.toList := by
      exact List.mem_permutations'.mp hperm
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

/-- The multiset of `FiveQuanta` obtained from a mutliset of charges `Multiset ℤ`,
  which have a `FluxesFive` in `FluxesFive.elemsNoExotics`. -/
def ofCharges (I : CodimensionOneConfig) (c : Multiset ℤ) : Multiset FiveQuanta :=
  FluxesFive.elemsNoExotics.bind fun f => fromParts I c f

lemma mem_ofCharges_iff (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (hc : ∀ s ∈ charges, s ∈ I.allowedBarFiveCharges) (F : FiveQuanta) :
    F ∈ ofCharges I charges ↔
      F.toCharges = charges ∧ F.toFluxesFive.NoExotics ∧ F.toFluxesFive.HasNoZero := by
  constructor
  · intro h
    simp [ofCharges] at h
    obtain ⟨f, hf, hF⟩ := h
    rw [← fromParts_eq_preimage] at hF
    obtain ⟨h1, h2⟩ := hF
    subst h1 h2
    simp only [true_and]
    constructor
    · exact FluxesFive.noExotics_of_mem_elemsNoExotics F.toFluxesFive hf
    · exact FluxesFive.hasNoZero_of_mem_elemsNoExotics F.toFluxesFive hf
    constructor
    · exact FluxesFive.noExotics_of_mem_elemsNoExotics f hf
    · exact FluxesFive.hasNoZero_of_mem_elemsNoExotics f hf
    · exact hc
  · intro ⟨rfl, h2, h3⟩
    simp [ofCharges]
    use F.toFluxesFive
    refine ⟨FluxesFive.mem_elemsNoExotics_of_noExotics F.toFluxesFive h2 h3, ?_⟩
    rw [← fromParts_eq_preimage I F.toCharges F.toFluxesFive]
    · simp
    · simp_all
      exact h3
    · exact hc

lemma mem_ofCharges_self (I : CodimensionOneConfig) (c : FiveQuanta)
    (h : c.toFluxesFive.NoExotics) (hnz : c.toFluxesFive.HasNoZero)
    (hc : ∀ s ∈ c.toCharges, s ∈ I.allowedBarFiveCharges) :
    c ∈ ofCharges I c.toCharges := by
  simp [ofCharges]
  use c.toFluxesFive
  refine ⟨FluxesFive.mem_elemsNoExotics_of_noExotics c.toFluxesFive h hnz, ?_⟩
  rw [← fromParts_eq_preimage I c.toCharges c.toFluxesFive]
  simp only [and_self]
  exact ⟨h, hnz⟩
  exact hc

end FiveQuanta

/-!

## TenQuanta from parts

-/

namespace TenQuanta

/-- The list of `TenQuanta` which arise from `charges` and `fluxes`.
  Note: This gives junk unless `charges`
  the charges correspond to a `CodimensionOneConfig`
  and `fluxes` has no exotics and no zero entries. -/
def fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesTen) :
    List TenQuanta :=
  if charges.card ≠ fluxes.card then {} else
  let chargesList : List ℤ := I.tenChargeMultisetToList charges
  let fluxesList : List (ℤ × ℤ) := FluxesTen.toList fluxes
  let fluxesPerms : List (List (ℤ × ℤ)) := fluxesList.permutations'.dedup
  fluxesPerms.map (fun l => chargesList.zip l)

lemma self_mem_fromParts_of_toCharges_toFluxesTen (I : CodimensionOneConfig) (F : TenQuanta)
    (hf : F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ F.toCharges, s ∈ I.allowedTenCharges) :
    F ∈ fromParts I F.toCharges F.toFluxesTen := by
  simp [fromParts]
  apply And.intro
  · simp [toCharges, toFluxesTen]
  use (F.toList I).map Prod.snd
  constructor
  · exact (toList_prod_snd_perm hf hc)
  · rw [← toList_prod_fst_eq hf hc]
    conv_rhs => rw [← coe_toList hf hc]
    congr
    exact Eq.symm (List.zip_of_prod rfl rfl)

lemma card_eq_charges_card_of_mem_fromParts (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (fluxes : FluxesTen) (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) :
    ∀ F ∈ fromParts I charges fluxes, F.card = charges.card := by
  intro F hF
  simp only [fromParts, ne_eq, List.empty_eq, ite_not, List.mem_ite_nil_right, List.mem_map] at hF
  obtain ⟨hcard, l, hperm, rfl⟩ := hF
  simp only [Multiset.coe_card, List.length_zip]
  rw [CodimensionOneConfig.tenChargeMultisetToList_length I charges hc]
  rw [hcard]
  rw [List.mem_dedup] at hperm
  have hl : l.Perm fluxes.toList := by
    exact List.mem_permutations'.mp hperm
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

lemma fromParts_eq_preimage (I : CodimensionOneConfig) (charges : Multiset ℤ) (fluxes : FluxesTen)
    (hf : fluxes.NoExotics ∧ fluxes.HasNoZero)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) (F : TenQuanta) :
    F.toCharges = charges ∧ F.toFluxesTen = fluxes ↔
      F ∈ fromParts I charges fluxes := by
  constructor
  · intro ⟨h1, h2⟩
    subst h1 h2
    exact self_mem_fromParts_of_toCharges_toFluxesTen I F hf hc
  · intro h
    simp [fromParts] at h
    obtain ⟨hcard, l, hperm, rfl⟩ := h
    have hlflux : l.Perm fluxes.toList := by
      exact hperm
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

/-- The multiset of `TenQuanta` obtained from a mutliset of charges `Multiset ℤ`,
  which have a `FluxesTen` in `FluxesTen.elemsNoExotics`. -/
def ofCharges (I : CodimensionOneConfig) (c : Multiset ℤ) : Multiset TenQuanta :=
  FluxesTen.elemsNoExotics.bind fun f => fromParts I c f

lemma mem_ofCharges_iff (I : CodimensionOneConfig) (charges : Multiset ℤ)
    (hc : ∀ s ∈ charges, s ∈ I.allowedTenCharges) (F : TenQuanta) :
    F ∈ ofCharges I charges ↔
      F.toCharges = charges ∧ F.toFluxesTen.NoExotics ∧ F.toFluxesTen.HasNoZero := by
  constructor
  · intro h
    simp [ofCharges] at h
    obtain ⟨f, hf, hF⟩ := h
    rw [← fromParts_eq_preimage] at hF
    obtain ⟨h1, h2⟩ := hF
    subst h1 h2
    simp only [true_and]
    constructor
    · exact FluxesTen.noExotics_of_mem_elemsNoExotics F.toFluxesTen hf
    · exact FluxesTen.hasNoZero_of_mem_elemsNoExotics F.toFluxesTen hf
    constructor
    · exact FluxesTen.noExotics_of_mem_elemsNoExotics f hf
    · exact FluxesTen.hasNoZero_of_mem_elemsNoExotics f hf
    · exact hc
  · intro ⟨rfl, h2, h3⟩
    simp [ofCharges]
    use F.toFluxesTen
    refine ⟨FluxesTen.mem_elemsNoExotics_of_noExotics F.toFluxesTen h2 h3, ?_⟩
    rw [← fromParts_eq_preimage I F.toCharges F.toFluxesTen]
    · simp
    · simp_all
      exact h3
    · exact hc

lemma mem_ofCharges_self (I : CodimensionOneConfig) (c : TenQuanta)
    (h : c.toFluxesTen.NoExotics) (hnz : c.toFluxesTen.HasNoZero)
    (hc : ∀ s ∈ c.toCharges, s ∈ I.allowedTenCharges) :
    c ∈ ofCharges I c.toCharges := by
  simp [ofCharges]
  use c.toFluxesTen
  refine ⟨FluxesTen.mem_elemsNoExotics_of_noExotics c.toFluxesTen h hnz, ?_⟩
  rw [← fromParts_eq_preimage I c.toCharges c.toFluxesTen]
  simp only [and_self]
  exact ⟨h, hnz⟩
  exact hc

end TenQuanta

namespace Quanta

open SuperSymmetry.SU5

/-- The multiset of `Quanta` obtained from a `Charges`,
  which have a `Fluxes` which do not permit exotics. -/
def ofCharges (I : CodimensionOneConfig) (c : Charges) : Multiset Quanta :=
    let c1 := FiveQuanta.ofCharges I c.2.2.1.val
    let c2 := TenQuanta.ofCharges I c.2.2.2.val
    (c1.product c2).map fun (F, T) => (c.1, c.2.1, F, T)

end Quanta

end SU5U1

end FTheory
