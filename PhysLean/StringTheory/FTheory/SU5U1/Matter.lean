/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfRationalSection
import Mathlib.Data.Finset.Powerset
/-!

# Matter

This module contains the data of the matter content of the SU(5) GUT model in F-theory
with an additional U(1) symmetry.

## Important results

- `Q5` and `Q10` are the multiset of charges associated with the 5-bar and 10d representations
  respectively.

## References

  Krippendorf, Schafer-Nameki and Wong.
  Froggatt-Nielson meets Mordell-Weil: A Phenomenological Survey of Global F-theory GUTs with U(1)s
  <https://arxiv.org/pdf/1507.05961>.

For conditions placed on the matter content, see:
  Krippendorf, Peña, Oehlmann, Ruehle.
  Rational F-theory GUTs without exotics
  <https://arxiv.org/pdf/1401.5084>.

-/
namespace FTheory

namespace SU5U1

/-!

## Quanta assocaited with matter content

-/

/-- A type for the chirality flux of matter. This is induced by G₄-flux.
  This is often denoted `M`. -/
abbrev ChiralityFlux : Type := ℤ

/-- A type for the hypercharge flux associated with matter curves.
  This is often denote `N`. -/
abbrev HyperChargeFlux : Type := ℤ

/-- The type of quanta associated with matter content in the 5-bar representation. -/
abbrev QuantaBarFive : Type :=
  ChiralityFlux × HyperChargeFlux × ℤ

/-- The `ChiralityFlux` quanta of a 5-bar representation. -/
abbrev QuantaBarFive.M (a : QuantaBarFive) : ChiralityFlux := a.1

/-- The `HyperChargeFlux` quanta of a 5-bar representation. -/
abbrev QuantaBarFive.N (a : QuantaBarFive) : HyperChargeFlux := a.2.1

/-- The `ChiralityFlux` and `HyperChargeFlux` quanta of a 5-bar representation. -/
abbrev QuantaBarFive.MN (a : QuantaBarFive) : ChiralityFlux × HyperChargeFlux := (a.M, a.N)

/-- The extra `U(1)` charge of a 5-bar representation. -/
abbrev QuantaBarFive.q (a : QuantaBarFive) : ℤ := a.2.2

/-- The type of quanta associated with matter content in the 10d representation. -/
abbrev QuantaTen : Type :=
  ChiralityFlux × HyperChargeFlux × ℤ

/-- The `ChiralityFlux` quanta of a 10d representation. -/
abbrev QuantaTen.M (a : QuantaTen) : ChiralityFlux := a.1

/-- The `HyperChargeFlux` quanta of a 10d representation. -/
abbrev QuantaTen.N (a : QuantaTen) : HyperChargeFlux := a.2.1

/-- The `ChiralityFlux` and`HyperChargeFlux` quanta of a 10d representation. -/
abbrev QuantaTen.MN (a : QuantaTen) : ChiralityFlux × HyperChargeFlux := (a.M, a.N)

/-- The extra `U(1)` charge of a 10d representation. -/
abbrev QuantaTen.q (a : QuantaTen) : ℤ := a.2.2

/-!

## Condition for distinct charges

-/

/-- The proposition on `Multiset (QuantaBarFive I)`,
  and two `I.allowedBarFiveCharges` denoted `qHu` and `qHd` which is true
  if none of the (underlying) charges are equal. -/
def DistinctChargedBarFive (quantaBarFiveMatter : Multiset QuantaBarFive)
    (qHu : ℤ) (qHd : ℤ) : Prop :=
  (quantaBarFiveMatter.map QuantaBarFive.q).toFinset.card =
      (quantaBarFiveMatter.map QuantaBarFive.q).card
    ∧ qHu ∉ (quantaBarFiveMatter.map QuantaBarFive.q)
    ∧ qHd ∉ (quantaBarFiveMatter.map QuantaBarFive.q)
    ∧ qHu ≠ qHd

instance (quantaBarFiveMatter : Multiset (QuantaBarFive)) (qHu : ℤ) (qHd : ℤ) :
    Decidable (DistinctChargedBarFive quantaBarFiveMatter qHu qHd) := instDecidableAnd

/-- The proposition on a `Multiset (QuantaTen I)` which is true if non of the underlying
  charges are equal. -/
def DistinctChargedTen (quantaTen : Multiset QuantaTen) : Prop :=
  (quantaTen.map QuantaTen.q).toFinset.card = (quantaTen.map QuantaTen.q).card

instance (quantaTen : Multiset QuantaTen) :
    Decidable (DistinctChargedTen quantaTen) := decEq _ _

/-!

## Definition of the matter content

-/

/-- The matter content, assumed to sit in the 5-bar or 10d representation of
  `SU(5)`. -/
@[ext]
structure MatterContent (I : CodimensionOneConfig) where
  /-- The chirality, charge and hyperChargeFlux associated with the 5-bar representations. -/
  quantaBarFiveMatter : Multiset QuantaBarFive
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges :
    (quantaBarFiveMatter.map QuantaBarFive.q).toFinset ⊆ I.allowedBarFiveCharges
  /-- The chirality, charge and hyperChargeFlux associated with the 10d representations. -/
  quantaTen : Multiset QuantaTen
  quantaTen_map_q_subset_allowedTenCharges :
    (quantaTen.map QuantaTen.q).toFinset ⊆ I.allowedTenCharges
  /-- The charge of the up-type Higgs in the 5-bar representation. -/
  qHu : ℤ
  qHu_mem_allowedBarFiveCharges : qHu ∈ I.allowedBarFiveCharges
  /-- The charge of the down-type Higgs in the 5-bar representation. -/
  qHd : ℤ
  qHd_mem_allowedBarFiveCharges : qHd ∈ I.allowedBarFiveCharges
  /-- There is no matter in the 5-bar representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_bar_five_matter :
    ∀ a ∈ quantaBarFiveMatter, (a.M = 0 → a.N ≠ 0)
  /-- There is no matter in the 10d representation with zero `Chirality` and `HyperChargeFlux`. -/
  chirality_charge_not_both_zero_ten : ∀ a ∈ quantaTen, (a.M = 0 → a.N ≠ 0)
  /-- All 5-bar representations carry distinct charges. -/
  distinctly_charged_quantaBarFiveMatter : DistinctChargedBarFive quantaBarFiveMatter qHu qHd
  /-- All 10d representations carry distinct charges. -/
  distinctly_charged_quantaTen : DistinctChargedTen quantaTen

namespace MatterContent

variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-- The type `MatterContent I` has a decidable equality. -/
instance : DecidableEq (MatterContent I) := fun a b =>
  match decEq (a.qHu) (b.qHu) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.qHd) (b.qHd) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.quantaBarFiveMatter) (b.quantaBarFiveMatter) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
  match decEq (a.quantaTen) (b.quantaTen) with
  | .isFalse _ => isFalse (by by_contra hn; simp_all)
  | .isTrue _ =>
    isTrue (by ext1 <;> simp_all)

/-!

## Some properties of quantaBarFiveMatter

-/

lemma quantaBarFiveMatter_map_MN_not_both_zero :
    ∀ a ∈ (𝓜.quantaBarFiveMatter.map QuantaBarFive.MN), (a.1 = 0 → a.2 ≠ 0) := by
  intro a ha
  simp at ha
  obtain ⟨a, b, c, ha, rfl⟩ := ha
  exact 𝓜.chirality_charge_not_both_zero_bar_five_matter (a, b, c) ha

/-!

## Q5: The charges associted with the 5-bar matter content

This is related to the multiset of charges associted with the 5-bar matter content, `𝓜.Q5`,
and its properties.

-/

/-- The multiset of charges associted with the 5-bar matter content. -/
abbrev Q5 : Multiset ℤ := 𝓜.quantaBarFiveMatter.map (QuantaBarFive.q)

lemma Q5_def : 𝓜.Q5 = 𝓜.quantaBarFiveMatter.map (QuantaBarFive.q) := by
  rfl

lemma Q5_subset_allowedBarFiveCharges : 𝓜.Q5.toFinset ⊆ I.allowedBarFiveCharges := by
  rw [Q5_def]
  exact 𝓜.quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges

lemma Q5_noDup : 𝓜.Q5.Nodup :=
  Multiset.dedup_card_eq_card_iff_nodup.mp 𝓜.distinctly_charged_quantaBarFiveMatter.1

lemma Q5_eq_toFinset : 𝓜.Q5 = 𝓜.Q5.toFinset.1 := by
  have h1 := 𝓜.Q5_noDup
  rw [← Multiset.dedup_eq_self] at h1
  conv_lhs => rw [← h1]
  rfl

lemma Q5_mem_powerset : 𝓜.Q5.toFinset ∈ I.allowedBarFiveCharges.powerset := by
  rw [Finset.mem_powerset]
  exact 𝓜.quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges

lemma Q5_mem_powerset_filter_card {n : ℕ}
    (hcard : 𝓜.quantaBarFiveMatter.card = n) : 𝓜.Q5.toFinset ∈
      I.allowedBarFiveCharges.powerset.filter fun x => x.card = n := by
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    𝓜.Q5_mem_powerset]
  trans 𝓜.Q5.card
  · rw [Q5_eq_toFinset]
    simp only [Multiset.toFinset_val, Multiset.toFinset_dedup]
    rfl
  · simpa using hcard

/-!

## quantaBarFive

-/

/-- The `QuantaBarFive` of all 5-bar representations including the up and down Higges.
  The chirality fluxes of the up and down Higges are taken to be zero,
  whilst their hypercharge flux is taken to be -1 and +1 respectively,
  this choice is related to doublet–triplet splitting.
-/
def quantaBarFive : Multiset QuantaBarFive :=
  (0, 1, 𝓜.qHd) ::ₘ (0, -1, 𝓜.qHu) ::ₘ 𝓜.quantaBarFiveMatter

lemma chirality_charge_not_both_zero_bar_five :
    ∀ a ∈ 𝓜.quantaBarFive, (a.M = 0 → a.N ≠ 0) := by
  intro a
  simp [quantaBarFive]
  intro h
  rcases h with rfl | rfl | h
  · simp [QuantaBarFive.N]
  · simp [QuantaBarFive.N]
  · exact 𝓜.chirality_charge_not_both_zero_bar_five_matter a h

lemma quantaBarFive_map_q_subset_allowedBarFiveCharges :
    (𝓜.quantaBarFive.map (QuantaBarFive.q)).toFinset ⊆ I.allowedBarFiveCharges := by
  rw [quantaBarFive]
  simp only [Int.reduceNeg, Multiset.map_cons, Multiset.toFinset_cons]
  refine Finset.insert_subset ?_ ?_
  · exact 𝓜.qHd_mem_allowedBarFiveCharges
  · apply Finset.insert_subset ?_ ?_
    · exact 𝓜.qHu_mem_allowedBarFiveCharges
    · exact 𝓜.quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges

lemma quantaBarFive_map_q_mem_powerset :
    (𝓜.quantaBarFive.map (QuantaBarFive.q)).toFinset ∈ I.allowedBarFiveCharges.powerset := by
  rw [Finset.mem_powerset]
  exact 𝓜.quantaBarFive_map_q_subset_allowedBarFiveCharges

lemma quantaBarFive_chiralityFlux_two_le_count_zero :
    2 ≤ (𝓜.quantaBarFive.map (QuantaBarFive.M)).count 0 := by
  simp [quantaBarFive]

lemma quantaBarFive_chiralityFlux_two_le_filter_zero_card :
    2 ≤ ((𝓜.quantaBarFive.map (QuantaBarFive.M)).filter (fun x => x = 0)).card := by
  apply le_of_le_of_eq 𝓜.quantaBarFive_chiralityFlux_two_le_count_zero
  rw [Multiset.count_eq_card_filter_eq]
  congr
  funext x
  exact Lean.Grind.eq_congr' rfl rfl

lemma quantaBarFive_map_q_noDup : (𝓜.quantaBarFive.map (QuantaBarFive.q)).Nodup := by
  simp only [quantaBarFive, Int.reduceNeg, Multiset.map_cons, Multiset.nodup_cons,
    Multiset.mem_cons, Multiset.mem_map, Prod.exists, exists_eq_right, not_or, not_exists,
    𝓜.Q5_noDup, and_true]
  have h1 := 𝓜.distinctly_charged_quantaBarFiveMatter
  simp_all only [DistinctChargedBarFive, QuantaBarFive.q, Multiset.card_map, Multiset.mem_map,
    Prod.exists, exists_eq_right, not_exists, ne_eq, not_false_eq_true, implies_true, and_true]
  exact fun a => h1.2.2.2 a.symm

set_option maxRecDepth 1000 in
lemma quantaBarFive_map_q_card_le_seven :
    (𝓜.quantaBarFive.map QuantaBarFive.q).card ≤ 7 := by
  rw [← Multiset.dedup_card_eq_card_iff_nodup.mpr 𝓜.quantaBarFive_map_q_noDup]
  have hmem := 𝓜.quantaBarFive_map_q_subset_allowedBarFiveCharges
  change (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset.card ≤ 7
  generalize (Multiset.map QuantaBarFive.q 𝓜.quantaBarFive).toFinset = S at *
  revert S
  match I with
  | CodimensionOneConfig.same => decide
  | CodimensionOneConfig.nearestNeighbor => decide
  | CodimensionOneConfig.nextToNearestNeighbor => decide

lemma quantaBarFive_card_le_seven : 𝓜.quantaBarFive.card ≤ 7 := by
  apply le_of_eq_of_le _ 𝓜.quantaBarFive_map_q_card_le_seven
  simp

/-!

## Some properties of quantaTen

-/
/-!

## Q10: The charges associted with the 10d matter content

This is related to the multiset of charges associted with the 10d matter content, `𝓜.Q10`,
and its properties.

-/

/-- The multiset of charges associted with the 10d matter content. -/
abbrev Q10 : Multiset ℤ := 𝓜.quantaTen.map QuantaTen.q

lemma Q10_def : 𝓜.Q10 = 𝓜.quantaTen.map QuantaTen.q := by rfl

lemma Q10_subset_allowedTenCharges : 𝓜.Q10.toFinset ⊆ I.allowedTenCharges := by
  rw [Q10_def]
  exact 𝓜.quantaTen_map_q_subset_allowedTenCharges

lemma Q10_nodup : 𝓜.Q10.Nodup :=
  Multiset.dedup_card_eq_card_iff_nodup.mp 𝓜.distinctly_charged_quantaTen

lemma Q10_eq_toFinset : 𝓜.Q10 = 𝓜.Q10.toFinset.1 := by
  have h1 := 𝓜.Q10_nodup
  rw [← Multiset.dedup_eq_self] at h1
  conv_lhs => rw [← h1]
  rfl

lemma Q10_mem_powerset : 𝓜.Q10.toFinset ∈ I.allowedTenCharges.powerset := by
  rw [Finset.mem_powerset]
  exact 𝓜.quantaTen_map_q_subset_allowedTenCharges

end MatterContent

end SU5U1

end FTheory
