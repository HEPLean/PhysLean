/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Basic
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.Basic
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Basic
/-!

# Examples of matter content and show that they satisfy certain conditions

The examples in this module correspond to those in:

  Krippendorf, Schafer-Nameki and Wong.
  Froggatt-Nielson meets Mordell-Weil: A Phenomenological Survey of Global F-theory GUTs with U(1)s
  <https://arxiv.org/pdf/1507.05961>.

We copy the notational convention used there.
For example I14a corresponds to the first (`a`) example with
`1` 10d representation and `4` 5-bar representations.

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

/-!

## One 10d representation and four 5-bar representations

These examples come from Table 1 of arXiv:1507.05961

-/

/--

The construction of matter content given a `CodimensionOneConfig` from
a value of `M`, `N` and the charges of the representations.

The charge of `qHu` is the charge of the `5` not the `5`-bar representation.

This parameterizaton comes from Section 3.1.2 of arXiv:1507.05961.
-/
def mkOneTenFourFiveBar (I : CodimensionOneConfig) (M : ChiralityFlux) (N : HyperChargeFlux)
    (q10 qHu qHd q5₁ q5₂ : ℤ)
    (hq10 : q10 ∈ I.allowedTenCharges := by decide)
    (hqHu : - qHu ∈ I.allowedBarFiveCharges := by decide)
    (hqHd : qHd ∈ I.allowedBarFiveCharges := by decide)
    (hq5₁ : q5₁ ∈ I.allowedBarFiveCharges := by decide)
    (hq5₂ : q5₂ ∈ I.allowedBarFiveCharges := by decide)
    (h5 : ∀ a ∈ ({(M, N, q5₁), (3 - M, - N, q5₂)} :
      Multiset QuantaBarFive), a.M = 0 → a.N ≠ 0 := by decide)
    (h10 : ∀ a ∈ ({(3, 0, q10)} : Multiset QuantaTen), a.M = 0 → a.N ≠ 0 := by decide)
    (hd5 : DistinctChargedBarFive {(M, N, q5₁), (3 - M, - N, q5₂)}
      (-qHu) qHd := by decide)
    (hd10 : DistinctChargedTen {(3, 0, q10)} := by decide) :
    MatterContent I where
  quantaBarFiveMatter := {(M, N, q5₁), (3 - M, - N, q5₂)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by
    simp [QuantaBarFive.q]
    refine Finset.insert_subset_iff.mpr ?_
    simp [hq5₁, hq5₂]
  quantaTen := {(3, 0, q10)}
  quantaTen_map_q_subset_allowedTenCharges := by
    simp only [QuantaTen.q, Multiset.map_singleton, Multiset.toFinset_singleton,
      Finset.singleton_subset_iff]
    exact hq10
  qHu := - qHu
  qHu_mem_allowedBarFiveCharges := hqHu
  qHd := qHd
  qHd_mem_allowedBarFiveCharges := hqHd
  chirality_charge_not_both_zero_bar_five_matter := h5
  chirality_charge_not_both_zero_ten := h10
  distinctly_charged_quantaBarFiveMatter := hd5
  distinctly_charged_quantaTen := hd10

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.a in table 1 of arXiv:1507.05961. -/
def caseI14a : MatterContent .same :=
  mkOneTenFourFiveBar .same 1 2 (-1) 2 2 (-1) 1

-- #eval println! caseI14a.phenoCharges

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.b in table 1 of arXiv:1507.05961. -/
def caseI14b : MatterContent .same :=
  mkOneTenFourFiveBar .same 3 (-3) (-1) 2 1 0 (-1)

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def caseI14c : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 2 (-2) (-7) 14 6 1 (-9)

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def caseI14c' : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 3 (-2) (-7) 14 6 1 (-9)

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.d in table 1 of arXiv:1507.05961. -/
def caseI14d : MatterContent .same :=
  mkOneTenFourFiveBar .same 3 (-3) 0 0 (-3) (-2) (-1)

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.e in table 1 of arXiv:1507.05961. -/
def caseI14e : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 0 3 (-7) 14 1 (-9) (-4)

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.f in table 1 of arXiv:1507.05961. -/
def caseI14f : MatterContent .nextToNearestNeighbor :=
  mkOneTenFourFiveBar .nextToNearestNeighbor 3 (-3) 6 (-12) (-3) 2 7

/-!

## Two 10d representations and four 5-bar representations

-/

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the two versions of I.2.4.a in table 8 of arXiv:1507.05961. -/
def caseI24a : MatterContent .same where
  quantaBarFiveMatter := {(0, 3, -3), (3, -3, -1)}
  quantaTen := {(1, -1, -3), (2, 1, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the two versions of the I.2.4.a in table 8 of arXiv:1507.05961. -/
def caseI24a' : MatterContent .same where
  quantaTen := {(2, -1, -3), (1, 1, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter := {(0, 3, -3), (3, -3, -1)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b : MatterContent .same where
  quantaTen := {(1, 0, -3), (2, 0, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter := {(0, 2, -1), (3, -2, 1)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b' : MatterContent .same where
  quantaTen := {(1, 0, -3), (2, 0, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter := {(1, 2, -1), (2, -2, 1)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b'' : MatterContent .same where
  quantaTen := {(2, 0, -3), (1, 0, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter := {(0, 2, -1), (3, -2, 1)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- An example of matter content with two 10d representation and 4 5-bar representations.
  This corresponds to one of the four versions of I.2.4.b in table 8 of arXiv:1507.05961. -/
def caseI24b''' : MatterContent .same where
  quantaTen := {(2, 0, -3), (1, 0, -1)}
  qHu := -2
  qHd := 2
  quantaBarFiveMatter := {(1, 2, -1), (2, -2, 1)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-!

## Three 10d representations and four 5-bar representations

-/

/-- An example of matter content with three 10d representations and 4 5-bar representations.
  This corresponds to example I.3.4.a of arXiv:1507.05961 (Eq. A12). -/
def caseI34a : MatterContent .same where
  quantaTen := {(1, 0, -3), (1, 0, -2), (1, 0, -1)}
  qHu := -2
  qHd := 1
  quantaBarFiveMatter := {(0, 3, -1), (3, -3, 0)}
  quantaBarFiveMatter_map_q_subset_allowedBarFiveCharges := by decide
  quantaTen_map_q_subset_allowedTenCharges := by decide
  qHu_mem_allowedBarFiveCharges := by decide
  qHd_mem_allowedBarFiveCharges := by decide
  chirality_charge_not_both_zero_bar_five_matter := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]
  distinctly_charged_quantaBarFiveMatter := by decide
  distinctly_charged_quantaTen := by decide

/-- The finite set of all examples of MatterContent currently defined in PhysLean. -/
def allCases : Finset (Σ I, MatterContent I) :=
  {⟨.same, caseI14a⟩, ⟨.same, caseI14b⟩, ⟨.nearestNeighbor, caseI14c⟩,
  ⟨.nearestNeighbor, caseI14c'⟩, ⟨.same, caseI14d⟩, ⟨.nearestNeighbor, caseI14e⟩,
  ⟨.nextToNearestNeighbor, caseI14f⟩,
  ⟨.same, caseI24a⟩, ⟨.same, caseI24a'⟩,
  ⟨.same, caseI24b⟩, ⟨.same, caseI24b'⟩, ⟨.same, caseI24b''⟩, ⟨.same, caseI24b'''⟩,
  ⟨.same, caseI34a⟩}

lemma allCases_anomalyFree : ∀ 𝓒 ∈ allCases, 𝓒.2.AnomalyFree := by decide

lemma allCases_validMatterSpectrum : ∀ 𝓒 ∈ allCases, 𝓒.2.ValidMatterSpectrum := by decide

lemma allCases_muTermU1Constrained : ∀ 𝓒 ∈ allCases, 𝓒.2.MuTermU1Constrained := by decide

lemma allCases_RParityU1Constrained : ∀ 𝓒 ∈ allCases, 𝓒.2.RParityU1Constrained := by decide

lemma allCases_protonDecayU1Constrained : ∀ 𝓒 ∈ allCases, 𝓒.2.ProtonDecayU1Constrained := by decide

lemma allCases_hasATopYukawa : ∀ 𝓒 ∈ allCases, 𝓒.2.HasATopYukawa := by decide

/-- Not all the examples have a bottom Yukawa. -/
lemma not_allCases_hasABottomYukawa : ¬ ∀ 𝓒 ∈ allCases, 𝓒.2.HasABottomYukawa := by decide

end MatterContent

end SU5U1

end FTheory
