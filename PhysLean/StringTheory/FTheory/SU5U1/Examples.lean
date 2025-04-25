/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Basic
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
    (hqHu : - qHu ∈ I.allowedBarFiveCharges:= by decide)
    (hqHd : qHd ∈ I.allowedBarFiveCharges:= by decide)
    (hq5₁ : q5₁ ∈ I.allowedBarFiveCharges:= by decide)
    (hq5₂ : q5₂ ∈ I.allowedBarFiveCharges:= by decide)
    (h5 : ∀ a ∈ ({(0, -1, ⟨-qHu, hqHu⟩), (0, 1, ⟨qHd, hqHd⟩),
      (M, N, ⟨q5₁, hq5₁⟩), (3 - M, - N, ⟨q5₂, hq5₂⟩)} :
      Multiset (QuantaBarFive I)), a.M = 0 → a.N ≠ 0 := by decide)
    (h10 :  ∀ a ∈ ({(3, 0, ⟨q10, hq10⟩)} :
      Multiset (QuantaTen I)), a.M = 0 → a.N ≠ 0 := by decide) :
    MatterContent I where
  quantaTen := {(3, 0, ⟨q10, hq10⟩)}
  quantaBarFive := {(0, -1, ⟨- qHu, hqHu⟩), (0, 1, ⟨qHd, hqHd⟩), (M , N, ⟨q5₁, hq5₁⟩),
    (3 - M, - N, ⟨q5₂, hq5₂⟩)}
  chirality_charge_not_both_zero_bar_five := h5
  chirality_charge_not_both_zero_ten := h10

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.a in table 1 of arXiv:1507.05961. -/
def exampleI14a : MatterContent .same :=
  mkOneTenFourFiveBar .same 1 2 (-1) 2 2 (-1) 1

lemma exampleI14a_anomalyFree : exampleI14a.AnomalyFree := by
  decide

lemma exampleI14a_validMatterSpectrum : exampleI14a.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.b in table 1 of arXiv:1507.05961. -/
def exampleI14b : MatterContent .same :=
  mkOneTenFourFiveBar .same 3 (-3) (-1) 2 1 0 (-1)

lemma exampleI14b_anomalyFree : exampleI14b.AnomalyFree := by
  decide

lemma exampleI14b_validMatterSpectrum : exampleI14b.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def exampleI14c : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 2 (-2) (-7) 14 6 1 (-9)

lemma exampleI14c_anomalyFree : exampleI14c.AnomalyFree := by
  decide

lemma exampleI14c_validMatterSpectrum : exampleI14c.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to one-version of example I.1.4.c in table 1 of arXiv:1507.05961. -/
def exampleI14c' : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 3 (-2) (-7) 14 6 1 (-9)

lemma exampleI14c'_anomalyFree : exampleI14c.AnomalyFree := by
  decide

lemma exampleI14c'_validMatterSpectrum : exampleI14c.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.d in table 1 of arXiv:1507.05961. -/
def exampleI14d : MatterContent .same :=
  mkOneTenFourFiveBar .same 3 (-3) 0 0 (-3) (-2) (-1)

lemma exampleI14d_anomalyFree : exampleI14d.AnomalyFree := by
  decide

lemma exampleI14d_validMatterSpectrum : exampleI14d.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.e in table 1 of arXiv:1507.05961. -/
def exampleI14e : MatterContent .nearestNeighbor :=
  mkOneTenFourFiveBar .nearestNeighbor 0 3 (-7) 14 1 (-9) (-4)

lemma exampleI14e_anomalyFree : exampleI14e.AnomalyFree := by
  decide

lemma exampleI14e_validMatterSpectrum : exampleI14e.ValidMatterSpectrum := by
  decide

/-- An example of matter content with one 10d representation and 4 5-bar representations.
  This corresponds to example I.1.4.f in table 1 of arXiv:1507.05961. -/
def exampleI14f : MatterContent .nextToNearestNeighbor :=
  mkOneTenFourFiveBar .nextToNearestNeighbor 3 (-3) 6 (-12) (-3) 2 7

lemma exampleI14f_anomalyFree : exampleI14f.AnomalyFree := by
  decide

lemma exampleI14f_validMatterSpectrum : exampleI14f.ValidMatterSpectrum := by
  decide

/-!

## Three 10d representations and four 5-bar representations

-/


/-- An example of matter content with three 10d representations and 4 5-bar representations.
  This corresponds to example I.3.4.a of arXiv:1507.05961 (Eq. A12). -/
def exampleI34a : MatterContent .same where
  quantaTen := {(1, 0, ⟨-3, by decide⟩), (1, 0, ⟨-2, by decide⟩), (1, 0, ⟨-1, by decide⟩)}
  quantaBarFive := {(0, -1, ⟨-2, by decide⟩), (0, 1, ⟨1, by decide⟩),
    (0, 3, ⟨-1, by decide⟩), (3, -3, ⟨0, by decide⟩)}
  chirality_charge_not_both_zero_bar_five := by
    simp [QuantaBarFive.N]
  chirality_charge_not_both_zero_ten := by
    simp [QuantaTen.N, QuantaTen.M]

lemma exampleI34a_anomalyFree : exampleI34a.AnomalyFree := by
  decide

lemma exampleI34a_validMatterSpectrum : exampleI34a.ValidMatterSpectrum := by
  decide

end MatterContent

end SU5U1

end FTheory
