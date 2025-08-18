/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Quanta.FiveQuanta
import PhysLean.StringTheory.FTheory.SU5.Quanta.TenQuanta
import PhysLean.StringTheory.FTheory.SU5.Charges.Viable
/-!

# Quanta of representations

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

-/
namespace FTheory

namespace SU5
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta associated with the representations in a `SU(5) x U(1)` F-theory.
  This contains the value of the charges and the flux intergers `(M, N)` for the
  5-bar matter content and the 10d matter content, and the charges of the `Hd` and
  `Hu` particles (there values of `(M,N)` are not included as they are
  forced to be `(0, 1)` and `(0, -1)` respectively. -/
abbrev Quanta (𝓩 : Type := ℤ) : Type := Option 𝓩 × Option 𝓩 × FiveQuanta 𝓩 × TenQuanta 𝓩

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm Charges

variable {𝓩 : Type}

instance [DecidableEq 𝓩] : DecidableEq (Quanta 𝓩) :=
  haveI : DecidableEq (FiveQuanta 𝓩) := by infer_instance
  inferInstanceAs (DecidableEq (Option 𝓩 × Option 𝓩 × FiveQuanta 𝓩 × TenQuanta 𝓩))

/-- The underlying `Charges` of a `Quanta`. -/
def toCharges [DecidableEq 𝓩] (x : Quanta 𝓩) : Charges 𝓩 :=
  (x.1, x.2.1, x.2.2.1.toCharges.toFinset, x.2.2.2.toCharges.toFinset)

/-!

## Reduce

-/

/-- The reduce of `Quanta` is a new `Quanta` with all the fluxes corresponding to the same
  charge (i.e. represenation) added together. -/
def reduce [DecidableEq 𝓩] (x : Quanta 𝓩) : Quanta 𝓩 :=
  (x.1, x.2.1, x.2.2.1.reduce, x.2.2.2.reduce)

/-!

## Anomaly cancellation conditions

There are two anomaly cancellation conditions in the SU(5)×U(1) model which involve the
`U(1)` charges. These are

- `∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar represenations and the second
  is over all 10d representations.
- `∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar represenations and the
  second is over all 10d representations.

According to arXiv:1401.5084 it is unclear whether this second condition should necessarily be
imposed.

-/

/-- The pair of anomaly cancellation coefficents associated with the `Hd` particle. -/
def HdAnomalyCoefficent [CommRing 𝓩] (qHd : Option 𝓩) : 𝓩 × 𝓩 :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)

/-- The pair of anomaly cancellation coefficents associated with the `Hu` particle. -/
def HuAnomalyCoefficent [CommRing 𝓩] (qHu : Option 𝓩) : 𝓩 × 𝓩 :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)

/-- The anomaly cancellation conditions on quanta making up the fields present in
  the theory. This corresponds to the conditions that:

- `∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar represenations and the second
  is over all 10d representations.
- `∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar represenations and the
  second is over all 10d representations.
-/
def AnomalyCancellation [CommRing 𝓩] (qHd qHu : Option 𝓩) (F : FiveQuanta 𝓩) (T : TenQuanta 𝓩) :
    Prop :=
  HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu + F.anomalyCoefficent +
    T.anomalyCoefficent = (0, 0)

instance [CommRing 𝓩] [DecidableEq 𝓩] :
    Decidable (AnomalyCancellation (𝓩 := 𝓩) qHd qHu F T) :=
  inferInstanceAs (Decidable ((HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu
    + F.anomalyCoefficent + T.anomalyCoefficent) = (0, 0)))

lemma anomalyCoefficent_snd_eq_zero_of_anomalyCancellation [CommRing 𝓩]
    {qHd qHu : Option 𝓩} {F : FiveQuanta 𝓩} {T : TenQuanta 𝓩}
    (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2) = 0 := by
  simp only [← Prod.snd_add]
  rw [h]

/-!

## ofChargesExpand

-/

/-- Given a finite set of charges `c` the `Quanta`
  with fluxes `{(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)}`
  for the 5-bar matter content and fluxes
  `{(1, 0), (1, 0), (1, 0)}` or `{(1, 1), (1, -1), (1, 0)}` for the
  10d matter content, and finite set of charges equal to `c`.

  These quanta reduce to all viable quanta. -/
def ofChargesExpand [DecidableEq 𝓩] (c : Charges 𝓩) : Multiset (Quanta 𝓩) :=
  let Q5s := FiveQuanta.ofChargesExpand c.2.2.1
  let Q10s := TenQuanta.ofChargesExpand c.2.2.2
  Q5s.bind <| fun Q5 =>
  Q10s.map <| fun Q10 =>
    (c.1, c.2.1, Q5, Q10)

end Quanta

end SU5

end FTheory
