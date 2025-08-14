/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.FiveQuanta
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.TenQuanta
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Viable
/-!

# Quanta of representations

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

-/
namespace FTheory

namespace SU5U1
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta associated with the representations in a `SU(5) x U(1)` F-theory.
  This contains the value of the charges and the flux intergers `(M, N)` for the
  5-bar matter content and the 10d matter content, and the charges of the `Hd` and
  `Hu` particles (there values of `(M,N)` are not included as they are
  forced to be `(0, 1)` and `(0, -1)` respectively. -/
abbrev Quanta : Type := Option ℤ × Option ℤ × FiveQuanta × TenQuanta

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm Charges

instance : DecidableEq Quanta := instDecidableEqProd

/-- The underlying `Charges` of a `Quanta`. -/
def toCharges (x : Quanta) : Charges :=
  (x.1, x.2.1, x.2.2.1.toCharges.toFinset, x.2.2.2.toCharges.toFinset)

/-!

## Reduce

-/

/-- The reduce of `Quanta` is a new `Quanta` with all the fluxes corresponding to the same
  charge (i.e. represenation) added together.-/
def reduce (x : Quanta) : Quanta :=
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
def HdAnomalyCoefficent (qHd : Option ℤ) : ℤ × ℤ :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)

/-- The pair of anomaly cancellation coefficents associated with the `Hu` particle. -/
def HuAnomalyCoefficent (qHu : Option ℤ) : ℤ × ℤ :=
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
def AnomalyCancellation (qHd qHu : Option ℤ) (F : FiveQuanta) (T : TenQuanta) : Prop :=
  HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu + F.anomalyCoefficent +
    T.anomalyCoefficent = (0, 0)

instance : Decidable (AnomalyCancellation qHd qHu F T) :=
  inferInstanceAs (Decidable ((HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu
    + F.anomalyCoefficent + T.anomalyCoefficent) = (0, 0)))

lemma anomalyCoefficent_snd_eq_zero_of_anomalyCancellation
    {qHd qHu : Option ℤ} {F : FiveQuanta} {T : TenQuanta} (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2) = 0 := by
  trans ((HdAnomalyCoefficent qHd)+ (HuAnomalyCoefficent qHu)
    + (F.anomalyCoefficent) + (T.anomalyCoefficent)).2
  · simp
  rw [h]

lemma five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation
    {qHd qHu : Option ℤ} {F : FiveQuanta} {T : TenQuanta} (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2) % 3 = 0 := by
  trans ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2) % 3
  swap
  · rw [anomalyCoefficent_snd_eq_zero_of_anomalyCancellation h]
    simp
  simp [TenQuanta.anomalyCoefficent]

/-!

## ofChargesExpand

-/

/-- Given a finite set of charges `c` the `Quanta`
  with fluxes `{(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)}`
  for the 5-bar matter content and fluxes
  `{(1, 0), (1, 0), (1, 0)}` or `{(1, 1), (1, -1), (1, 0)}` for the
  10d matter content, and finite set of charges equal to `c`.

  These quanta reduce to all viable quanta. -/
def ofChargesExpand (c : Charges) : Multiset Quanta :=
  let Q5s := FiveQuanta.ofChargesExpand c.2.2.1
  let Q10s := TenQuanta.ofChargesExpand c.2.2.2
  Q5s.bind <| fun Q5 =>
  Q10s.map <| fun Q10 =>
    (c.1, c.2.1, Q5, Q10)

end Quanta

end SU5U1

end FTheory
