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
structure Quanta (𝓩 : Type := ℤ) where
  qHd : Option 𝓩
  qHu : Option 𝓩
  F : FiveQuanta 𝓩
  T : TenQuanta 𝓩

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm ChargeSpectrum

variable {𝓩 : Type}

@[ext]
lemma ext {𝓩 : Type} {x y : Quanta 𝓩} (h1 : x.qHd = y.qHd) (h2 : x.qHu = y.qHu)
    (h3 : x.F = y.F) (h4 : x.T = y.T) : x = y := by
  cases x; cases y;
  simp_all

instance [DecidableEq 𝓩] : DecidableEq (Quanta 𝓩) := fun x y =>
  decidable_of_iff (x.qHd = y.qHd ∧ x.qHu = y.qHu ∧ x.F = y.F ∧ x.T = y.T) Quanta.ext_iff.symm



/-- The underlying `ChargeSpectrum` of a `Quanta`. -/
def toCharges [DecidableEq 𝓩] (x : Quanta 𝓩) : ChargeSpectrum 𝓩 where
  qHd := x.qHd
  qHu := x.qHu
  Q5 := x.F.toCharges.toFinset
  Q10 := x.T.toCharges.toFinset

lemma toCharges_qHd [DecidableEq 𝓩] (x : Quanta 𝓩) : (toCharges x).qHd = x.qHd := rfl

lemma toCharges_qHu [DecidableEq 𝓩] (x : Quanta 𝓩) : (toCharges x).qHu = x.qHu := rfl
/-!

## Reduce

-/

/-- The reduce of `Quanta` is a new `Quanta` with all the fluxes corresponding to the same
  charge (i.e. represenation) added together. -/
def reduce [DecidableEq 𝓩] (x : Quanta 𝓩) : Quanta 𝓩 where
  qHd := x.qHd
  qHu := x.qHu
  F := x.F.reduce
  T := x.T.reduce

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

@[simp]
lemma HdAnomalyCoefficent_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (qHd : Option 𝓩) :
    HdAnomalyCoefficent (qHd.map f) = (f.prodMap f) (HdAnomalyCoefficent qHd) := by
  match qHd with
  | none => simp [HdAnomalyCoefficent]
  | some qHd => simp [HdAnomalyCoefficent]

/-- The pair of anomaly cancellation coefficents associated with the `Hu` particle. -/
def HuAnomalyCoefficent [CommRing 𝓩] (qHu : Option 𝓩) : 𝓩 × 𝓩 :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)

@[simp]
lemma HuAnomalyCoefficent_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (qHu : Option 𝓩) :
    HuAnomalyCoefficent (qHu.map f) = (f.prodMap f) (HuAnomalyCoefficent qHu) := by
  match qHu with
  | none => simp [HuAnomalyCoefficent]
  | some qHu => simp [HuAnomalyCoefficent]

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

instance {qHd qHu F T} [CommRing 𝓩] [DecidableEq 𝓩] :
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
def liftCharge [DecidableEq 𝓩] (c : ChargeSpectrum 𝓩) : Multiset (Quanta 𝓩) :=
  let Q5s := FiveQuanta.liftCharge c.Q5
  let Q10s := TenQuanta.liftCharge c.Q10
  Q5s.bind <| fun Q5 =>
  Q10s.map <| fun Q10 =>
    ⟨c.qHd, c.qHu, Q5, Q10⟩

lemma mem_liftCharge_iff [DecidableEq 𝓩] {c : ChargeSpectrum 𝓩}
    {x : Quanta 𝓩} :
    x ∈ liftCharge c ↔ x.qHd = c.qHd ∧ x.qHu = c.qHu ∧
    x.F ∈ FiveQuanta.liftCharge c.Q5 ∧ x.T ∈ TenQuanta.liftCharge c.Q10:= by
  simp [liftCharge, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · rintro ⟨Q5, h1, Q10, h2, rfl⟩
    simp_all
  · intro h
    use x.F
    simp_all
    use x.T
    simp_all
    rw [← h.1, ← h.2.1]

end Quanta

end SU5

end FTheory
