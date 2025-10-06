/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Quanta.Basic
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Map
/-!

# Anomaly cancellation

## i. Overview

In this module we do two things. The first is to define a proposition `IsAnomalyFree`
on a `ChargeSpectrum` which states that the charge spectrum can be lifted
to an anomaly-free `Quanta` with fluxes which do not have exotics.

We then find all the viable charges given a configuration of the sections in codimension one
fiber `CodimensionOneConfig` that can be lifted to an anomaly-free `Quanta` with fluxes
which do not have exotics.

## ii. Key results

- `IsAnomalyFree` : The proposition on a `ChargeSpectrum` that it can be lifted to an
  anomaly-free `Quanta` with fluxes which do not have exotics.
- `viable_anomalyFree` : The viable charges given a configuration of the sections
  in codimension one fiber `CodimensionOneConfig` which can be lifted to an anomaly-free
  `Quanta` with fluxes which do not have exotics.

## iii. Table of contents

- A. Charge spectrum which lift to anomaly free quanta
  - A.1. Decidability of the proposition
  - A.2. The proposition is preserved under mappings of charge spectra
- B. The viable charges which lift to anomaly free quanta

## iv. References

There are no known references for the material in this section.

-/
namespace FTheory

namespace SU5

namespace ChargeSpectrum
open SuperSymmetry.SU5
open SuperSymmetry.SU5.ChargeSpectrum
open PotentialTerm
open CodimensionOneConfig
open PhysLean

/-!

## A. Charge spectrum which lift to anomaly free quanta

-/

variable {𝓩 : Type}
/-- The condition on a collection of charges `c` that it extends to an anomaly free `Quanta`.
  That anomaly free `Quanta` is not tracked by this proposition. -/
def IsAnomalyFree [DecidableEq 𝓩] [CommRing 𝓩] (c : ChargeSpectrum 𝓩) : Prop :=
  ∃ x ∈ Quanta.liftCharge c, Quanta.AnomalyCancellation x.qHd x.qHu x.F x.T

/-!

### A.1. Decidability of the proposition

-/

instance [DecidableEq 𝓩] [CommRing 𝓩] {c : ChargeSpectrum 𝓩} : Decidable (IsAnomalyFree c) :=
  Multiset.decidableExistsMultiset

/-!

### A.2. The proposition is preserved under mappings of charge spectra

-/

section map

variable {𝓩 𝓩1 : Type} [DecidableEq 𝓩1] [DecidableEq 𝓩][CommRing 𝓩1] [CommRing 𝓩]

lemma isAnomalyFree_map (f : 𝓩 →+* 𝓩1) {c : ChargeSpectrum 𝓩}
    (h : IsAnomalyFree c) : IsAnomalyFree (c.map (f.toAddMonoidHom)) := by
  obtain ⟨Q, h1, h2⟩ := h
  match Q with
  | ⟨qHd, qHu, F5, F10⟩ =>
  let QM : Quanta 𝓩1 := ⟨Option.map f qHd, Option.map f qHu, F5.map fun y => (f y.1, y.2),
    F10.map fun y => (f y.1, y.2)⟩
  use QM.reduce
  constructor
  · rw [Quanta.mem_liftCharge_iff] at ⊢ h1
    simp [Quanta.reduce, QM] at ⊢ h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [ChargeSpectrum.map, h1.1]
    · simp [ChargeSpectrum.map, h1.2]
    · exact FiveQuanta.map_liftCharge _ _ _ h1.2.2.1
    · exact TenQuanta.map_liftCharge _ _ _ h1.2.2.2
  · simp at h2
    simp only [Quanta.AnomalyCancellation, Quanta.reduce, FiveQuanta.anomalyCoefficent_of_reduce,
      FiveQuanta.anomalyCoefficent_of_map, RingHom.coe_prodMap,
      TenQuanta.anomalyCoefficent_of_reduce, TenQuanta.anomalyCoefficent_of_map, QM]
    trans (f.prodMap f) ((Quanta.HdAnomalyCoefficent qHd) +
      (Quanta.HuAnomalyCoefficent qHu) + F5.anomalyCoefficent + F10.anomalyCoefficent)
    · simp [map_add]
    rw [h2]
    exact map_zero _

end map

/-!

## B. The viable charges which lift to anomaly free quanta

-/

set_option maxRecDepth 2000 in
/-- The viable charges which are anomaly free. -/
lemma viable_anomalyFree (I : CodimensionOneConfig) :
    (viableCharges I).filter IsAnomalyFree =
    (match I with
    | .same => {⟨some 2, some (-2), {-1, 1}, {-1}⟩, ⟨some (-2), some 2, {-1, 1}, {1}⟩}
    | .nearestNeighbor => {⟨some 6, some (-14), {-9, 1}, {-7}⟩}
    | .nextToNearestNeighbor => ∅) := by
  revert I
  decide

end ChargeSpectrum

end SU5

end FTheory
