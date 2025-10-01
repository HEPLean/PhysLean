/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Quanta.Basic
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Map
/-!

# Anomaly cancellation

In this module we define the proposition `IsAnomalyFree` on charges, which states
that the charges can be extended to quanta which are anomaly free.

We give the viable charges which are anomaly free for each of the three codimension one
configurations. This is in the lemma `viable_anomalyFree`.

-/
namespace FTheory

namespace SU5

namespace ChargeSpectrum
open SuperSymmetry.SU5
open SuperSymmetry.SU5.ChargeSpectrum
open PotentialTerm
open CodimensionOneConfig
open Tree
open PhysLean

/-!

## Anomaly coefficents of charges

-/

variable {𝓩 : Type}
/-- The condition on a collection of charges `c` that it extends to an anomaly free `Quanta`.
  That anomaly free `Quanta` is not tracked by this proposition. -/
def IsAnomalyFree [DecidableEq 𝓩] [CommRing 𝓩] (c : ChargeSpectrum 𝓩) : Prop :=
  ∃ x ∈ Quanta.ofChargesExpand c, Quanta.AnomalyCancellation x.qHd x.qHu x.F x.T

instance [DecidableEq 𝓩] [CommRing 𝓩] {c : ChargeSpectrum 𝓩} : Decidable (IsAnomalyFree c) :=
  Multiset.decidableExistsMultiset

/-!

## The IsAnomalyFree condition under a map

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
  use QM
  constructor
  · simp [QM, Quanta.ofChargesExpand] at ⊢ h1
    have hqHd := h1.2.2.1
    have hqHu := h1.2.2.2
    subst hqHd hqHu
    simp [ChargeSpectrum.map]
    refine ⟨?_, ?_⟩
    · have h5 := h1.1
      rw [FiveQuanta.mem_ofChargesExpand_iff] at h5 ⊢
      constructor
      · rw [← h5.1]
        simp [FiveQuanta.toCharges]
        rw [← Finset.image_toFinset, ← Finset.image_toFinset, Finset.image_image]
        rfl
      · rw [← h5.2]
        simp [FiveQuanta.toFluxesFive]
    · have h10 := h1.2.1
      rw [TenQuanta.mem_ofChargesExpand_iff] at h10 ⊢
      constructor
      · rw [← h10.1]
        simp [TenQuanta.toCharges]
        rw [← Finset.image_toFinset, ← Finset.image_toFinset, Finset.image_image]
        rfl
      · have hr := h10.2
        rcases hr with hr | hr
        all_goals
          rw [← hr]
          simp [TenQuanta.toFluxesTen]
  · simp at h2
    simp [QM]
    rw [Quanta.AnomalyCancellation]
    simp only [Quanta.HdAnomalyCoefficent_map, RingHom.coe_prodMap, Quanta.HuAnomalyCoefficent_map,
      FiveQuanta.anomalyCoefficent_of_map, TenQuanta.anomalyCoefficent_of_map]
    trans (f.prodMap f) ((Quanta.HdAnomalyCoefficent qHd) +
      (Quanta.HuAnomalyCoefficent qHu) + F5.anomalyCoefficent + F10.anomalyCoefficent)
    · simp [map_add]
    rw [h2]
    exact map_zero _

end map

/-!

## The viable charges which are anomaly free.

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
