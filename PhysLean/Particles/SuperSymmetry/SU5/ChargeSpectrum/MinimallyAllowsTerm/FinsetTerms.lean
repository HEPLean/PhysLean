/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoConstrained
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.Basic
/-!

# Minimally allows a finite set of terms

Given a set of charges `x : Charges` corresponding to charges of the representations
present in the theory, and a finite set of
potential terms `Ts : Finset PotentialTerm`, we say that `x`
minimally allows `Ts` if it allows each term in `Ts` and no proper subset of `x` allows
each term in `Ts`.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]
open SuperSymmetry.SU5
open PotentialTerm

/-- A collection of charges `x : Charges` is said to minimally allow
  a finite set of potential terms `Ts` if it allows
  all terms in `Ts` and no strict subset of it allows all terms in `Ts`. -/
def MinimallyAllowsFinsetTerms (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T

instance (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) :
    Decidable (x.MinimallyAllowsFinsetTerms Ts) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T))

variable {Ts : Finset PotentialTerm} {x : ChargeSpectrum 𝓩}

lemma allowsTerm_of_minimallyAllowsFinsetTerms {T : PotentialTerm}
    (h : x.MinimallyAllowsFinsetTerms Ts) (hT : T ∈ Ts) : x.AllowsTerm T :=
  (h x (self_mem_powerset x)).mp rfl T hT

@[simp]
lemma minimallyAllowsFinsetTerms_singleton {T : PotentialTerm} :
    x.MinimallyAllowsFinsetTerms {T} ↔ x.MinimallyAllowsTerm T := by
  simp [MinimallyAllowsFinsetTerms, MinimallyAllowsTerm]

/-!

## Minimally allows top and bottom Yukawa

-/

/-- The set of charges of the form `(qHd, qHu, {q5}, {-qHd-q5, q10, qHu - q10})`
  This includes every charge which minimally allows for the top and bottom Yukawas. -/
def minTopBottom (S5 S10 : Finset 𝓩) : Multiset (ChargeSpectrum 𝓩) := Multiset.dedup <|
  (S5.val.product <| S5.val.product <| S5.val.product <| S10.val).map
    (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩)

lemma allowsTerm_topYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm topYukawa := by
  simp [minTopBottom] at h
  obtain ⟨qHd, qHu, q5, q10, ⟨hHd, hHu, h5, h10⟩, rfl⟩ := h
  rw [allowsTerm_iff_subset_allowsTermForm]
  simp [allowsTermForm]
  use -qHu, q10
  rw [subset_def]
  simp

lemma allowsTerm_bottomYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm bottomYukawa := by
  simp [minTopBottom] at h
  obtain ⟨qHd, qHu, q5, q10, ⟨hHd, hHu, h5, h10⟩, rfl⟩ := h
  rw [allowsTerm_iff_subset_allowsTermForm]
  simp [allowsTermForm]
  use qHd, q5
  rw [subset_def]
  simp

lemma mem_minTopBottom_of_minimallyAllowsFinsetTerms
    {x : ChargeSpectrum 𝓩} {S5 S10 : Finset 𝓩}
    (h : x.MinimallyAllowsFinsetTerms {topYukawa, bottomYukawa})
    (hx : x ∈ ofFinset S5 S10) :
    x ∈ minTopBottom S5 S10 := by
  simp [minTopBottom]
  have hTop : x.AllowsTerm topYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  have hBottom : x.AllowsTerm bottomYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    rw [allowsTerm_iff_subset_allowsTermForm] at hBottom
    simp [allowsTermForm, subset_def] at hBottom
  | ⟨qHd, none, Q5, Q10⟩ =>
    rw [allowsTerm_iff_subset_allowsTermForm] at hTop
    simp [allowsTermForm, subset_def] at hTop
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
  rw [allowsTerm_iff_subset_allowsTermForm] at hTop hBottom
  simp [allowsTermForm, subset_def] at hTop hBottom
  obtain ⟨n, hn, q10, h10⟩ := hTop
  obtain ⟨q5, h5⟩ := hBottom
  use qHd, qHu, q5, q10
  rw [mem_ofFinset_iff] at hx
  simp at hx
  refine ⟨⟨hx.1, hx.2.1, hx.2.2.1 h5.1, hx.2.2.2 (h10 (Finset.mem_insert_self _ _))⟩, ?_⟩
  refine (h _ ?_).mpr ?_
  · simp [subset_def]
    refine ⟨h5.1, ?_⟩
    refine Finset.insert_subset h5.2 ?_
    refine Finset.insert_subset (h10 ?_) ?_
    · simp
    · refine Finset.singleton_subset_iff.mpr (h10 ?_)
      simp [hn]
  · intro T hT
    fin_cases hT
    · rw [allowsTerm_iff_subset_allowsTermForm]
      simp [allowsTermForm, subset_def]
      use -qHu
      simp only [neg_neg, true_and]
      use q10
      simp
    · rw [allowsTerm_iff_subset_allowsTermForm]
      simp [allowsTermForm, subset_def]

end ChargeSpectrum

end SU5
end SuperSymmetry
