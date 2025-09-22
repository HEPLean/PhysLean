/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Basic
/-!

# Charges assocated with field labels

Given a field label `F`, and a charge `x : Charges`,
we can extract the set of charges associated with that field label.
This is done by the function `ofFieldLabel`, which returns a `Finset ℤ`.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open SuperSymmetry.SU5

variable {𝓩 : Type} [InvolutiveNeg 𝓩]

/-- Given an `x : Charges`, the charges associated with a given `FieldLabel`. -/
def ofFieldLabel (x : ChargeSpectrum 𝓩) : FieldLabel → Finset 𝓩
  | .fiveBarHd => x.qHd.toFinset
  | .fiveBarHu => x.qHu.toFinset
  | .fiveBarMatter => x.Q5
  | .tenMatter => x.Q10
  | .fiveHd => x.qHd.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveHu => x.qHu.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveMatter => x.Q5.map ⟨Neg.neg, neg_injective⟩

@[simp]
lemma ofFieldLabel_empty (F : FieldLabel) :
    ofFieldLabel (∅ : ChargeSpectrum 𝓩) F = ∅ := by
  cases F
  all_goals
    rfl

lemma ofFieldLabel_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (F : FieldLabel) :
    x.ofFieldLabel F ⊆ y.ofFieldLabel F := by
  rw [subset_def] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases F
  all_goals simp_all [ofFieldLabel]

@[simp]
lemma mem_ofFieldLabel_fiveHd (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHd ↔ -x ∈ y.ofFieldLabel .fiveBarHd := by
  simp [ofFieldLabel]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveHu (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHu ↔ -x ∈ y.ofFieldLabel .fiveBarHu := by
  simp [ofFieldLabel]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveMatter (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveMatter ↔ -x ∈ y.ofFieldLabel .fiveBarMatter := by
  simp [ofFieldLabel]
  aesop

/-- Two charges are equal if they are equal on all field labels. -/
lemma ext_ofFieldLabel {x y : ChargeSpectrum 𝓩} (h : ∀ F, x.ofFieldLabel F = y.ofFieldLabel F) :
    x = y := by
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  have h1 := h FieldLabel.fiveBarHd
  have h2 := h FieldLabel.fiveBarHu
  have h3 := h FieldLabel.fiveBarMatter
  have h4 := h FieldLabel.tenMatter
  clear h
  simp_all [ofFieldLabel]
  rw [← Option.toFinset_inj] at h1 h2
  simp_all

end ChargeSpectrum

end SU5
end SuperSymmetry
