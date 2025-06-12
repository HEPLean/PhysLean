/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
import PhysLean.Particles.SuperSymmetry.SU5.Potential
/-!

# Charges assocated with field labels

Given a field label `F`, and a charge `x : Charges`,
we can extract the set of charges associated with that field label.
This is done by the function `ofFieldLabel`, which returns a `Finset ℤ`.

-/

namespace FTheory
namespace SU5U1

namespace Charges
open SuperSymmetry.SU5

/-- Given an `x : Charges`, the charges associated with a given `FieldLabel`. -/
def ofFieldLabel (x : Charges) : FieldLabel → Finset ℤ
  | .fiveBarHd => x.1.toFinset
  | .fiveBarHu => x.2.1.toFinset
  | .fiveBarMatter => x.2.2.1
  | .tenMatter => x.2.2.2
  | .fiveHd => x.1.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveHu => x.2.1.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveMatter => x.2.2.1.map ⟨Neg.neg, neg_injective⟩

@[simp]
lemma mem_ofFieldLabel_fiveHd (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHd ↔ -x ∈ y.ofFieldLabel .fiveBarHd := by
  simp [ofFieldLabel, FieldLabel.fiveHd]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveHu (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHu ↔ -x ∈ y.ofFieldLabel .fiveBarHu := by
  simp [ofFieldLabel, FieldLabel.fiveHu]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveMatter (x : ℤ) (y : Charges) :
    x ∈ y.ofFieldLabel FieldLabel.fiveMatter ↔ -x ∈ y.ofFieldLabel .fiveBarMatter := by
  simp [ofFieldLabel, FieldLabel.fiveBarHd]
  aesop

lemma ofFieldLabel_subset_of_subset {x y : Charges} (h : x ⊆ y) (F : FieldLabel) :
    x.ofFieldLabel F ⊆ y.ofFieldLabel F := by
  rw [subset_def] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases F
  all_goals simp_all [ofFieldLabel]

/-- Two charges are equal if they are equal on all field labels. -/
lemma ext_ofFieldLabel {x y : Charges} (h : ∀ F, x.ofFieldLabel F = y.ofFieldLabel F) :
    x = y := by
  match x, y with
  | (x1, x2, x3, x4), (y1, y2, y3, y4) =>
  have h1 := h FieldLabel.fiveBarHd
  have h2 := h FieldLabel.fiveBarHu
  have h3 := h FieldLabel.fiveBarMatter
  have h4 := h FieldLabel.tenMatter
  clear h
  simp_all [ofFieldLabel]
  rw [← Option.toFinset_inj] at h1 h2
  simp_all

end Charges

end SU5U1
end FTheory
