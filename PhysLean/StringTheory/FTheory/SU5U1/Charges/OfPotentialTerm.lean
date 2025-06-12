/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.OfFieldLabel
/-!

# Charges associated with a potential term

Given a potential term `T`, and a charge `x : Charges`,
we can extract the set of charges associated with instances of that potential term.

-/

namespace FTheory
namespace SU5U1

namespace Charges
open SuperSymmetry.SU5
open PotentialTerm

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term. -/
def ofPotentialTerm (x : Charges) (T : PotentialTerm) : Multiset ℤ :=
  let add : Multiset ℤ → Multiset ℤ → Multiset ℤ := fun a b => (a.product b).map
      fun (x, y) => x + y
  (T.toFieldLabel.map fun F => (ofFieldLabel x F).val).foldl add {0}

lemma ofPotentialTerm_subset_of_subset {x y : Charges} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ y.ofPotentialTerm T := by
  have h1 {S1 S2 T1 T2 : Multiset ℤ} (h1 : S1 ⊆ S2) (h2 : T1 ⊆ T2) :
      (S1.product T1) ⊆ S2.product T2 :=
    Multiset.subset_iff.mpr (fun x => by simpa using fun h1' h2' => ⟨h1 h1', h2 h2'⟩)
  rw [subset_def] at h
  cases T
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel]
    repeat'
      apply Multiset.map_subset_map <| Multiset.subset_iff.mpr <|
        h1 _ (Finset.subset_def.mp (ofFieldLabel_subset_of_subset h _))
    simp

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term.

  This is a more explicit form of `PotentialTerm`, which has the benifit that
  it is quick with `decide`, but it is not defined based on more fundamental
  concepts, like `ofPotentialTerm` is. -/
def ofPotentialTerm' (y : Charges) (T : PotentialTerm) : Multiset ℤ :=
  let qHd := y.1
  let qHu := y.2.1
  let Q5 := y.2.2.1
  let Q10 := y.2.2.2
  match T with
  | μ => (qHd.toFinset.product <| qHu.toFinset).val.map (fun x => x.1 - x.2)
  | β => (qHu.toFinset.product <| Q5).val.map (fun x => - x.1 + x.2)
  | Λ => (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 => (qHd.toFinset.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W3 => (qHu.toFinset.product <| Q5.product <| Q5).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2)
  | W4 => (qHd.toFinset.product <| qHu.toFinset.product <| Q5).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2)
  | K1 => (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2 => (qHd.toFinset.product <| qHu.toFinset.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)
  | topYukawa => (qHu.toFinset.product <| Q10.product <| Q10).val.map
    (fun x => -x.1 + x.2.1 + x.2.2)
  | bottomYukawa => (qHd.toFinset.product <| Q5.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2)

lemma ofPotentialTerm_subset_ofPotentialTerm' {x : Charges} (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ x.ofPotentialTerm' T := by
  refine Multiset.subset_iff.mpr (fun n h => ?_)
  simp [ofPotentialTerm] at h
  cases T
  all_goals
    simp [PotentialTerm.toFieldLabel] at h
    obtain ⟨f1, f2, ⟨⟨f3, f4, ⟨h3, f4_mem⟩, rfl⟩, f2_mem⟩, f1_add_f2_eq_zero⟩ := h
  case' μ | β => obtain ⟨rfl⟩ := h3
  case' Λ | W1 | W2 | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨f5, f6, ⟨h4, f6_mem⟩, rfl⟩ := h3
  case' Λ | K1 | K2 | topYukawa | bottomYukawa => obtain ⟨rfl⟩ := h4
  case' W1 | W2 | W3 | W4 => obtain ⟨f7, f8, ⟨rfl, f8_mem⟩, rfl⟩ := h4
  all_goals
    simp [ofPotentialTerm']
    simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
    simp_all [ofFieldLabel]
  case' W1 => use f2, f4, f6, f8
  case' W2 => use f2, f4, f6, f8
  case' W3 => use (-f2), f6, f8
  case' W4 => use f6, (-f4), f8
  case' K1 => use (-f2), f4, f6
  case' K2 => use f4, f6, f2
  case' Λ => use f4, f6, f2
  case' topYukawa => use (-f2), f4, f6
  case' bottomYukawa => use f2, f4, f6
  case' β => use (-f4), f2
  all_goals simp_all
  all_goals omega

lemma ofPotentialTerm'_subset_ofPotentialTerm {x : Charges} (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ x.ofPotentialTerm T := by
  refine Multiset.subset_iff.mpr (fun n h => ?_)
  cases T
  all_goals
    simp [ofPotentialTerm'] at h
    simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product] at h
  case' μ | β =>
    obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
  case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
  case' W1 | W2 =>
    obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
  case' μ => refine ofPotentialTerm_subset_of_subset (x := (q1, q2, ∅, ∅)) ?μSub _ ?μP
  case' β => refine ofPotentialTerm_subset_of_subset (x := (none, q1, {q2}, ∅)) ?βSub _ ?βP
  case' Λ =>
    refine ofPotentialTerm_subset_of_subset (x := (none, none, {q1, q2}, {q3})) ?ΛSub _ ?ΛP
  case' W1 =>
    refine ofPotentialTerm_subset_of_subset (x := (none, none, {q1}, {q2, q3, q4})) ?W1Sub _ ?W1P
  case' W2 =>
    refine ofPotentialTerm_subset_of_subset (x := (q1, none, ∅, {q2, q3, q4})) ?W2Sub _ ?W2P
  case' W3 => refine ofPotentialTerm_subset_of_subset (x := (none, q1, {q2, q3}, ∅)) ?W3Sub _ ?W3P
  case' W4 => refine ofPotentialTerm_subset_of_subset (x := (q1, q2, {q3}, ∅)) ?W4Sub _ ?W4P
  case' K1 =>
    refine ofPotentialTerm_subset_of_subset (x := (none, none, {q1}, {q2, q3}))
      ?K1Sub _ ?K1P
  case' K2 => refine ofPotentialTerm_subset_of_subset (x := (q1, q2, ∅, {q3})) ?K2Sub _ ?K2P
  case' topYukawa =>
    refine ofPotentialTerm_subset_of_subset (x := (none, q1, ∅, {q2, q3}))
      ?topYukawaSub _ ?topYukawaP
  case' bottomYukawa =>
    refine ofPotentialTerm_subset_of_subset (x := (q1, none, {q2}, {q3}))
      ?bottomYukawaSub _ ?bottomYukawaP
  case' μSub | βSub | ΛSub | W1Sub | W2Sub | W3Sub | W4Sub | K1Sub | K2Sub |
      topYukawaSub | bottomYukawaSub =>
    rw [subset_def]
    simp_all [Finset.insert_subset]
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel, ofFieldLabel]
  any_goals omega
  case' ΛP =>
    use - q3 + n
    simp only [neg_add_cancel_comm, and_true]
    use - q1 - q3 + n, q1
    apply And.intro ?_ (by omega)
    simp only [true_or, and_true]
    use 0
    simp only [true_and, zero_add, exists_eq_right]
    omega
  case' W3P =>
    use 2 * q1 + n
    apply And.intro ?_ (by omega)
    use - q2 + 2 * q1 + n, q2
    apply And.intro ?_ (by omega)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    omega
  case' K1P =>
    use q1 + n
    apply And.intro ?_ (by omega)
    use q1 - q2 + n, q2
    apply And.intro ?_ (by omega)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    omega
  case' topYukawaP =>
    use q1 + n
    apply And.intro ?_ (by omega)
    use q1 - q2 + n, q2
    apply And.intro ?_ (by omega)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    omega
  case' W1P | W2P =>
    use - q1 + n
    apply And.intro ?_ (by omega)
    use - q1 - q2 + n, q2
    apply And.intro ?_ (by omega)
    simp only [true_or, and_true]
    use -q1 - q2 - q3 + n, q3
    apply And.intro ?_ (by omega)
    simp only [true_or, or_true, and_true]
    use 0, q4
    simp only [or_true, and_self, zero_add, true_and]
    omega

lemma mem_ofPotentialTerm_iff_mem_ofPotentialTerm {T : PotentialTerm} {n : ℤ} {y : Charges} :
    n ∈ y.ofPotentialTerm T ↔ n ∈ y.ofPotentialTerm' T := by
  constructor
  · exact fun h => ofPotentialTerm_subset_ofPotentialTerm' T h
  · exact fun h => ofPotentialTerm'_subset_ofPotentialTerm T h

end Charges

end SU5U1
end FTheory
