/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel
import Mathlib.Tactic.Abel
/-!

# Charges associated with a potential term

Given a potential term `T`, and a charge `x : Charges`,
we can extract the set of charges associated with instances of that potential term.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term. -/
def ofPotentialTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let add : Multiset 𝓩 → Multiset 𝓩 → Multiset 𝓩 := fun a b => (a.product b).map
      fun (x, y) => x + y
  (T.toFieldLabel.map fun F => (ofFieldLabel x F).val).foldl add {0}

lemma ofPotentialTerm_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ y.ofPotentialTerm T := by
  have h1 {S1 S2 T1 T2 : Multiset 𝓩} (h1 : S1 ⊆ S2) (h2 : T1 ⊆ T2) :
      (S1.product T1) ⊆ S2.product T2 :=
    Multiset.subset_iff.mpr (fun x => by simpa using fun h1' h2' => ⟨h1 h1', h2 h2'⟩)
  rw [subset_def] at h
  cases T
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel]
    repeat'
      apply Multiset.map_subset_map <| Multiset.subset_iff.mpr <|
        h1 _ (Finset.subset_def.mp (ofFieldLabel_mono h _))
    simp

@[simp]
lemma ofPotentialTerm_empty (T : PotentialTerm) :
    ofPotentialTerm (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    rfl

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term.

  This is a more explicit form of `PotentialTerm`, which has the benifit that
  it is quick with `decide`, but it is not defined based on more fundamental
  concepts, like `ofPotentialTerm` is. -/
def ofPotentialTerm' (y : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let qHd := y.1
  let qHu := y.2.1
  let Q5 := y.2.2.1
  let Q10 := y.2.2.2
  match T with
  | μ =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => {qHd - qHu}
  | β =>
    match qHu with
    | none => ∅
    | some qHu => Q5.val.map (fun x => - qHu + x)
  | Λ => (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 =>
    match qHd with
    | none => ∅
    | some qHd =>
      (Q10.product <| Q10.product <| Q10).val.map (fun x => qHd + x.1 + x.2.1 + x.2.2)
  | W3 =>
    match qHu with
    | none => ∅
    | some qHu => (Q5.product <| Q5).val.map (fun x => -qHu - qHu + x.1 + x.2)
  | W4 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q5.val.map (fun x => qHd - qHu - qHu + x)
  | K1 => (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q10.val.map (fun x => qHd + qHu + x)
  | topYukawa =>
    match qHu with
    | none => ∅
    | some qHu => (Q10.product <| Q10).val.map (fun x => - qHu + x.1 + x.2)
  | bottomYukawa =>
    match qHd with
    | none => ∅
    | some qHd => (Q5.product <| Q10).val.map (fun x => qHd + x.1 + x.2)

lemma ofPotentialTerm'_μ_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' μ =
    (x.1.toFinset.product <| x.2.1.toFinset).val.map (fun x => x.1 - x.2) := by
  match x with
  | (none, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_β_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' β =
    (x.2.1.toFinset.product <| x.2.2.1).val.map (fun x => - x.1 + x.2) := by
  match x with
  | (qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W2 = (x.1.toFinset.product <|
      x.2.2.2.product <| x.2.2.2.product <| x.2.2.2).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := by
  match x with
  | (none, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W3_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W3 = (x.2.1.toFinset.product <| x.2.2.1.product <| x.2.2.1).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2) := by
  match x with
  | (qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W4_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W4 = (x.1.toFinset.product <|
      x.2.1.toFinset.product <| x.2.2.1).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2) := by
  match x with
  | (none, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_K2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' K2 = (x.1.toFinset.product <|
      x.2.1.toFinset.product <| x.2.2.2).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | (none, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_topYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' topYukawa = (x.2.1.toFinset.product <|
      x.2.2.2.product <| x.2.2.2).val.map
    (fun x => -x.1 + x.2.1 + x.2.2) := by
  match x with
  | (qHd, none, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (qHd, some qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_bottomYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' bottomYukawa = (x.1.toFinset.product <|
      x.2.2.1.product <| x.2.2.2).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | (none, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']
  | (some qHd, qHu, Q5, Q10) =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm_subset_ofPotentialTerm' {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
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
    try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset]
    try simp [ofPotentialTerm']
    simp only [SProd.sprod, Multiset.mem_product]
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
  all_goals
    rw [← f1_add_f2_eq_zero]
    abel

lemma ofPotentialTerm'_subset_ofPotentialTerm [DecidableEq 𝓩] {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ x.ofPotentialTerm T := by
  refine Multiset.subset_iff.mpr (fun n h => ?_)
  cases T
  all_goals
    try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset] at h
    try simp [ofPotentialTerm'] at h
    simp only [SProd.sprod, Multiset.mem_product] at h
  case' μ | β =>
    obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
  case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
  case' W1 | W2 =>
    obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
  case' μ => refine ofPotentialTerm_mono (x := (q1, q2, ∅, ∅)) ?μSub _ ?μP
  case' β => refine ofPotentialTerm_mono (x := (none, q1, {q2}, ∅)) ?βSub _ ?βP
  case' Λ =>
    refine ofPotentialTerm_mono (x := (none, none, {q1, q2}, {q3})) ?ΛSub _ ?ΛP
  case' W1 =>
    refine ofPotentialTerm_mono (x := (none, none, {q1}, {q2, q3, q4})) ?W1Sub _ ?W1P
  case' W2 =>
    refine ofPotentialTerm_mono (x := (q1, none, ∅, {q2, q3, q4})) ?W2Sub _ ?W2P
  case' W3 => refine ofPotentialTerm_mono (x := (none, q1, {q2, q3}, ∅)) ?W3Sub _ ?W3P
  case' W4 => refine ofPotentialTerm_mono (x := (q1, q2, {q3}, ∅)) ?W4Sub _ ?W4P
  case' K1 =>
    refine ofPotentialTerm_mono (x := (none, none, {q1}, {q2, q3}))
      ?K1Sub _ ?K1P
  case' K2 => refine ofPotentialTerm_mono (x := (q1, q2, ∅, {q3})) ?K2Sub _ ?K2P
  case' topYukawa =>
    refine ofPotentialTerm_mono (x := (none, q1, ∅, {q2, q3}))
      ?topYukawaSub _ ?topYukawaP
  case' bottomYukawa =>
    refine ofPotentialTerm_mono (x := (q1, none, {q2}, {q3}))
      ?bottomYukawaSub _ ?bottomYukawaP
  case' μSub | βSub | ΛSub | W1Sub | W2Sub | W3Sub | W4Sub | K1Sub | K2Sub |
      topYukawaSub | bottomYukawaSub =>
    rw [subset_def]
    simp_all [Finset.insert_subset]
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel, ofFieldLabel]
  case' ΛP =>
    use - q3 + n
    simp only [neg_add_cancel_comm, and_true]
    use - q1 - q3 + n, q1
    apply And.intro ?_ (by abel)
    simp only [true_or, and_true]
    use 0
    simp only [true_and, zero_add, exists_eq_right]
    right
    rw [← q_sum]
    abel
  case' W3P =>
    use 2 • q1 + n
    apply And.intro ?_ (by abel)
    use - q2 + 2 • q1 + n, q2
    apply And.intro ?_ (by abel)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    rw [← q_sum]
    abel
  case' K1P =>
    use q1 + n
    apply And.intro ?_ (by abel)
    use q1 - q2 + n, q2
    apply And.intro ?_ (by abel)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    rw [← q_sum]
    abel
  case' topYukawaP =>
    use q1 + n
    apply And.intro ?_ (by abel)
    use q1 - q2 + n, q2
    apply And.intro ?_ (by abel)
    simp only [true_or, and_true]
    use 0, q3
    simp only [or_true, and_self, zero_add, true_and]
    rw [← q_sum]
    abel
  case' W1P | W2P =>
    use - q1 + n
    apply And.intro ?_ (by abel)
    use - q1 - q2 + n, q2
    apply And.intro ?_ (by abel)
    simp only [true_or, and_true]
    use -q1 - q2 - q3 + n, q3
    apply And.intro ?_ (by abel)
    simp only [true_or, or_true, and_true]
    use 0, q4
    simp only [or_true, and_self, zero_add, true_and]
    rw [← q_sum]
    abel
  all_goals
    rw [← q_sum]
    try abel

lemma mem_ofPotentialTerm_iff_mem_ofPotentialTerm [DecidableEq 𝓩]
    {T : PotentialTerm} {n : 𝓩} {y : ChargeSpectrum 𝓩} :
    n ∈ y.ofPotentialTerm T ↔ n ∈ y.ofPotentialTerm' T := by
  constructor
  · exact fun h => ofPotentialTerm_subset_ofPotentialTerm' T h
  · exact fun h => ofPotentialTerm'_subset_ofPotentialTerm T h

lemma ofPotentialTerm'_mono [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ y.ofPotentialTerm' T := by
  intro i
  rw [← mem_ofPotentialTerm_iff_mem_ofPotentialTerm, ← mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  exact fun a => ofPotentialTerm_mono h T a

@[simp]
lemma ofPotentialTerm'_empty (T : PotentialTerm) :
    ofPotentialTerm' (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    simp [ofPotentialTerm']

end ChargeSpectrum

end SU5
end SuperSymmetry
