/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Basic
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.Basic
/-!

## Equivalence class on Tensor Trees

This file contains the basic node identities for tensor trees.
More complicated identities appear in there own files.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open PhysLean.Fin
open TensorProduct

namespace TensorTree

variable {k : Type} [CommRing k] {S : TensorSpecies k}

/-- The relation `tensorRel` on `TensorTree S c` is defined such that `tensorRel t1 t2` is true
  if `t1` and `t2` have the same underlying tensors. -/
def tensorRel {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) : Prop := t1.tensor = t2.tensor

lemma tensorRel_refl {n} {c : Fin n → S.C} (t : TensorTree S c) : tensorRel t t := rfl

lemma tensorRel_symm {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    tensorRel t1 t2 → tensorRel t2 t1 :=
  Eq.symm

lemma tensorRel_trans {n} {c : Fin n → S.C} {t1 t2 t3 : TensorTree S c} :
    tensorRel t1 t2 → tensorRel t2 t3 → tensorRel t1 t3 := Eq.trans

lemma tensorRel_equivalence {n} (c : Fin n → S.C) :
    Equivalence (tensorRel (c := c) (S := S)) :=
  { refl := tensorRel_refl,
    symm := tensorRel_symm,
    trans := tensorRel_trans}

instance tensorTreeSetoid {n} (c : Fin n → S.C) : Setoid (TensorTree S c) :=
  Setoid.mk (tensorRel (c := c) (S := S)) (tensorRel_equivalence c)

/-- The equivalence classes of `TensorTree` under the relation `tensorRel`. -/
def _root_.TensorSpecies.TensorTreeQuot (S : TensorSpecies k) {n} (c : Fin n → S.C) : Type :=
    Quot (tensorRel (c := c))

namespace TensorTreeQuot

/-- The projection from `TensorTree` down to `TensorTreeQuot`. -/
def ι {n} {c : Fin n → S.C} (t : TensorTree S c) : S.TensorTreeQuot c := Quot.mk _ t

lemma ι_surjective {n} {c : Fin n → S.C} : Function.Surjective (ι (c := c)) := by
  simp only [Function.Surjective]
  exact fun b => Quotient.exists_rep b

lemma ι_apply_eq_iff_tensorRel {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    ι t1 = ι t2 ↔ tensorRel t1 t2 := by
  simp only [ι]
  rw [Equivalence.quot_mk_eq_iff (tensorRel_equivalence c)]

lemma ι_apply_eq_iff_tensor_apply_eq {n} {c : Fin n → S.C} {t1 t2 : TensorTree S c} :
    ι t1 = ι t2 ↔ t1.tensor = t2.tensor := by
  rw [ι_apply_eq_iff_tensorRel]
  simp [tensorRel]

/-!

## Addition and smul

-/

/-- The addition of two equivalence classes of tensor trees. -/
def addQuot {n} {c : Fin n → S.C} :
    S.TensorTreeQuot c → S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift₂ (fun t1 t2 => ι (t1.add t2)) ?_ ?_
  · intro t1 t2  t3 h1
    simp only [tensorRel] at h1
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_tensor, add_tensor, h1]
  · intro t1 t2 t3 h1
    simp only [tensorRel] at h1
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_tensor, add_tensor, h1]

lemma ι_add_eq_addQuot {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) :
    ι (t1.add t2) = addQuot (ι t1) (ι t2) := rfl

/-- The scalar multiplication of an equivalence classes of tensor trees. -/
def smulQuot {n} {c : Fin n → S.C} (r : k) :
    S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift (fun t => ι (smul r t)) ?_
  · intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [smul_tensor, smul_tensor, h]

lemma ι_smul_eq_smulQuot {n} {c : Fin n → S.C} (r : k) (t : TensorTree S c) :
    ι (smul r t) = smulQuot r (ι t) := rfl

noncomputable instance {n} (c : Fin n → S.C) : AddCommMonoid (S.TensorTreeQuot c) where
  add := addQuot
  zero := ι zeroTree
  nsmul := fun n t => smulQuot (n : k) t
  add_assoc := by
    intro a b c
    obtain ⟨a, rfl⟩ := ι_surjective a
    obtain ⟨b, rfl⟩ := ι_surjective b
    obtain ⟨c, rfl⟩ := ι_surjective c
    change addQuot (addQuot (ι a) (ι b)) (ι c) = addQuot (ι a) (addQuot (ι b) (ι c))
    rw [← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ← ι_add_eq_addQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [add_assoc]
  zero_add := by
    intro a
    obtain ⟨a, rfl⟩ := ι_surjective a
    change addQuot (ι zeroTree) (ι a) = _
    rw [← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.zero_add]
  add_zero := by
    intro a
    obtain ⟨a, rfl⟩ := ι_surjective a
    change addQuot (ι a) (ι zeroTree) = _
    rw [← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.add_zero]
  add_comm := by
    intro a b
    obtain ⟨a, rfl⟩ := ι_surjective a
    obtain ⟨b, rfl⟩ := ι_surjective b
    change addQuot (ι a) (ι b) = addQuot (ι b) (ι a)
    rw [← ι_add_eq_addQuot, ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    rw [add_comm]
  nsmul_zero t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp only [Nat.cast_zero]
    change smulQuot ((0 : k)) (ι t) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [zero_smul]
  nsmul_succ n t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    simp only [Nat.cast_add, Nat.cast_one]
    change smulQuot ((n: k) + 1) (ι t) = addQuot (smulQuot (n : k) (ι t)) (ι t)
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot, ← ι_add_eq_addQuot,
      ι_apply_eq_iff_tensor_apply_eq]
    simp only [smul_tensor, add_tensor]
    rw [add_smul]
    simp

instance {n} {c : Fin n → S.C} : Module k (S.TensorTreeQuot c) where
  smul r t := smulQuot r t
  one_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (1 : k) (ι t) = ι t
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [TensorTree.smul_one]
  mul_smul r s t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (r * s) (ι t) = smulQuot r (smulQuot s (ι t))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,  ← ι_smul_eq_smulQuot,
      ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, mul_smul]
  smul_add r t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    change smulQuot r (addQuot (ι t1) (ι t2)) = addQuot (smulQuot r (ι t1)) (smulQuot r (ι t2))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,  ← ι_add_eq_addQuot, ← ι_add_eq_addQuot,
      ← ι_smul_eq_smulQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, add_tensor]
  smul_zero a := by
    change smulQuot (a : k) (ι zeroTree) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, zero_smul]
  add_smul r s t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (r + s) (ι t)  = addQuot (smulQuot r (ι t)) (smulQuot s (ι t))
    rw [← ι_smul_eq_smulQuot, ← ι_smul_eq_smulQuot,    ← ι_smul_eq_smulQuot,
      ← ι_add_eq_addQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, add_tensor, add_smul]
  zero_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change smulQuot (0 : k) (ι t) = ι zeroTree
    rw [← ι_smul_eq_smulQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [smul_tensor, zero_smul]

lemma add_eq_addQuot {n} {c : Fin n → S.C} (t1 t2 : S.TensorTreeQuot c) :
    t1 + t2 = addQuot t1 t2 := rfl

@[simp]
lemma ι_add_eq_add {n} {c : Fin n → S.C} (t1 t2 : TensorTree S c) :
    ι (t1.add t2) =  (ι t1) + (ι t2) := rfl

lemma smul_eq_smulQuot {n} {c : Fin n → S.C} (r : k) (t : S.TensorTreeQuot c) :
    r • t = smulQuot r t := rfl

@[simp]
lemma ι_smul_eq_smul {n} {c : Fin n → S.C} (r : k) (t : TensorTree S c) :
    ι (smul r t) = r • (ι t) := rfl

/-!

## The group action

-/

/-- The group action on an equivalence classes of tensor trees. -/
def actionQuot {n} {c : Fin n → S.C} (g : S.G) :
    S.TensorTreeQuot c → S.TensorTreeQuot c := by
  refine Quot.lift (fun t => ι (action g t)) ?_
  · intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [ι_apply_eq_iff_tensor_apply_eq]
    rw [action_tensor, action_tensor, h]

lemma ι_action_eq_actionQuot {n} {c : Fin n → S.C} (g : S.G) (t : TensorTree S c) :
    ι (action g t) = actionQuot g (ι t) := rfl

noncomputable instance {n} {c : Fin n → S.C} : MulAction S.G (S.TensorTreeQuot c) where
  smul := actionQuot
  one_smul t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change actionQuot (1 : S.G) (ι t) = ι t
    rw [← ι_action_eq_actionQuot]
    rw [ι_apply_eq_iff_tensor_apply_eq]
    simp [action_tensor]
  mul_smul g h t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    change actionQuot (g * h) (ι t) = actionQuot g (actionQuot h (ι t))
    rw [← ι_action_eq_actionQuot, ← ι_action_eq_actionQuot,
      ← ι_action_eq_actionQuot, ι_apply_eq_iff_tensor_apply_eq]
    simp [action_tensor]

@[simp]
lemma ι_action_eq_mulAction {n} {c : Fin n → S.C} (g : S.G) (t : TensorTree S c) :
    ι (action g t) = g • (ι t) := rfl

/-!

## To Tensors

-/

/-- The underlying tensor for an equivalence class of tensor trees. -/
noncomputable def tensorQuot {n} {c : Fin n → S.C} :
    S.TensorTreeQuot c →ₗ[k] S.F.obj (OverColor.mk c) where
  toFun := by
    refine Quot.lift (fun t => t.tensor) ?_
    intro t1 t2 h
    simp only [tensorRel] at h
    simp only
    rw [h]
  map_add' t1 t2 := by
    obtain ⟨t1, rfl⟩ := ι_surjective t1
    obtain ⟨t2, rfl⟩ := ι_surjective t2
    rw [← ι_add_eq_add]
    change ((t1.add t2)).tensor = (t1).tensor + (t2).tensor
    simp [add_tensor]
  map_smul' r t := by
    obtain ⟨t, rfl⟩ := ι_surjective t
    rw [← ι_smul_eq_smul]
    change (smul r t).tensor = r • t.tensor
    simp [smul_tensor]

lemma tensor_eq_tensorQuot_apply {n} {c : Fin n → S.C} (t : TensorTree S c) :
    (t).tensor = tensorQuot (ι t) := rfl

lemma tensorQuot_surjective {n} {c : Fin n → S.C} : Function.Surjective (tensorQuot (c := c)) := by
  simp only [Function.Surjective]
  intro t
  use ι (tensorNode t)
  rw [← tensor_eq_tensorQuot_apply]
  simp

end TensorTreeQuot

end TensorTree
