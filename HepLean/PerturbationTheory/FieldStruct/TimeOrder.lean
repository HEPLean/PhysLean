/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List.InsertionSort
import HepLean.PerturbationTheory.Algebras.StateAlgebra.Basic
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# State algebra

We define the state algebra of a field structure to be the free algebra
generated by the states.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

/-- Returns true if `timeOrder a b` is true if `a` has time greater then or equal to `b`.
  This will put the stats at the greatest time to left. -/
def timeOrderProp : 𝓕.States → 𝓕.States → Prop
  | States.posAsymp _, _ => True
  | States.position φ0, States.position φ1 => φ1.2 0 ≤ φ0.2 0
  | States.position _, States.negAsymp _ => True
  | States.position _, States.posAsymp _ => False
  | States.negAsymp _, States.posAsymp _ => False
  | States.negAsymp _, States.position _ => False
  | States.negAsymp _, States.negAsymp _ => True

noncomputable instance : (φ φ' : 𝓕.States) → Decidable (timeOrderProp φ φ')
  | States.posAsymp _, _ => isTrue True.intro
  | States.position φ0, States.position φ1 => inferInstanceAs (Decidable (φ1.2 0 ≤ φ0.2 0))
  | States.position _, States.negAsymp _ => isTrue True.intro
  | States.position _, States.posAsymp _ => isFalse (fun a => a)
  | States.negAsymp _, States.posAsymp _ => isFalse (fun a => a)
  | States.negAsymp _, States.position _ => isFalse (fun a => a)
  | States.negAsymp _, States.negAsymp _ => isTrue True.intro

/-- Time ordering is total. -/
instance : IsTotal 𝓕.States 𝓕.timeOrderProp where
  total a b := by
    cases a <;> cases b <;>
      simp only [or_self, or_false, or_true, timeOrderProp, Fin.isValue, implies_true, imp_self,
        IsEmpty.forall_iff]
    exact LinearOrder.le_total _ _

/-- Time ordering is transitive. -/
instance : IsTrans 𝓕.States 𝓕.timeOrderProp where
  trans a b c := by
    cases a <;> cases b <;> cases c <;>
      simp only [timeOrderProp, Fin.isValue, implies_true, imp_self, IsEmpty.forall_iff]
    exact fun h1 h2 => Preorder.le_trans _ _ _ h2 h1

noncomputable section

open FieldStatistic
open HepLean.List

def maxTimeFieldPos (φ : 𝓕.States) (φs : List 𝓕.States) : ℕ :=
  insertionSortMinPos timeOrderProp φ φs

lemma maxTimeFieldPos_lt_length (φ : 𝓕.States) (φs : List 𝓕.States) :
    maxTimeFieldPos φ φs < (φ :: φs).length := by
  simp [maxTimeFieldPos]

def maxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) : 𝓕.States :=
  insertionSortMin timeOrderProp φ φs

def eraseMaxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) : List 𝓕.States :=
  insertionSortDropMinPos timeOrderProp φ φs

@[simp]
lemma eraseMaxTimeField_length (φ : 𝓕.States) (φs : List 𝓕.States) :
    (eraseMaxTimeField φ φs).length = φs.length := by
  simp [eraseMaxTimeField, insertionSortDropMinPos, eraseIdx_length']

lemma maxTimeFieldPos_lt_eraseMaxTimeField_length_succ (φ : 𝓕.States) (φs : List 𝓕.States) :
    maxTimeFieldPos φ φs < (eraseMaxTimeField φ φs).length.succ := by
  simp only [eraseMaxTimeField_length, Nat.succ_eq_add_one]
  exact maxTimeFieldPos_lt_length φ φs

def maxTimeFieldPosFin (φ : 𝓕.States) (φs : List 𝓕.States) :
    Fin (eraseMaxTimeField φ φs).length.succ :=
  insertionSortMinPosFin timeOrderProp φ φs

lemma lt_maxTimeFieldPosFin_not_timeOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin (eraseMaxTimeField φ φs).length)
    (hi : (maxTimeFieldPosFin φ φs).succAbove i < maxTimeFieldPosFin φ φs) :
    ¬ timeOrderProp ((eraseMaxTimeField φ φs)[i.val]) (maxTimeField φ φs) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt timeOrderProp φ φs i hi

lemma timeOrder_maxTimeField (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin (eraseMaxTimeField φ φs).length) :
    timeOrderProp (maxTimeField φ φs) ((eraseMaxTimeField φ φs)[i.val]) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos timeOrderProp φ φs _

def timeOrderSign (φs : List 𝓕.States) : ℂ :=
  Wick.koszulSign 𝓕.statesStatistic 𝓕.timeOrderProp φs

lemma timeOrderSign_pair_ordered {φ ψ : 𝓕.States} (h : timeOrderProp φ ψ) :
    timeOrderSign [φ, ψ] = 1 := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, ite_eq_left_iff,
    ite_eq_right_iff, and_imp]
  exact fun h' => False.elim (h' h)

lemma timeOrderSign_pair_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderProp φ ψ) :
    timeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, instCommGroup.eq_1]
  rw [if_neg h]
  simp [FieldStatistic.pairedSign_eq_if]

lemma timerOrderSign_of_eraseMaxTimeField (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrderSign (eraseMaxTimeField φ φs) = timeOrderSign (φ :: φs) *
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) := by
  rw [eraseMaxTimeField, insertionSortDropMinPos, timeOrderSign,
    Wick.koszulSign_eraseIdx_insertionSortMinPos]
  rw [← timeOrderSign, ← maxTimeField]
  rfl

def timeOrderList (φs : List 𝓕.States) : List 𝓕.States :=
  List.insertionSort 𝓕.timeOrderProp φs

lemma timeOrderList_pair_ordered {φ ψ : 𝓕.States} (h : timeOrderProp φ ψ) :
    timeOrderList [φ, ψ] = [φ, ψ] := by
  simp only [timeOrderList, List.insertionSort, List.orderedInsert, ite_eq_left_iff,
    List.cons.injEq, and_true]
  exact fun h' => False.elim (h' h)

lemma timeOrderList_pair_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderProp φ ψ) :
    timeOrderList [φ, ψ] = [ψ, φ] := by
  simp only [timeOrderList, List.insertionSort, List.orderedInsert, ite_eq_right_iff,
    List.cons.injEq, and_true]
  exact fun h' => False.elim (h h')

@[simp]
lemma timeOrderList_nil : timeOrderList (𝓕 := 𝓕) [] = [] := by
  simp [timeOrderList]

lemma timeOrderList_eq_maxTimeField_timeOrderList (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrderList (φ :: φs) = maxTimeField φ φs :: timeOrderList (eraseMaxTimeField φ φs) := by
  exact insertionSort_eq_insertionSortMin_cons timeOrderProp φ φs

end
end FieldStruct
