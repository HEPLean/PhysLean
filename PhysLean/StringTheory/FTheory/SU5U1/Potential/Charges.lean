/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.PresentIrredSet


namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

-- order qHd, qHu, Q5, Q10
def Charges : Type := Option ℤ × Option ℤ × Finset ℤ × Finset ℤ

instance : DecidableEq Charges := inferInstanceAs
  (DecidableEq (Option ℤ × Option ℤ × Finset ℤ × Finset ℤ))
namespace Charges
open PotentialTerm

instance hasSubset : HasSubset Charges where
  Subset x y := x.1.toFinset ⊆ y.1.toFinset ∧
    x.2.1.toFinset ⊆ y.2.1.toFinset ∧
    x.2.2.1 ⊆ y.2.2.1 ∧
    x.2.2.2 ⊆ y.2.2.2

instance subsetDecidable (x y : Charges) : Decidable (x ⊆ y) := instDecidableAnd

@[simp, refl]
lemma subset_refl (x : Charges) : x ⊆ x := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

lemma subset_trans {x y z : Charges} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z := by
  simp_all [Subset]

def fromPotentialTerm : (T : PotentialTerm) → T.ChargeType → Charges
  | μ, (qHd, qHu) => (qHd, qHu, {}, {})
  | β, (qHu, Q5) => (none, qHu, Q5, {})
  | Λ, (Q5, Q10) => (none, none, Q5, Q10)
  | W1, (Q5, Q10) => (none, none, Q5, Q10)
  | W2, (qHd, Q10) => (qHd, none, {}, Q10)
  | W3, (qHu, Q5) => (none, qHu, Q5, {})
  | W4, (qHd, qHu, Q5) => (qHd, qHu, Q5, {})
  | K1, (Q5, Q10) => (none, none, Q5, Q10)
  | K2, (qHd, qHu, Q10) => (qHd, qHu, {}, Q10)
  | topYukawa, (qHu, Q10) => (qHu, none, {}, Q10)
  | bottomYukawa, (qHd, Q5, Q10) => (qHd, none, Q5, Q10)

lemma fromPotentialTerm_injective (T : PotentialTerm) :
    Function.Injective (fromPotentialTerm T) := by
  sorry

lemma fromPotentialTerm_subset (T : PotentialTerm) (x y : T.ChargeType) :
    fromPotentialTerm T x ⊆ fromPotentialTerm T y ↔ x ⊆ y := by
  sorry

def toPotentialTerm : (T : PotentialTerm) → (x : Charges) → T.ChargeType
  | μ, (qHd, qHu, _, _) => (qHd, qHu)
  | β, (_, qHu, Q5, _) => (qHu, Q5)
  | Λ, (_, _, Q5, Q10) => (Q5, Q10)
  | W1, (_, _, Q5, Q10) => (Q5, Q10)
  | W2, (qHd, _, _, Q10) => (qHd, Q10)
  | W3, (_, qHu, Q5, _) => (qHu, Q5)
  | W4, (qHd, qHu, Q5, _) => (qHd, qHu, Q5)
  | K1, (_, _, Q5, Q10) => (Q5, Q10)
  | K2, (qHd, qHu, _, Q10) => (qHd, qHu, Q10)
  | topYukawa, (qHu, _, _, Q10) => (qHu, Q10)
  | bottomYukawa, (qHd, _, Q5, Q10) => (qHd, Q5, Q10)


def IsPhenoConstrained (x : Charges) : Prop :=
  ∀ T ∈ ({μ, β, Λ, W1, W2, W4, K1, K2} : Finset PotentialTerm), IsPresent T (x.toPotentialTerm T)


def phenoConstrainedIrredSetExe (I : CodimensionOneConfig): Finset Charges :=
  let X1 := ((presentIrredSet I μ).val.map (fromPotentialTerm μ)).toFinset
    ∪ ((presentIrredSet I β).val.map (fromPotentialTerm β)).toFinset
    ∪ ((presentIrredSet I Λ).val.map (fromPotentialTerm Λ)).toFinset
    ∪ ((presentIrredSet I W1).val.map (fromPotentialTerm W1)).toFinset
    ∪ ((presentIrredSet I W2).val.map (fromPotentialTerm W2)).toFinset
    ∪ ((presentIrredSet I W4).val.map (fromPotentialTerm W4)).toFinset
    ∪ ((presentIrredSet I K1).val.map (fromPotentialTerm K1)).toFinset
    ∪ ((presentIrredSet I K2).val.map (fromPotentialTerm K2)).toFinset
  X1.filter (fun x => ∀ y ∈ X1, x = y ∨ ¬ (y ⊆ x))

def allowedQ10Map (I : CodimensionOneConfig) (Q10 : Finset ℤ) : Finset Charges :=
  let X1 := phenoConstrainedIrredSetExe I
  let Xprod := I.allowedBarFiveCharges.product (I.allowedBarFiveCharges.product I.allowedBarFiveCharges)
  let X2 : Multiset Charges := Xprod.val.map
    (fun x => (x.1, x.2.1, {x.2.2}, Q10))
  (X2.filter (fun x => ¬ ∃ g ∈ X1, g ⊆ x)).toFinset

def allowedQ10 (I : CodimensionOneConfig) : Finset (Finset ℤ) :=
  I.allowedTenCharges.powerset.filter (fun x => (allowedQ10Map I x) = ∅)

def allowedQ5Map (I : CodimensionOneConfig) (Q5 : Finset ℤ) : Finset Charges :=
  let X1 := phenoConstrainedIrredSetExe I
  let Xprod := I.allowedBarFiveCharges.product (I.allowedBarFiveCharges.product I.allowedTenCharges)
  let X2 : Multiset Charges := Xprod.val.map
    (fun x => (x.1, x.2.1, Q5, {x.2.2}))
  (X2.filter (fun x => ¬ ∃ g ∈ X1, g ⊆ x)).toFinset

def allowedQ5 (I : CodimensionOneConfig) : Finset (Finset ℤ) :=
  I.allowedBarFiveCharges.powerset.filter (fun x => (allowedQ5Map I x) = ∅)

def allowedqHdQ5 (I : CodimensionOneConfig) (qHd q5 : ℤ) : Finset Charges :=
  let X1 := phenoConstrainedIrredSetExe I
  let Xprod := I.allowedBarFiveCharges.product (I.allowedTenCharges)
  let X2 : Multiset Charges := Xprod.val.map
    (fun x => (qHd, x.1, {q5}, {x.2}))
  (X2.filter (fun x => ¬ ∃ g ∈ X1, g ⊆ x)).toFinset


def test : Finset (Finset ℤ) := {{-3, -1, 0},
 {-2, -1, 0},
 {-3, -2, -1, 0},
 {-3, -2, 1},
 {-1, 1},
 {-3, -1, 1},
 {-2, -1, 1},
 {-3, -2, -1, 1},
 {-3, 0, 1},
 {-2, 0, 1},
 {-3, -2, 0, 1},
 {-1, 0, 1},
 {-3, -1, 0, 1},
 {-2, -1, 0, 1},
 {-3, -2, -1, 0, 1},
 {-3, -1, 2},
 {-2, -1, 2},
 {-3, -2, -1, 2},
 {-3, 0, 2},
 {-3, -2, 0, 2},
 {-1, 0, 2},
 {-3, -1, 0, 2},
 {-2, -1, 0, 2},
 {-3, -2, -1, 0, 2},
 {-3, 1, 2},
 {-2, 1, 2},
 {-3, -2, 1, 2},
 {-1, 1, 2},
 {-3, -1, 1, 2},
 {-2, -1, 1, 2},
 {-3, -2, -1, 1, 2},
 {0, 1, 2},
 {-3, 0, 1, 2},
 {-2, 0, 1, 2},
 {-3, -2, 0, 1, 2},
 {-1, 0, 1, 2},
 {-3, -1, 0, 1, 2},
 {-2, -1, 0, 1, 2},
 {-3, -2, -1, 0, 1, 2},
 {-3, -1, 3},
 {-2, -1, 3},
 {-3, -2, -1, 3},
 {-2, 0, 3},
 {-3, -2, 0, 3},
 {-1, 0, 3},
 {-3, -1, 0, 3},
 {-2, -1, 0, 3},
 {-3, -2, -1, 0, 3},
 {-3, 1, 3},
 {-2, 1, 3},
 {-3, -2, 1, 3},
 {-1, 1, 3},
 {-3, -1, 1, 3},
 {-2, -1, 1, 3},
 {-3, -2, -1, 1, 3},
 {0, 1, 3},
 {-3, 0, 1, 3},
 {-2, 0, 1, 3},
 {-3, -2, 0, 1, 3},
 {-1, 0, 1, 3},
 {-3, -1, 0, 1, 3},
 {-2, -1, 0, 1, 3},
 {-3, -2, -1, 0, 1, 3},
 {-3, -2, 2, 3},
 {-1, 2, 3},
 {-3, -1, 2, 3},
 {-2, -1, 2, 3},
 {-3, -2, -1, 2, 3},
 {-3, 0, 2, 3},
 {-2, 0, 2, 3},
 {-3, -2, 0, 2, 3},
 {-1, 0, 2, 3},
 {-3, -1, 0, 2, 3},
 {-2, -1, 0, 2, 3},
 {-3, -2, -1, 0, 2, 3},
 {-3, 1, 2, 3},
 {-2, 1, 2, 3},
 {-3, -2, 1, 2, 3},
 {-1, 1, 2, 3},
 {-3, -1, 1, 2, 3},
 {-2, -1, 1, 2, 3},
 {-3, -2, -1, 1, 2, 3},
 {0, 1, 2, 3},
 {-3, 0, 1, 2, 3},
 {-2, 0, 1, 2, 3},
 {-3, -2, 0, 1, 2, 3},
 {-1, 0, 1, 2, 3},
 {-3, -1, 0, 1, 2, 3},
 {-2, -1, 0, 1, 2, 3},
 {-3, -2, -1, 0, 1, 2, 3}}

#eval (test.filter (fun x => x.card ≤ 3))
def disallowed (I : CodimensionOneConfig) : Finset Charges :=by
  let X1 := phenoConstrainedIrredSetExe I
  let X2 : Multiset Charges := (I.allowedBarFiveCharges.product I.allowedBarFiveCharges).val.map
    (fun x => (some x.1, none, {x.2}, {}))

  sorry
example : (phenoConstrainedIrredSetExe .same).card = 178 := by native_decide

end Charges

end SU5U1

end FTheory
