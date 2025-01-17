/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.CreateAnnihilate
/-!

# State algebra

We define the state algebra of a field structure to be the free algebra
generated by the states.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

abbrev StateAlgebra (𝓕 : FieldStruct) : Type := FreeAlgebra ℂ 𝓕.States

namespace StateAlgebra

open FieldStatistic

def ofState (φ : 𝓕.States) : StateAlgebra 𝓕 :=
  FreeAlgebra.ι ℂ φ

def ofList (φs : List 𝓕.States) : StateAlgebra 𝓕 :=
  (List.map ofState φs).prod

@[simp]
lemma ofList_nil : ofList ([] : List 𝓕.States) = 1 := rfl

lemma ofList_singleton (φ : 𝓕.States) : ofList [φ] = ofState φ := by
  simp [ofList]

lemma ofList_append (φs ψs : List 𝓕.States) :
    ofList (φs ++ ψs) = ofList φs * ofList ψs := by
  rw [ofList, List.map_append, List.prod_append]
  rfl

lemma ofList_cons (φ : 𝓕.States) (φs : List 𝓕.States) :
    ofList (φ :: φs) = ofState φ * ofList φs := rfl

noncomputable def ofListBasis : Basis (List 𝓕.States) ℂ (StateAlgebra 𝓕) where
  repr := FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv

@[simp]
lemma ofListBasis_eq_ofList (φs : List 𝓕.States) :
    ofListBasis φs = ofList φs := by
  simp [ofListBasis, ofList, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  erw [MonoidAlgebra.lift_apply]
  simp
  rw [@FreeMonoid.lift_apply]
  simp [List.prod]
  match φs with
  | [] => rfl
  | φ :: φs =>
    erw [List.map_cons]

/-!

## The super commutor on the state algebra.

-/


noncomputable def superCommute :
   𝓕.StateAlgebra →ₗ[ℂ] 𝓕.StateAlgebra →ₗ[ℂ] 𝓕.StateAlgebra :=
  Basis.constr ofListBasis ℂ fun φs =>
  Basis.constr ofListBasis ℂ fun φs' =>
  ofList (φs ++ φs') - pairedSign (FieldStatistic.ofList 𝓕.statesStatistic φs)
    (FieldStatistic.ofList 𝓕.statesStatistic φs') • ofList (φs' ++ φs)

local notation "⟨" φs "," φs' "⟩ₛ" => superCommute φs φs'

lemma superCommute_ofList (φs φs' : List 𝓕.States) : ⟨ofList φs, ofList φs'⟩ₛ =
    ofList (φs ++ φs') - pairedSign (FieldStatistic.ofList 𝓕.statesStatistic φs)
    (FieldStatistic.ofList 𝓕.statesStatistic φs') • ofList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommute, Basis.constr_basis]

end StateAlgebra

end FieldStruct
