/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.StateAlgebra.Basic
import HepLean.PerturbationTheory.FieldStruct.CreateAnnihilateSect
/-!

# Creation and annihlation free-algebra

This module defines the creation and annihilation algebra for a field structure.

The creation and annihilation algebra extends from the state algebra by adding information about
whether a state is a creation or annihilation operator.

The algebra is spanned by lists of creation/annihilation states.

The main structures defined in this module are:

* `CrAnAlgebra` - The creation and annihilation algebra
* `ofCrAnState` - Maps a creation/annihilation state to the algebra
* `ofCrAnList` - Maps a list of creation/annihilation states to the algebra
* `ofState` - Maps a state to a sum of creation and annihilation operators
* `crPart` - The creation part of a state in the algebra
* `anPart` - The annihilation part of a state in the algebra
* `superCommute` - The super commutator on the algebra

The key lemmas show how these operators interact, particularly focusing on the
super commutation relations between creation and annihilation operators.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

/-- The creation and annihlation free-algebra.
  The free algebra generated by `CrAnStates`,
  that is a position based states or assymptotic states with a specification of
  whether the state is a creation or annihlation state.
  As a module `CrAnAlgebra` is spanned by lists of `CrAnStates`. -/
abbrev CrAnAlgebra (𝓕 : FieldStruct) : Type := FreeAlgebra ℂ 𝓕.CrAnStates

namespace CrAnAlgebra

open StateAlgebra

/-- Maps a creation and annihlation state to the creation and annihlation free-algebra. -/
def ofCrAnState (φ : 𝓕.CrAnStates) : CrAnAlgebra 𝓕 :=
  FreeAlgebra.ι ℂ φ

/-- Maps a list creation and annihlation state to the creation and annihlation free-algebra
  by taking their product. -/
def ofCrAnList (φs : List 𝓕.CrAnStates) : CrAnAlgebra 𝓕 := (List.map ofCrAnState φs).prod

@[simp]
lemma ofCrAnList_nil : ofCrAnList ([] : List 𝓕.CrAnStates) = 1 := rfl

lemma ofCrAnList_cons (φ : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates) :
    ofCrAnList (φ :: φs) = ofCrAnState φ * ofCrAnList φs := rfl

lemma ofCrAnList_append (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnList (φs ++ φs') = ofCrAnList φs * ofCrAnList φs' := by
  dsimp only [ofCrAnList]
  rw [List.map_append, List.prod_append]

lemma ofCrAnList_singleton (φ : 𝓕.CrAnStates) :
    ofCrAnList [φ] = ofCrAnState φ := by
  simp [ofCrAnList]

/-- Maps a state to the sum of creation and annihilation operators in
  creation and annihilation free-algebra. -/
def ofState (φ : 𝓕.States) : CrAnAlgebra 𝓕 :=
  ∑ (i : 𝓕.statesToCrAnType φ), ofCrAnState ⟨φ, i⟩

/-- The algebra map from the state free-algebra to the creation and annihlation free-algebra. -/
def ofStateAlgebra : StateAlgebra 𝓕 →ₐ[ℂ] CrAnAlgebra 𝓕 :=
  FreeAlgebra.lift ℂ ofState

@[simp]
lemma ofStateAlgebra_ofState (φ : 𝓕.States) :
    ofStateAlgebra (StateAlgebra.ofState φ) = ofState φ := by
  simp [ofStateAlgebra, StateAlgebra.ofState]

/-- Maps a list of states to the creation and annihilation free-algebra by taking
  the product of their sums of creation and annihlation operators.
  Roughly `[φ1, φ2]` gets sent to `(φ1ᶜ+ φ1ᵃ) * (φ2ᶜ+ φ2ᵃ)` etc. -/
def ofStateList (φs : List 𝓕.States) : CrAnAlgebra 𝓕 := (List.map ofState φs).prod

@[simp]
lemma ofStateList_nil : ofStateList ([] : List 𝓕.States) = 1 := rfl

lemma ofStateList_cons (φ : 𝓕.States) (φs : List 𝓕.States) :
    ofStateList (φ :: φs) = ofState φ * ofStateList φs := rfl

lemma ofStateList_singleton (φ : 𝓕.States) :
    ofStateList [φ] = ofState φ := by
  simp [ofStateList]

lemma ofStateList_append (φs φs' : List 𝓕.States) :
    ofStateList (φs ++ φs') = ofStateList φs * ofStateList φs' := by
  dsimp only [ofStateList]
  rw [List.map_append, List.prod_append]

lemma ofStateAlgebra_ofList_eq_ofStateList : (φs : List 𝓕.States) →
    ofStateAlgebra (ofList φs) = ofStateList φs
  | [] => by
    simp [ofStateList]
  | φ :: φs => by
    rw [ofStateList_cons, StateAlgebra.ofList_cons]
    rw [map_mul]
    simp only [ofStateAlgebra_ofState, mul_eq_mul_left_iff]
    apply Or.inl (ofStateAlgebra_ofList_eq_ofStateList φs)

lemma ofStateList_sum (φs : List 𝓕.States) :
    ofStateList φs = ∑ (s : CreateAnnihilateSect φs), ofCrAnList s.1 := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
    rw [CreateAnnihilateSect.sum_cons]
    dsimp only [CreateAnnihilateSect.cons, ofCrAnList_cons]
    conv_rhs =>
      enter [2, x]
      rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ofStateList_cons, ← ih]
    rfl

/-!

## Creation and annihilation parts of a state

-/

def crPart : 𝓕.StateAlgebra →ₐ[ℂ] 𝓕.CrAnAlgebra :=
  FreeAlgebra.lift ℂ fun φ =>
  match φ with
  | States.negAsymp φ => ofCrAnState ⟨States.negAsymp φ, ()⟩
  | States.position φ => ofCrAnState ⟨States.position φ, CreateAnnihilate.create⟩
  | States.posAsymp _ => 0

@[simp]
lemma crPart_negAsymp (φ : 𝓕.AsymptoticNegTime) :
    crPart (StateAlgebra.ofState (States.negAsymp φ)) = ofCrAnState ⟨States.negAsymp φ, ()⟩ := by
  dsimp only [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma crPart_position (φ : 𝓕.PositionStates) :
    crPart (StateAlgebra.ofState (States.position φ)) =
    ofCrAnState ⟨States.position φ, CreateAnnihilate.create⟩ := by
  dsimp only [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma crPart_posAsymp (φ : 𝓕.AsymptoticPosTime) :
    crPart (StateAlgebra.ofState (States.posAsymp φ)) = 0 := by
  dsimp only [crPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

def anPart : 𝓕.StateAlgebra →ₐ[ℂ] 𝓕.CrAnAlgebra :=
  FreeAlgebra.lift ℂ fun φ =>
  match φ with
  | States.negAsymp _ => 0
  | States.position φ => ofCrAnState ⟨States.position φ, CreateAnnihilate.annihilate⟩
  | States.posAsymp φ => ofCrAnState ⟨States.posAsymp φ, ()⟩

@[simp]
lemma anPart_negAsymp (φ : 𝓕.AsymptoticNegTime) :
    anPart (StateAlgebra.ofState (States.negAsymp φ)) = 0 := by
  dsimp only [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma anPart_position (φ : 𝓕.PositionStates) :
    anPart (StateAlgebra.ofState (States.position φ)) =
    ofCrAnState ⟨States.position φ, CreateAnnihilate.annihilate⟩ := by
  dsimp only [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

@[simp]
lemma anPart_posAsymp (φ : 𝓕.AsymptoticPosTime) :
    anPart (StateAlgebra.ofState (States.posAsymp φ)) = ofCrAnState ⟨States.posAsymp φ, ()⟩ := by
  dsimp only [anPart, StateAlgebra.ofState]
  rw [FreeAlgebra.lift_ι_apply]

lemma ofState_eq_crPart_add_anPart (φ : 𝓕.States) :
    ofState φ = crPart (StateAlgebra.ofState φ) + anPart (StateAlgebra.ofState φ) := by
  rw [ofState]
  cases φ with
  | negAsymp φ =>
    dsimp only [statesToCrAnType]
    simp
  | position φ =>
    dsimp only [statesToCrAnType]
    rw [CreateAnnihilate.sum_eq]
    simp
  | posAsymp φ =>
    dsimp only [statesToCrAnType]
    simp

/-!

## The basis of the creation and annihlation free-algebra.

-/

noncomputable def ofCrAnListBasis : Basis (List 𝓕.CrAnStates) ℂ (CrAnAlgebra 𝓕) where
  repr := FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv

@[simp]
lemma ofListBasis_eq_ofList (φs : List 𝓕.CrAnStates) :
    ofCrAnListBasis φs = ofCrAnList φs := by
  simp only [ofCrAnListBasis, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    Basis.coe_ofRepr, AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.ofAlgHom_symm_apply, ofCrAnList]
  erw [MonoidAlgebra.lift_apply]
  simp only [zero_smul, Finsupp.sum_single_index, one_smul]
  rw [@FreeMonoid.lift_apply]
  simp only [List.prod]
  match φs with
  | [] => rfl
  | φ :: φs =>
    erw [List.map_cons]

/-!

## Some useful multi-linear maps.

-/

noncomputable def mulLinearMap : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 where
  toFun a := {
    toFun := fun b => a * b,
    map_add' := fun c d => by
      simp [mul_add]
    map_smul' := by simp}
  map_add' := fun a b => by
    ext c
    simp [add_mul]
  map_smul' := by
    intros
    ext c
    simp [smul_mul']

lemma mulLinearMap_apply (a b : CrAnAlgebra 𝓕) :
    mulLinearMap a b = a * b := by rfl

noncomputable def smulLinearMap (c : ℂ) : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 where
  toFun a := c • a
  map_add' := by simp
  map_smul' m x := by
    simp only [smul_smul, RingHom.id_apply]
    rw [NonUnitalNormedCommRing.mul_comm]

end CrAnAlgebra

end FieldStruct
