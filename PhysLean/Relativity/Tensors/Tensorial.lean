/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Product
/-!

# Tensorial class

## i. Overview

We define a class called `Tensorial`.
This class is used to enable the use of index notation on a type `M` via a linear equivalence to a
tensor of a `TensorSpecies`.

We define the class `Tensorial` here, and provide an API around its use.

## ii. Key results

- `Tensorial` : The class used to allow index notation on a type `M`.
- `Tensorial.numIndices` : The number of indices of an element of an `M`
  carrying a tensorial instance.
- `Tensorial.mulAction` : The action of the group `G` on a
  type `M` carrying a tensorial instance.
- `Tensorial.prod` : The product of two tensorial instances is a tensorial instance.

## iii. Table of contents

- A. Defining the tensorial class
  - A.1. Tensors carry a tensorial instance
  - A.2. The number of indices
- B. The action of the group on a module with a tensorial instance
  - B.1. Relation between the action and the equivalence to tensors
  - B.2. Linear properties of the action
  - B.3. The action as a linear map
- C. Properties of the basis
- D. Products of tensorial instances
  - D.1. The equivalence to tensors on products
  - D.2. The group action on products
  - D.3. The basis on products

## iv. References

There are no known references for this material.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

/-!

## A. Defining the tensorial class

We first define the `Tensorial` class.

-/

/-- The tensorial class is used to define a tensor structure on a type `M` through a
  linear equivalence with a module `S.Tensor c` for `S` a tensor species. -/
class Tensorial
    {k : outParam Type} [CommRing k] {C G : outParam Type} [Group G]
    {n : outParam ℕ} (S : outParam (TensorSpecies k C G)) (c :outParam (Fin n → C)) (M : Type)
    [AddCommMonoid M] [Module k M] where
  /-- The equivalence between `M` and `S.Tensor c` in a tensorial instance. -/
  toTensor : M ≃ₗ[k] S.Tensor c

namespace Tensorial

variable {n : ℕ} {c : Fin n → C} {M : Type} [AddCommMonoid M] [Module k M]

/-!

### A.1. Tensors carry a tensorial instance

The module of tensors of a tensor species carries a canonical tensorial instance,
through the equivalence.

-/
noncomputable instance self {n : ℕ} (S : TensorSpecies k C G) (c : Fin n → C) :
    Tensorial S c (S.Tensor c) where
  toTensor := LinearEquiv.refl k (S.Tensor c)

@[simp]
lemma self_toTensor_apply {n : ℕ} (S : TensorSpecies k C G) (c : Fin n → C) (t : S.Tensor c) :
    Tensorial.toTensor t = t := by
  rw [Tensorial.toTensor]
  rfl

/-!

### A.2. The number of indices

-/

/-- The number of indices of a elements `t : M` where `M` carries a tensorial instance. -/
def numIndices (t : M) [Tensorial S c M] : ℕ :=
  TensorSpecies.numIndices (toTensor t)

/-!

## B. The action of the group on a module with a tensorial instance

We now define the action of the group `G` on a type `M` carrying a tensorial instance.

-/

noncomputable instance mulAction [Tensorial S c M] : MulAction G M where
  smul g m := toTensor.symm (g • toTensor m)
  one_smul m := by
    change toTensor.symm (1 • toTensor m) = _
    simp
  mul_smul g h m := by
    change _ = toTensor.symm (g • toTensor (toTensor.symm (h • toTensor m)))
    simp only [LinearEquiv.apply_symm_apply]
    rw [← mul_smul]
    rfl

/-!

### B.1. Relation between the action and the equivalence to tensors

-/

lemma smul_eq {g : G} {t : M} [Tensorial S c M] :
    g • t = toTensor.symm (g • toTensor t) := by
  rw [Tensorial.toTensor]
  rfl

lemma toTensor_smul {g : G} {t : M} [Tensorial S c M] :
    toTensor (g • t) = g • toTensor t := by
  rw [smul_eq]
  simp

lemma smul_toTensor_symm {g : G} {t : Tensor S c} [self : Tensorial S c M] :
    g • (toTensor (self := self).symm t) = toTensor.symm (g • t) := by
  rw [smul_eq]
  simp

/-!

### B.2. Linear properties of the action

-/

@[simp]
lemma smul_add {g : G} [Tensorial S c M] (m m' : M) :
    g • (m + m') = g • m + g • m' := by
  apply toTensor.injective
  simp [toTensor_smul, map_add, Tensor.actionT_add]

@[simp]
lemma smul_neg {n : ℕ} {c : Fin n → C} {M : Type} [AddCommGroup M] [Module k M]
    [Tensorial S c M] (g : G) (m : M) :
    g • (-m) = - (g • m) := toTensor.injective <| by
  simp [toTensor_smul, map_neg, Tensor.actionT_neg]

@[simp]
lemma smul_zero [Tensorial S c M] {g : G} :
    g • (0 : M) = 0 := toTensor.injective <| by
  simp [toTensor_smul, map_zero, Tensor.actionT_zero]

/-!

### B.3. The action as a linear map

-/

/-- The action of the group on a `Tensorial` instance as a linear map. -/
noncomputable def smulLinearMap (g : G) [Tensorial S c M] : M →ₗ[k] M where
  toFun m := g • m
  map_add' x y := by
    apply toTensor.injective
    simp [toTensor_smul]
  map_smul' c x := by
    apply toTensor.injective
    simp [toTensor_smul]

lemma smulLinearMap_apply {g : G} [Tensorial S c M] (m : M) :
    smulLinearMap g m = g • m := rfl

/-!

## C. Properties of the basis

We now prove some properties of the basis induced on a `Tensorial` instance.

-/

lemma basis_toTensor_apply [Tensorial S c M] (m : M) :
    (Tensor.basis c).repr (toTensor m) = ((Tensor.basis c).map toTensor.symm).repr m := rfl

/-!

## D. Products of tensorial instances

-/

open TensorProduct

noncomputable instance prod [Tensorial S c M] {n2 : ℕ} {c2 : Fin n2 → C}
    {M₂ : Type} [AddCommMonoid M₂] [Module k M₂] [Tensorial S c2 M₂] :
    Tensorial S (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm) (M ⊗[k] M₂) where
  toTensor := (TensorProduct.congr toTensor toTensor).trans
    (Tensor.tensorEquivProd)

/-!

### D.1. The equivalence to tensors on products

-/

lemma toTensor_tprod {n2 : ℕ} {c2 : Fin n2 → C} {M₂ : Type}
    [Tensorial S c M] [AddCommMonoid M₂] [Module k M₂]
    [Tensorial S c2 M₂] (m : M) (m2 : M₂) :
    toTensor (m ⊗ₜ[k] m2) = Tensor.prodT (toTensor m) (toTensor m2) := rfl

/-!

### D.2. The group action on products

-/
lemma smul_prod {n2 : ℕ} {c2 : Fin n2 → C} {M₂ : Type}
    [Tensorial S c M] [AddCommMonoid M₂] [Module k M₂]
    [Tensorial S c2 M₂] (g : G) (m : M) (m2 : M₂) :
    g • (m ⊗ₜ[k] m2) = (g • m) ⊗ₜ[k] (g • m2) := by
  apply toTensor.injective
  simp [toTensor_smul]
  rw [toTensor_tprod, toTensor_tprod]
  rw [← Tensor.prodT_equivariant, toTensor_smul, toTensor_smul]

/-!

### D.3. The basis on products

-/
lemma basis_map_prod {n2 : ℕ} {c2 : Fin n2 → C} {M₂ : Type}
    [Tensorial S c M] [AddCommMonoid M₂] [Module k M₂]
    [Tensorial S c2 M₂] :
    (Tensor.basis (S := S) (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm)).map
      (toTensor (M := (M ⊗[k] M₂))).symm =
    (((Tensor.basis (S := S) c).map (toTensor (M := M)).symm).tensorProduct
    ((Tensor.basis (S := S) c2).map (toTensor (M := M₂)).symm)).reindex
    (Tensor.ComponentIdx.splitEquiv.symm) := by
  rw [Tensor.basis_prod_eq]
  ext b
  simp only [Tensor.ComponentIdx.splitEquiv, Module.Basis.map_apply, Module.Basis.coe_reindex,
    Equiv.symm_symm, Equiv.coe_fn_mk, Function.comp_apply, Module.Basis.tensorProduct_apply]
  apply toTensor.injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [toTensor_tprod]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

end Tensorial
