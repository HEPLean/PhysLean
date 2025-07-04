/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Basic
/-!

# Tensorial class

The tensorial class is used to define a tensorial structure on a type `M` via
a linear equivalence to a tensor of a `TensorSpecies`.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

/-- The tensorial class is used to define a tensor structure on a type `M` through a
  linear equivalence with a module `S.Tensor c` for `S` a tensor species. -/
class Tensorial
   {k : outParam Type} [CommRing k] {C G : outParam Type} [Group G]
   {n : outParam ℕ} (S : outParam (TensorSpecies k C G)) (c :outParam (Fin n → C)) (M : Type)
  [AddCommMonoid M] [Module k M] where
  toTensor : M ≃ₗ[k] S.Tensor c

namespace Tensorial

variable {n : ℕ} {c : Fin n → C} {M : Type} [AddCommMonoid M] [Module k M]

noncomputable instance self {n : ℕ} (S : TensorSpecies k C G) (c : Fin n → C) :
    Tensorial S c (S.Tensor c) where
  toTensor := LinearEquiv.refl k (S.Tensor c)

@[simp]
lemma self_toTensor_apply {n : ℕ} (S : TensorSpecies k C G) (c : Fin n → C) (t : S.Tensor c) :
    Tensorial.toTensor t = t := by
  rw [Tensorial.toTensor]
  rfl

noncomputable instance mulAction [Tensorial S c M] : MulAction G M where
  smul g m := toTensor.symm (g • toTensor m)
  one_smul m := by
    change toTensor.symm (1 • toTensor m) = _
    simp
  mul_smul g h m := by
    change _ = toTensor.symm (g • toTensor (toTensor.symm (h • toTensor m) ))
    simp only [LinearEquiv.apply_symm_apply]
    rw [← mul_smul]
    rfl

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

/-- The number of indices of a elements `t : M` where `M` carries a tensorial instance. -/
def numIndices (t : M) [Tensorial S c M] : ℕ :=
  TensorSpecies.numIndices (toTensor t)

end Tensorial
