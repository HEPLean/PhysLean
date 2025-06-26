/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.LorentzGroup.Restricted
import PhysLean.Relativity.Tensors.RealTensor.Velocity.Basic
import PhysLean.Meta.Informal.SemiFormal
/-!

# Generalized Boosts

This module defines a generalization of the tradiational boosts.
They are define given two elocities `u` and `v`, as an input an take
the velocity `u` to the velocity `v`.

We show that these generalised boosts are Lorentz transformations,
and furthermore sit in the restricted Lorentz group.

A boost is the special case of a generalised boost when `u = basis 0`.

## References

- The main argument follows: Guillem Cobos, The Lorentz Group, 2015:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf

-/
noncomputable section

namespace LorentzGroup

open Lorentz
open TensorProduct
open Vector
variable {d : ℕ}

/-- An auxiliary linear map used in the definition of a generalised boost. -/
def genBoostAux₁ (u v : Velocity d) : Vector d →ₗ[ℝ] Vector d where
  toFun x := (2 * ⟪x, u⟫ₘ) • v
  map_add' x y := by
    simp [map_add, LinearMap.add_apply, tmul_add, add_tmul, mul_add, add_smul]
  map_smul' c x := by
    simp only [smul_tmul, tmul_smul, map_smul, smul_eq_mul, RingHom.id_apply, smul_smul]
    dsimp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    ring

/-- An auxiliary linear map used in the definition of a generalised boost. -/
def genBoostAux₂ (u v : Velocity d) : Vector d →ₗ[ℝ] Vector d where
  toFun x := - (⟪x, u.1 + v.1⟫ₘ / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1)
  map_add' x y := by
    rw [← add_smul]
    apply congrFun (congrArg _ _)
    field_simp [add_tmul]
    apply congrFun (congrArg _ _)
    ring
  map_smul' c x := by
    rw [map_smul]
    dsimp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [smul_smul, mul_div_assoc, neg_mul_eq_mul_neg]

lemma genBoostAux₂_self (u : Velocity d) : genBoostAux₂ u u = - genBoostAux₁ u u := by
  ext1 x
  simp only [genBoostAux₂, LinearMap.coe_mk, AddHom.coe_mk, genBoostAux₁, LinearMap.neg_apply]
  rw [neg_smul]
  apply congrArg
  conv => lhs; rhs; rw [← (two_smul ℝ u.val)]
  rw [smul_smul]
  congr 1
  rw [Velocity.minkowskiProduct_self_eq_one u]
  conv => lhs; lhs; rhs; rhs; change 1
  rw [show 1 + (1 : ℝ) = (2 : ℝ) by ring]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [← (two_smul ℝ u.1)]
  simp only [tmul_smul, map_smul, smul_eq_mul]

/-- An generalised boost. This is a Lorentz transformation which takes the four velocity `u`
to `v`. -/
def genBoost (u v : Velocity d) : Vector d →ₗ[ℝ] Vector d :=
  LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v

namespace genBoost

lemma genBoost_mul_one_plus_contr (u v : Velocity d) (x : Vector d) :
    (1 + ⟪u, v.1⟫ₘ) • genBoost u v x =
    (1 + ⟪u, v.1⟫ₘ) • x + (2 * ⟪x, u⟫ₘ * (1 + ⟪u, v.1⟫ₘ)) • v - ⟪x, u + v⟫ₘ • (u + v) := by
  simp only [genBoost, LinearMap.add_apply, LinearMap.id_apply, id_eq]
  rw [smul_add, smul_add]
  trans (1 + ⟪u, v.1⟫ₘ) • x +
    (2 * ⟪x, u⟫ₘ * (1 + ⟪u, v.1⟫ₘ)) • v
    + (- ⟪x, u + v⟫ₘ) • (u + v)
  · congr 1
    · congr 1
      rw [genBoostAux₁]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [smul_smul]
      congr 1
      ring
    · rw [genBoostAux₂]
      simp only [neg_smul, LinearMap.coe_mk, AddHom.coe_mk, smul_neg]
      rw [smul_smul]
      congr
      have h1 := Velocity.one_add_minkowskiProduct_neq_zero u v
      field_simp
  · rw [neg_smul]
    rfl

/--
  This lemma states that for a given four-velocity `u`, the general boost
  transformation `genBoost u u` is equal to the identity linear map `LinearMap.id`.
-/
lemma self (u : Velocity d) : genBoost u u = LinearMap.id := by
  ext x
  simp only [genBoost, LinearMap.add_apply, LinearMap.id_coe, id_eq]
  rw [genBoostAux₂_self]
  simp only [LinearMap.neg_apply, add_neg_cancel_right]

open minkowskiMatrix

lemma genBoostAux₁_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    (genBoostAux₁ u v) (Vector.basis μ) = (2 * η μ μ * toCoord u μ) • v := by
  simp [genBoostAux₁]
  ring_nf

lemma genBoostAux₂_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    (genBoostAux₂ u v) (Vector.basis μ) =
    - (η μ μ * (toCoord u μ + toCoord v μ) / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1) := by
  simp [genBoostAux₂]
  ring_nf

lemma genBoost_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    (genBoost u v) (Vector.basis μ) =
    Vector.basis μ + (2 * η μ μ * toCoord u μ) • v - (η μ μ * (toCoord u μ + toCoord v μ)
      / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1) := by
  simp only [genBoost, LinearMap.add_apply, LinearMap.id_apply, id_eq]
  rw [genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
  congr 1
  simp

/-!

## To Matrix

-/

/-- A generalised boost as a matrix. -/
def toMatrix (u v : Velocity d) : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LinearMap.toMatrix Vector.basis Vector.basis (genBoost u v)

lemma toMatrix_mulVec (u v : Velocity d) (x : Vector d) :
    Matrix.mulVec (toMatrix u v) x.toCoord = (genBoost u v x).toCoord := by
  rw [toMatrix, toMatrix_basis_mulVec_toCoord]

lemma genBoostAux₁_toMatrix_apply (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix Vector.basis Vector.basis (genBoostAux₁ u v)) μ ν =
    η ν ν * (2 * toCoord u ν * toCoord v μ) := by
  rw [LinearMap.toMatrix_apply, basis_repr_apply_eq_toCoord]
  simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, genBoostAux₁,
    LinearMap.coe_mk, AddHom.coe_mk, minkowskiProduct_basis_left, map_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma genBoostAux₂_toMatrix_apply (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix Vector.basis Vector.basis (genBoostAux₂ u v)) μ ν =
      η ν ν * (- ((toCoord u.1 μ) + (toCoord v.1 μ)) * ((toCoord u.1 ν) + (toCoord v.1 ν))
      / (1 + ⟪u.1, v.1⟫ₘ)) := by
  rw [LinearMap.toMatrix_apply, basis_repr_apply_eq_toCoord]
  simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, genBoostAux₂,
    LinearMap.coe_mk, AddHom.coe_mk, minkowskiProduct_basis_left, map_smul, Pi.smul_apply,
    smul_eq_mul]
  have h1 := Velocity.one_add_minkowskiProduct_neq_zero u v
  field_simp
  ring

lemma toMatrix_apply_eq_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (toMatrix u v) μ ν = η μ μ * (⟪Vector.basis μ, Vector.basis ν⟫ₘ + 2 *
    ⟪Vector.basis ν, u⟫ₘ * ⟪Vector.basis μ, v.1⟫ₘ
    - ⟪Vector.basis μ, u + v⟫ₘ * ⟪Vector.basis ν, u + v⟫ₘ / (1 + ⟪u.1, v⟫ₘ)) := by
  conv_lhs =>
    rw [toMatrix, genBoost]
    simp
  conv_rhs =>
    rw [mul_sub, mul_add]
  congr
  · simp
    by_cases h : μ = ν
    · subst h
      simp
    · simp [h]
  · rw [genBoostAux₁_toMatrix_apply u v μ ν]
    simp
    ring_nf
    simp
  · rw [genBoostAux₂_toMatrix_apply u v μ ν]
    simp
    ring_nf
    simp

lemma toMatrix_apply_eq_toCoord (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (toMatrix u v) μ ν = ((1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) μ ν +
    2 * η ν ν * toCoord u ν * toCoord v μ
    - η ν ν * (toCoord u μ + toCoord v μ) * (toCoord u ν + toCoord v ν) / (1 + ⟪u.1, v⟫ₘ)) := by
  conv_lhs =>
    rw [toMatrix, genBoost]
    simp
  congr
  · rw [genBoostAux₁_toMatrix_apply u v μ ν]
    simp
    ring_nf
  · rw [genBoostAux₂_toMatrix_apply u v μ ν]
    simp
    ring_nf

@[fun_prop]
lemma toMatrix_continuous_snd (u : Velocity d) : Continuous (toMatrix u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply_eq_minkowskiProduct]
  refine (continuous_mul_left (η i i)).comp' (?_)
  refine Continuous.sub (by fun_prop) (?_)
  refine .mul (by fun_prop) ?_
  · refine .inv₀ (by fun_prop) ?_
    exact fun x => Velocity.one_add_minkowskiProduct_neq_zero u x

@[fun_prop]
lemma toMatrix_continuous_fst (u : Velocity d) : Continuous (toMatrix · u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply_eq_minkowskiProduct]
  refine (continuous_mul_left (η i i)).comp' (?_)
  refine Continuous.sub (by fun_prop) (?_)
  refine .mul (by fun_prop) ?_
  · refine .inv₀ (by fun_prop) ?_
    exact fun x => Velocity.one_add_minkowskiProduct_neq_zero _ _

/-!

# Proving that `toMatrix` is in the Lorentz group

-/

lemma genBoostAux₁_basis_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ), genBoostAux₁ u v (Vector.basis ν)⟫ₘ =
    4 * η μ μ * η ν ν * toCoord u μ * toCoord u ν := by
  simp [genBoostAux₁]
  ring

lemma genBoostAux₂_basis_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₂ u v (Vector.basis μ), genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    2 * η μ μ * η ν ν * (toCoord u μ + toCoord v μ) * (toCoord u ν + toCoord v ν)
    * (1 + ⟪u, v.1⟫ₘ)⁻¹ := by
  rw [genBoostAux₂_apply_basis, genBoostAux₂_apply_basis]
  rw [map_smul, map_smul]
  have h1 : ⟪u.1 + v.1, u.1 + v.1⟫ₘ = 2 * (1 + ⟪u.1, v.1⟫ₘ) := by
    simp
    rw [minkowskiProduct_symm]
    ring
  dsimp
  rw [h1]
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_neq_zero u v
  field_simp [h2]
  ring

lemma genBoostAux₁_basis_genBoostAux₂_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ), genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    - 2 * η μ μ * η ν ν * toCoord u μ * (toCoord u ν + toCoord v ν) := by
  rw [genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
  rw [map_smul, map_smul]
  have h1 : ⟪ v.1, u.1 + v.1⟫ₘ = (1 + ⟪u.1, v.1⟫ₘ) := by
    simp
    rw [minkowskiProduct_symm]
    ring
  dsimp
  rw [h1]
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_neq_zero u v
  field_simp [h2]
  ring

lemma genBoostAux₁_add_genBoostAux₂_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ) + genBoostAux₂ u v (Vector.basis μ),
    genBoostAux₁ u v (Vector.basis ν) + genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    2 * η μ μ * η ν ν * (- toCoord u μ * (toCoord u ν + toCoord v ν)
      - toCoord u ν * (toCoord u μ + toCoord v μ)
      + (toCoord u μ + toCoord v μ) * (toCoord u ν + toCoord v ν) * (1 + ⟪u, v.1⟫ₘ)⁻¹ +
      2 * toCoord u μ * toCoord u ν) := by
  conv_lhs =>
    simp
    rw [genBoostAux₁_basis_minkowskiProduct, genBoostAux₂_basis_minkowskiProduct,
      genBoostAux₁_basis_genBoostAux₂_minkowskiProduct,
      minkowskiProduct_symm,
      genBoostAux₁_basis_genBoostAux₂_minkowskiProduct]
  ring

lemma basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂ (u v : Velocity d)
    (μ ν : Fin 1 ⊕ Fin d) :
    ⟪Vector.basis μ, genBoostAux₁ u v (Vector.basis ν) + genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    η μ μ * η ν ν * (2 * toCoord u ν * toCoord v μ
    - (toCoord u μ + toCoord v μ) * (toCoord u ν + toCoord v ν) * (1 + ⟪u.1, v.1⟫ₘ)⁻¹) := by
  conv_lhs =>
    rw [map_add]
    rw [genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
    rw [map_smul, map_smul]
    simp
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_neq_zero u v
  field_simp
  ring

lemma toMatrix_in_lorentzGroup (u v : Velocity d) : toMatrix u v ∈ LorentzGroup d := by
  rw [toMatrix]
  rw [← isLorentz_iff_toMatrix_mem_lorentzGroup]
  rw [isLorentz_iff_basis]
  intro μ ν
  rw [genBoost]
  trans ⟪(basis μ) + (genBoostAux₁ u v (basis μ) + genBoostAux₂ u v (basis μ)),
    (basis ν) + (genBoostAux₁ u v (basis ν) + genBoostAux₂ u v (basis ν))⟫ₘ
  · simp only [realLorentzTensor.C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.add_apply, LinearMap.id_coe, id_eq, map_add]
    ring
  rw [map_add]
  conv_lhs =>
    enter [1]
    rw [map_add]
    dsimp
    enter [2]
    rw [minkowskiProduct_symm, basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂]
  conv_lhs =>
    enter [2, 1]
    rw [map_add]
  conv_lhs =>
    enter [2]
    dsimp
    rw [basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂,
      genBoostAux₁_add_genBoostAux₂_minkowskiProduct]
  ring

/-!

## To Lorentz group

-/

TODO "6VZKM" "Make `toLorentz` the definition of a generalised boost. This will involve
  refactoring this file."

/-- A generalised boost as an element of the Lorentz Group. -/
def toLorentz (u v : Velocity d) : LorentzGroup d :=
  ⟨toMatrix u v, toMatrix_in_lorentzGroup u v⟩

lemma toLorentz_continuous (u : Velocity d) : Continuous (toLorentz u) := by
  refine Continuous.subtype_mk ?_ (fun x => toMatrix_in_lorentzGroup u x)
  exact toMatrix_continuous_snd u

lemma toLorentz_joined_to_1 (u v : Velocity d) : Joined 1 (toLorentz u v) := by
  obtain ⟨f, _⟩ := Velocity.isPathConnected.joinedIn u trivial v trivial
  use ContinuousMap.comp ⟨toLorentz u, toLorentz_continuous u⟩ f
  · simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Path.source, ContinuousMap.coe_mk]
    rw [@Subtype.ext_iff, toLorentz]
    simp [toMatrix, self u]
  · simp

lemma toLorentz_in_connected_component_1 (u v : Velocity d) :
    toLorentz u v ∈ connectedComponent 1 :=
  pathComponent_subset_component _ (toLorentz_joined_to_1 u v)

lemma isProper (u v : Velocity d) : IsProper (toLorentz u v) :=
  (isProper_on_connected_component (toLorentz_in_connected_component_1 u v)).mp id_IsProper

lemma isOrthochronous (u v : Velocity d) : IsOrthochronous (toLorentz u v) :=
  (isOrthochronous_on_connected_component (toLorentz_in_connected_component_1 u v)).mp
    id_isOrthochronous

lemma toLorentz_mem_restricted (u v : Velocity d) :
    toLorentz u v ∈ LorentzGroup.restricted d := by
  rw [LorentzGroup.restricted]
  apply And.intro
  · exact isProper u v
  · exact isOrthochronous u v

/--
The time component of a generalised boost is equal to
```
1 +
    ‖u.1.timeComponent • v.1.spatialPart - v.1.timeComponent • u.1.spatialPart‖ / (1 + ⟪u.1, v.1⟫ₘ)
```

A proof of this result can be found at the below link:
https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Lorentz.20group/near/523249684

Note that the decleration of this semiformal result will be similar once
the TODO item `FXQ45` is completed.
-/
semiformal_result "FXNQY" toMatrix_timeComponent_eq (u v : Velocity d) :
  (toMatrix u v) (Sum.inl 0) (Sum.inl 0) = 1 +
    ‖u.1.timeComponent • v.1.spatialPart - v.1.timeComponent • u.1.spatialPart‖ / (1 + ⟪u.1, v.1⟫ₘ)

end genBoost

end LorentzGroup

end
