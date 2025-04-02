/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.FromConst
/-!

# The unit tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {G : Type} [Group G] {S : TensorSpecies k G}

open Tensor

/-- The unit tensor associated with a color `c`. -/
noncomputable def unitTensor (c : S.C) : S.Tensor ![S.τ c, c] :=
  fromConstPair (S.unit.app (Discrete.mk c))

lemma unitTensor_congr {c c1 : S.C} (h : c = c1) :
    unitTensor c = permT id (by simp [h]) (unitTensor c1) := by
  subst h
  simp

lemma unit_app_eq_dual_unit_app (c : S.C) :
    (S.unit.app (Discrete.mk c)) = (S.unit.app ({ as := S.τ c })) ≫
      (β_ (S.FD.obj ({ as := S.τ (S.τ c) })) (S.FD.obj ({ as := S.τ c }))).hom ≫
      ((S.FD.obj ({ as := S.τ c } : Discrete S.C) ◁ S.FD.map (Discrete.eqToHom (by simp)))) := by
  ext
  change (ConcreteCategory.hom (S.unit.app { as := c }).hom) (1 : k)  = _
  rw [ S.unit_symm c]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_whiskerLeft_hom,
    Action.β_hom_hom, Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
    Action.comp_hom, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rfl

/-- The unit tensor is symmetric on dualing the color. -/
lemma unitTensor_eq_permT_dual (c : S.C) :
    unitTensor c = permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
    (unitTensor (S.τ c)) := by
  rw [unitTensor, unit_app_eq_dual_unit_app, ← Category.assoc]
  rw [fromConstPair_whiskerLeft, fromConstPair_braid]
  simp
  rfl

lemma dual_unitTensor_eq_permT_unitTensor (c : S.C) :
    unitTensor (S.τ c) = permT ![1, 0] (And.intro (by decide) (fun i => by fin_cases i <;> simp))
      (unitTensor c) := by
  rw [unitTensor_eq_permT_dual]
  rw [unitTensor_congr (by simp : c = S.τ (S.τ c))]
  simp



end TensorSpecies
