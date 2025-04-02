/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Basic
/-!

# Construction from the constant maps

Given a morphism in `Rep k G` to a representation isomorphisc to `Tensor S c`,
we get an invariant tensor of type `Tensor S c`.

This is used in the construction of metric tensors, unit tensors, and the Pauli matrices.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {G : Type} [Group G] {S : TensorSpecies k G}

namespace Tensor

/-- A general constant node. -/
def fromConst {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep k G) ⟶ S.F.obj (OverColor.mk c)) :
    Tensor S c := (T.hom (1 : k))

/-- A constant two tensor (e.g. metric and unit). -/
noncomputable def fromConstPair {c1 c2 : S.C}
      (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2)) :
      S.Tensor ![c1, c2] := (OverColor.Discrete.pairIsoSep S.FD).hom.hom (v.hom (1 : k))

/-- A constant three tensor (e.g. the Pauli matrices). -/
noncomputable def fromConstTriple {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
      S.FD.obj (Discrete.mk c3)) :
    S.Tensor ![c1, c2, c3] := (OverColor.Discrete.tripleIsoSep S.FD).hom.hom (v.hom (1 : k))

/-!

## Actions on tensors constructed from morphisms

Tensors constructed from morphisms are invariant under the group action.

-/

/-- Tensors formed by `fromConst` are invariant under the group action. -/
@[simp]
lemma actionT_fromConst {n : ℕ} {c : Fin n → S.C} (T : 𝟙_ (Rep k G) ⟶ S.F.obj (OverColor.mk c))
    (g : G) : g • fromConst T = fromConst T:= by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    fromConstPair]
  change ((T.hom ≫ ModuleCat.ofHom ((S.F.obj _).ρ g))) _ = _
  erw [← T.comm g]
  simp [fromConst]

/-- Tensors formed by `fromConstPair` are invariant under the group action. -/
@[simp]
lemma actionT_fromConstPair {c1 c2 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2))
    (g : G) : g • fromConstPair v = fromConstPair v := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    fromConstPair]
  change ((Discrete.pairIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2])).ρ g)) (v.hom _) = _
  erw [← (Discrete.pairIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 }).ρ g)) ≫
    (Discrete.pairIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp

/-- An `action` node on a `constThreeNode` leaves the tensor invariant. -/
@[simp]
lemma action_fromConstTriple {c1 c2 c3 : S.C}
    (v : 𝟙_ (Rep k G) ⟶ S.FD.obj (Discrete.mk c1) ⊗ S.FD.obj (Discrete.mk c2) ⊗
      S.FD.obj (Discrete.mk c3))
    (g : G) : g • fromConstTriple v = fromConstTriple v := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, actionT_eq, fromConstTriple,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  change ((Discrete.tripleIsoSep S.FD).hom.hom ≫
    ModuleCat.ofHom ((S.F.obj (OverColor.mk ![c1, c2, c3])).ρ g)) (v.hom _) = _
  erw [← (Discrete.tripleIsoSep S.FD).hom.comm g]
  change ((v.hom ≫ ModuleCat.ofHom ((S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 } ⊗
    S.FD.obj { as := c3 }).ρ g)) ≫ (Discrete.tripleIsoSep S.FD).hom.hom) _ = _
  erw [← v.comm g]
  simp

end Tensor

end TensorSpecies
