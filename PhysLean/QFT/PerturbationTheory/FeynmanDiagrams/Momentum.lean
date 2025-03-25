/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.Dimension.Finrank
/-!
# Momentum in Feynman diagrams

The aim of this file is to associate with each half-edge of a Feynman diagram a momentum,
and constrain the momentums based conservation at each vertex and edge.

The number of loops of a Feynman diagram is related to the dimension of the resulting
vector space.

## TODO

- Prove lemmas that make the calculation of the number of loops of a Feynman diagram easier.

## Note

This section is non-computable as we depend on the norm on `F.HalfEdgeMomenta`.
-/

namespace FeynmanDiagram

open CategoryTheory
open PreFeynmanRule

variable {P : PreFeynmanRule} (F : FeynmanDiagram P) [IsFiniteDiagram F]

/-!

## Vector spaces associated with momenta in Feynman diagrams.

We define the vector space associated with momenta carried by half-edges,
outflowing momenta of edges, and inflowing momenta of vertices.

We define the direct sum of the edge and vertex momentum spaces.

-/

/-- The type which associates to each half-edge a `1`-dimensional vector space.
  Corresponding to that spanned by its momentum. -/
def HalfEdgeMomenta : Type := F.𝓱𝓔 → ℝ

/-- The half momenta carries the structure of an additive commutative group. -/
instance : AddCommGroup F.HalfEdgeMomenta := Pi.addCommGroup

/-- The half momenta carries the structure of a module over `ℝ`. Defined via its target. -/
instance : Module ℝ F.HalfEdgeMomenta := Pi.module _ _ _

/-- An auxiliary function used to define the Euclidean inner product on `F.HalfEdgeMomenta`. -/
def euclidInnerAux (x : F.HalfEdgeMomenta) : F.HalfEdgeMomenta →ₗ[ℝ] ℝ where
  toFun y := ∑ i, (x i) * (y i)
  map_add' z y :=
    show (∑ i, (x i) * (z i + y i)) = (∑ i, x i * z i) + ∑ i, x i * (y i) by
      simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c y :=
    show (∑ i, x i * (c * y i)) = c * ∑ i, x i * y i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma euclidInnerAux_symm (x y : F.HalfEdgeMomenta) :
    F.euclidInnerAux x y = F.euclidInnerAux y x := Finset.sum_congr rfl (fun _ _ => by ring)

/-- The Euclidean inner product on `F.HalfEdgeMomenta`. -/
def euclidInner : F.HalfEdgeMomenta →ₗ[ℝ] F.HalfEdgeMomenta →ₗ[ℝ] ℝ where
  toFun x := F.euclidInnerAux x
  map_add' x y := by
    refine LinearMap.ext (fun z => ?_)
    simp only [euclidInnerAux_symm, map_add, LinearMap.add_apply]
  map_smul' c x := by
    refine LinearMap.ext (fun z => ?_)
    simp only [euclidInnerAux_symm, LinearMapClass.map_smul, smul_eq_mul, RingHom.id_apply,
      LinearMap.smul_apply]

/-- The type which associates to each edge a `1`-dimensional vector space.
  Corresponding to that spanned by its total outflowing momentum. -/
def EdgeMomenta : Type := F.𝓔 → ℝ

/-- The edge momenta form an additive commutative group. -/
instance : AddCommGroup F.EdgeMomenta := Pi.addCommGroup

/-- The edge momenta form a module over `ℝ`. -/
instance : Module ℝ F.EdgeMomenta := Pi.module _ _ _

/-- The type which associates to each edge a `1`-dimensional vector space.
  Corresponding to that spanned by its total inflowing momentum. -/
def VertexMomenta : Type := F.𝓥 → ℝ

/-- The vertex momenta carries the structure of an additive commutative group. -/
instance : AddCommGroup F.VertexMomenta := Pi.addCommGroup

/-- The vertex momenta carries the structure of a module over `ℝ`. -/
instance : Module ℝ F.VertexMomenta := Pi.module _ _ _

/-- The map from `Fin 2` to `Type` landing on `EdgeMomenta` and `VertexMomenta`. -/
def EdgeVertexMomentaMap : Fin 2 → Type := fun i =>
  match i with
  | 0 => F.EdgeMomenta
  | 1 => F.VertexMomenta

/-- The target of the map `EdgeVertexMomentaMap` is either the type of edge momenta
  or vertex momenta and thus carries the structure of an additive commutative group. -/
instance (i : Fin 2) : AddCommGroup (EdgeVertexMomentaMap F i) :=
  match i with
  | 0 => instAddCommGroupEdgeMomenta F
  | 1 => instAddCommGroupVertexMomenta F

/-- The target of the map `EdgeVertexMomentaMap` is either the type of edge momenta
  or vertex momenta and thus carries the structure of a module over `ℝ`. -/
instance (i : Fin 2) : Module ℝ (EdgeVertexMomentaMap F i) :=
  match i with
  | 0 => instModuleRealEdgeMomenta F
  | 1 => instModuleRealVertexMomenta F

/-- The direct sum of `EdgeMomenta` and `VertexMomenta`. -/
def EdgeVertexMomenta : Type := DirectSum (Fin 2) (EdgeVertexMomentaMap F)

/-- The structure of a additive commutative group on `EdgeVertexMomenta` for a
  Feynman diagram `F`. -/
instance : AddCommGroup F.EdgeVertexMomenta := DirectSum.instAddCommGroup _

/-- The structure of a module over `ℝ` on `EdgeVertexMomenta` for a Feynman diagram `F`. -/
instance : Module ℝ F.EdgeVertexMomenta := DirectSum.instModule

/-!

## Linear maps between the vector spaces.

We define various maps into `F.HalfEdgeMomenta`.

In particular, we define a map from `F.EdgeVertexMomenta` to `F.HalfEdgeMomenta`. This
map represents the space orthogonal (with respect to the standard Euclidean inner product)
to the allowed momenta of half-edges (up-to an offset determined by the
external momenta).

The number of loops of a diagram is defined as the number of half-edges minus
the rank of this matrix.

-/

/-- The linear map from `F.EdgeMomenta` to `F.HalfEdgeMomenta` induced by
  the map `F.𝓱𝓔To𝓔.hom`. -/
def edgeToHalfEdgeMomenta : F.EdgeMomenta →ₗ[ℝ] F.HalfEdgeMomenta where
  toFun x := x ∘ F.𝓱𝓔To𝓔.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear map from `F.VertexMomenta` to `F.HalfEdgeMomenta` induced by
  the map `F.𝓱𝓔To𝓥.hom`. -/
def vertexToHalfEdgeMomenta : F.VertexMomenta →ₗ[ℝ] F.HalfEdgeMomenta where
  toFun x := x ∘ F.𝓱𝓔To𝓥.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear map from `F.EdgeVertexMomenta` to `F.HalfEdgeMomenta` induced by
  `F.edgeToHalfEdgeMomenta` and `F.vertexToHalfEdgeMomenta`. -/
def edgeVertexToHalfEdgeMomenta : F.EdgeVertexMomenta →ₗ[ℝ] F.HalfEdgeMomenta :=
  DirectSum.toModule ℝ (Fin 2) F.HalfEdgeMomenta
    (fun i => match i with | 0 => F.edgeToHalfEdgeMomenta | 1 => F.vertexToHalfEdgeMomenta)

/-!

## Submodules

We define submodules of `F.HalfEdgeMomenta` which correspond to
the orthogonal space to allowed momenta (up-to an offset), and the space of
allowed momenta.

-/

/-- The submodule of `F.HalfEdgeMomenta` corresponding to the range of
  `F.edgeVertexToHalfEdgeMomenta`. -/
def orthogHalfEdgeMomenta : Submodule ℝ F.HalfEdgeMomenta :=
  LinearMap.range F.edgeVertexToHalfEdgeMomenta

/-- The submodule of `F.HalfEdgeMomenta` corresponding to the allowed momenta. -/
def allowedHalfEdgeMomenta : Submodule ℝ F.HalfEdgeMomenta :=
  Submodule.orthogonalBilin F.orthogHalfEdgeMomenta F.euclidInner

/-!

## Number of loops

We define the number of loops of a Feynman diagram as the dimension of the
allowed space of half-edge momenta.

-/

/-- The number of loops of a Feynman diagram. Defined as the dimension
  of the space of allowed Half-loop momenta. -/
noncomputable def numberOfLoops : ℕ := Module.finrank ℝ F.allowedHalfEdgeMomenta

/-!

## Lemmas regarding `numberOfLoops`

We now give a series of lemmas which be used to help calculate the number of loops
for specific Feynman diagrams.

### TODO

- Complete this section.

-/

/-!

## Category theory

### TODO

- Complete this section.

-/

end FeynmanDiagram
