/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.TODO.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!

# The tight binding chain

The tight binding chain corresponds to an electron in motion
in a 1d solid with the assumption the electron can sit only on the atoms of the solid.

The solid is assumed to consist of `N` sites with a seperation of `a` between them.

Mathematically, the tight binding chain corresponds to a
QM problem located on a lattice with only self and nearest neighbour integractions.

## Refs.

- https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf

-/

TODO "BBZAB" "Prove results related to the one-dimensional tight binding chain.
  This is related to the following issue/feature-request:
  https://github.com/HEPLean/PhysLean/issues/523 "

namespace CondensedMatter

structure TightBindingChain  where
  /-- The number of sites, or atoms, in the chain -/
  N : Nat
  /-- The distance between the sites -/
  a : ℝ
  /-- The energy associate with a particle sitting at a fixed site. -/
  E0 : ℝ
  /-- The hopping parameter. -/
  t : ℝ

namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-- The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional
Hilbert space. -/
abbrev HilbertSpace := EuclideanSpace ℂ (Fin T.N)

/-- The eigenstate corresponding to the particle been located on the `n`th site. -/
noncomputable def localizedState {T : TightBindingChain} (n : Fin T.N) : HilbertSpace T :=
  EuclideanSpace.single n 1

@[inherit_doc localizedState]
scoped notation "|" n "⟩" => localizedState n

/-- The inner product of two localized states. -/
scoped notation "⟨" m "|" n "⟩" => ⟪localizedState m, localizedState n⟫_ℝ

end TightBindingChain
end CondensedMatter
