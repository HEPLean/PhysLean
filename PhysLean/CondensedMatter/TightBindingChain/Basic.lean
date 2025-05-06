/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.TODO.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.QuantumMechanics.FiniteTarget.HilbertSpace
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

/-- The physical parameters making up the tight binding chain. -/
structure TightBindingChain where
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

TODO "BQS7X" "The definition of the Hilbert space in the tight binding chian
  should be moved to the generic folder for finite-dimensional quantum mechanical systems."

/-- The Hilbert space of a `TightBindingchain` is the `N`-dimensional finite dimensional
Hilbert space. -/
abbrev HilbertSpace := QuantumMechanics.FiniteHilbertSpace T.N

/-- The eigenstate corresponding to the particle been located on the `n`th site. -/
noncomputable def localizedState {T : TightBindingChain} :
    OrthonormalBasis (Fin T.N) ℂ (HilbertSpace T) :=
  EuclideanSpace.basisFun (Fin T.N) ℂ

@[inherit_doc localizedState]
scoped notation "|" n "⟩" => localizedState n

/-- The inner product of two localized states. -/
scoped notation "⟨" m "|" n "⟩" => ⟪localizedState m, localizedState n⟫_ℂ

/-- The localized states are normalized. -/
lemma localizedState_orthonormal : Orthonormal ℂ (localizedState (T := T)) :=
  (localizedState (T := T)).orthonormal

/-- The linear map `|m⟩⟨n|` for `⟨n|` localized states. -/
noncomputable def localizedComp {T : TightBindingChain} (m n : Fin T.N) :
    T.HilbertSpace →ₗ[ℂ] T.HilbertSpace where
  toFun ψ := ⟪|n⟩, ψ⟫_ℂ • |m⟩
  map_add' ψ1 ψ2 := by
    rw [inner_add_right]
    simp [add_smul]
  map_smul' _ _ := by
    rw [inner_smul_right]
    simp [smul_smul]

@[inherit_doc localizedComp]
scoped notation "|" n "⟩⟨" m "|" => localizedComp n m

lemma localizedComp_apply_localizedState (m n p : Fin T.N) :
    |m⟩⟨n| |p⟩ = if n = p then |m⟩ else 0 := by
  rw [localizedComp]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [orthonormal_iff_ite.mp T.localizedState_orthonormal n p]
  simp

/-- The Hamiltonian of the tight binding chain is given by
  `E₀ ∑ n, |n⟩⟨n| - t ∑ n,(|n⟩⟨n + 1| + |n + 1⟩⟨n|)`. -/
noncomputable def hamiltonian : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.E0 • ∑ n : Fin T.N, |n⟩⟨n| - T.t • ∑ n : Fin T.N, ∑ m : Fin T.N,
    if n.val = m.val + 1 then |n⟩⟨m| + |m⟩⟨n| else 0

/-- The Brillouin zone of the tight binding model is `[-π/a, π/a)`.
  This is the set in which wave functions are uniquly defined. -/
def BrillouinZone : Set ℝ := Set.Ico (- Real.pi / T.a) (Real.pi / T.a)

/-- The energy eigenstates of the tight binding chain. -/
noncomputable def energyEigenstate (k : T.BrillouinZone) : T.HilbertSpace :=
  ∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • |n⟩

/-- The energy eigenvalue of the tight binding chain for a `k` in the `BrillouinZone`. -/
noncomputable def energyEigenvalue (k : T.BrillouinZone) : ℝ :=
  T.E0 - 2 * T.t * Real.cos (k * T.a)

end TightBindingChain
end CondensedMatter
