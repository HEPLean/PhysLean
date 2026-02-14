/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Algebra.Ring.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Kronecker delta

This file defines the Kronecker delta, `δ[i,j] ≔ if (i = j) then 1 else 0`.

-/
TODO "YVABB" "Build functionality for working with sums involving Kronecker deltas."

namespace KroneckerDelta

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kronecker_delta [Ring R] (i j : Fin d) : R := if (i = j) then 1 else 0

@[inherit_doc kronecker_delta]
macro "δ[" i:term "," j:term "]" : term => `(kronecker_delta $i $j)

lemma kronecker_delta_symm [Ring R] (i j : Fin d) :
    kronecker_delta (R := R) i j = kronecker_delta j i :=
  ite_cond_congr (Eq.propIntro Eq.symm Eq.symm)

lemma kronecker_delta_self [Ring R] : ∀ i : Fin d, kronecker_delta (R := R) i i = 1 := by
  intro i
  exact if_pos rfl

end KroneckerDelta
