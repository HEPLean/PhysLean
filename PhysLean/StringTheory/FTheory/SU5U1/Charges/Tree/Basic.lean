/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Combinatorics.Additive.Dissociation
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
import PhysLean.Mathematics.DataStructures.FourTree.Basic
/-!

# Trees of charges

Naively one might which to store charges in `Mutliset Charges`.
However, this is not very efficent in terms of memory not membership checks.
Thus in this section we define a tree structure to store charges.
Our tree type is isomorphic to
`Option ℤ × Multiset (Option ℤ × Multiset (Finset ℤ × Multiset (Finset ℤ)))`,
although defined inductively.

We give definitions converting to and from `Mutliset Charges`.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges

open PotentialTerm

end Charges

end SU5U1

end FTheory
