/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype
import PhysLean.StringTheory.FTheory.SU5U1.Charges
/-!

# Potential of the SU(5) + U(1) GUT for F-Theory

This file contains properties of the potential terms of the `SU(5)` SUSY GUT with an
additional `U(1)` gauge group in F-theory.

The terms from the superpotential considered are (arXiv:0912.0853) :
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

The terms of the Kahler potential are (arXiv:0912.0853) :
`K ⊃ K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

## Important results

- `PotentialTerm` : The inductive type indexing the potential terms.
- `violateRParity` : The finite set of terms which violate R-parity.
  `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
- `causeProtonDecay` : The finite set of terms which contribute to proton decay.
  `W¹`, `W²`, `K¹`, `λ`
- `IsPresent`: The condition on the potential terms for them to be present
  based on the `U(1)` charges.

## Previous versions

A previous version of this code was replaced in PR #569.

-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- Relevant terms part of the superpotential and Kahler potential of the `SU(5)` SUSY GUT. -/
inductive PotentialTerm
  /-- The term `μ 5Hu 5̄Hd`. -/
  | μ : PotentialTerm
  /-- The term `𝛽ᵢ 5̄Mⁱ5Hu`. -/
  | β : PotentialTerm
  /-- The term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`. -/
  | Λ : PotentialTerm
  /-- The term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` -/
  | W1 : PotentialTerm
  /-- The term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`. -/
  | W2 : PotentialTerm
  /-- The term `W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu`. -/
  | W3 : PotentialTerm
  /-- The term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`. -/
  | W4 : PotentialTerm
  /-- The term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`. -/
  | K1 : PotentialTerm
  /-- The term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` -/
  | K2 : PotentialTerm
  /-- The term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`. -/
  | topYukawa : PotentialTerm
  /-- The term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd`. -/
  | bottomYukawa : PotentialTerm
deriving DecidableEq, Fintype

namespace PotentialTerm

/-- The finite set of terms in the superpotential and Kahler potential which violate R-parity.
- `𝛽ᵢ 5̄Mⁱ5Hu`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
These correspond to the terms with an odd number of matter fields.
-/
def violateRParity : Finset PotentialTerm :=
  {β, Λ, W2, W4, K1, K2}

/-- The finite set of terms in the superpotential and Kahler potential which are involved in
  proton decay.
- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
-/
def causeProtonDecay : Finset PotentialTerm :=
  {W1, Λ, W2, K1}

end PotentialTerm

end SU5U1

end FTheory
