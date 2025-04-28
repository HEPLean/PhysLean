/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

## Phenomenological constraints on matter content

In arXiv:1507.05961, the authors give a number of phenomenological constraints on
the matter content of the SU(5) GUT model in F-theory with an additional U(1) symmetry.

Important terms coming from the superpotential are (0912.0853):
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

Important terms coming from the Kahler potential are (0912.0853):
`K ⊃ K¹ᵢⱼₖ  10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

The following terms break R-parity:
- β, λ, W², W⁴, K¹, K²

The following terms are involved in proton-decay:
- W¹, W², K¹, λ

In what follows we constrain
- `μ` (C1 in 1507.05961)
- `𝛽ᵢ` (C3 in 1507.05961)
- `𝜆ᵢⱼₖ` (C4 in 1507.05961)
- `W¹ᵢⱼₖₗ` (C2 in 1507.05961)
- `W²ᵢⱼₖ` (C2 (?) in 1507.05961)
- `K¹ᵢⱼₖ` (C5 in 1507.05961)
- `W⁴ᵢ` (C6 in 1507.05961)
- `K²ᵢ` (C7 in 1507.05961)
-/
