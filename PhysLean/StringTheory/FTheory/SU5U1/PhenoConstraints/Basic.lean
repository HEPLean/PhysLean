/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Meta.Informal.SemiFormal
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
- `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
(These are the interactions with an odd number of matter fields.)


The following terms are involved in proton-decay:
- `W¹`, `W²`, `K¹`, `λ`

In what follows we constrain via `U(1)` charges
- `μ` (C1 in 1507.05961)
- `𝛽ᵢ` (C3 in 1507.05961)
- `𝜆ᵢⱼₖ` (C4 in 1507.05961)
- `W¹ᵢⱼₖₗ` (C2 in 1507.05961)
- `W²ᵢⱼₖ` (C2 (?) in 1507.05961)
- `K¹ᵢⱼₖ` (C5 in 1507.05961)
- `W⁴ᵢ` (C6 in 1507.05961)
- `K²ᵢ` (C7 in 1507.05961)
-/

namespace FTheory

namespace SU5U1
namespace MatterContent
variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-- A proposition which is true when the `μ`-term (`5Hu 5̄Hd`) does not obey the additional
  `U(1)` symmetry in the model, and is therefore constrained. -/
def MuTermU1Constrained : Prop := - 𝓜.qHu.1 + 𝓜.qHd.1 ≠ 0

instance : Decidable 𝓜.MuTermU1Constrained := instDecidableNot

/-- A proposition which is true
  when the R-parity violating terms all do not obey the additional
  `U(1)` symmetry in the model, and are therefore constrained.
  This corresponds to the terms:
- `𝛽ᵢ 5̄Mⁱ5Hu`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
- `K¹ᵢⱼₖ  10ⁱ 10ʲ 5Mᵏ`
- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
-/
def RParityU1Constrained : Prop :=
  --`𝛽ᵢ 5̄Mⁱ5Hu`
  (∀ fi ∈ 𝓜.quantaBarFiveMatter, fi.q.1 + (- 𝓜.qHu.1) ≠ 0)
  -- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
  ∧ (∀ fi ∈ 𝓜.quantaBarFiveMatter, ∀ fj ∈ 𝓜.quantaBarFiveMatter, ∀ tk ∈ 𝓜.quantaTen,
    fi.q.1 + fj.q.1 + tk.q.1 ≠ 0)
  -- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
  ∧ (∀ ti ∈ 𝓜.quantaTen, ∀ tj ∈ 𝓜.quantaTen, ∀ tk ∈ 𝓜.quantaTen,
    ti.q.1 + tj.q.1 + tk.q.1 + 𝓜.qHd.1 ≠ 0)
  -- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
  ∧ (∀ fi ∈ 𝓜.quantaBarFiveMatter, fi.q.1 + 𝓜.qHd.1 + (- 𝓜.qHu.1) + (- 𝓜.qHu.1) ≠ 0)
  -- `K¹ᵢⱼₖ  10ⁱ 10ʲ 5Mᵏ`
  ∧ (∀ ti ∈ 𝓜.quantaTen, ∀ tj ∈ 𝓜.quantaTen, ∀ fk ∈ 𝓜.quantaBarFiveMatter,
    ti.q.1 + tj.q.1 + (- fk.q.1) ≠ 0)
  -- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
  ∧ (∀ ti ∈ 𝓜.quantaTen, 𝓜.qHu.1 + 𝓜.qHd.1 + ti.q.1 ≠ 0)

instance : Decidable 𝓜.RParityU1Constrained := instDecidableAnd

/-- A proposition which is true when the terms in the super-potential and the Kahler potential
  contributing to proton decay do not obey the additional `U(1)` symmetry in the model,
  and are therefore constrained.
  This corresponds to the terms
- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `K¹ᵢⱼₖ  10ⁱ 10ʲ 5Mᵏ`
-/
def ProtonDecayU1Constrained : Prop :=
  -- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
  (∀ ti ∈ 𝓜.quantaTen, ∀ tj ∈ 𝓜.quantaTen, ∀ tk ∈ 𝓜.quantaTen, ∀ fl ∈ 𝓜.quantaBarFiveMatter,
    ti.q.1 + tj.q.1 + tk.q.1 + fl.q.1 ≠ 0)
  -- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
  ∧ (∀ fi ∈ 𝓜.quantaBarFiveMatter, ∀ fj ∈ 𝓜.quantaBarFiveMatter, ∀ tk ∈ 𝓜.quantaTen,
    fi.q.1 + fj.q.1 + tk.q.1 ≠ 0)
  -- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
  ∧ (∀ ti ∈ 𝓜.quantaTen, ∀ tj ∈ 𝓜.quantaTen, ∀ tk ∈ 𝓜.quantaTen,
    ti.q.1 + tj.q.1 + tk.q.1 + 𝓜.qHd.1 ≠ 0)
  -- `K¹ᵢⱼₖ  10ⁱ 10ʲ 5Mᵏ`
  ∧ (∀ ti ∈ 𝓜.quantaTen, ∀ tj ∈ 𝓜.quantaTen, ∀ fk ∈ 𝓜.quantaBarFiveMatter,
    ti.q.1 + tj.q.1 + (- fk.q.1) ≠ 0)

instance : Decidable 𝓜.ProtonDecayU1Constrained := instDecidableAnd

/-- The condition on the matter content for there to exist at least one copy of the coupling
- `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`
-/
def HasATopYukawa  (𝓜 : MatterContent I) : Prop := ∃ ti ∈ 𝓜.quantaTen,  ∃ tj ∈ 𝓜.quantaTen,
  ti.q.1 + tj.q.1 + (- 𝓜.qHu.1)  = 0

instance : Decidable 𝓜.HasATopYukawa :=
  haveI : DecidablePred fun (ti : QuantaTen I) =>
      ∃ tj ∈ 𝓜.quantaTen, ti.q.1 + ↑tj.q + -↑𝓜.qHu = 0 := fun _ =>
        Multiset.decidableExistsMultiset
  Multiset.decidableExistsMultiset

/-- The condition on the matter content for there to exist at least one copy of the coupling
- `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd`
-/
def HasABottomYukawa (𝓜 : MatterContent I) : Prop := ∃ ti ∈ 𝓜.quantaTen,
  ∃ fj ∈ 𝓜.quantaBarFiveMatter,
  ti.q.1 + fj.q.1 + 𝓜.qHd.1 = 0

instance : Decidable 𝓜.HasABottomYukawa :=
  haveI : DecidablePred fun (ti : QuantaTen I) =>
      ∃ fj ∈ 𝓜.quantaBarFiveMatter, ti.q.1 + fj.q.1 + 𝓜.qHd.1 = 0 := fun _ =>
        Multiset.decidableExistsMultiset
  Multiset.decidableExistsMultiset

end MatterContent
end SU5U1

end FTheory
