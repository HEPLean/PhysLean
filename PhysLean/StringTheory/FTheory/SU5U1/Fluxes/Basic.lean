/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Fluxes

Associated with each matter curve `Σ` are `G₄`-fluxes and `hypercharge` fluxes.

For a given matter curve `Σ`, and a Standard Model representation `R`,
these two fluxes contribute to the chiral index `χ(R)` of the representation
(eq 17 of [1]).

The chiral index is equal to the difference the number of left-handed minus
the number of right-handed fermions `Σ` leads to in the representation `R`.
Thus, for example, if `χ(R) = 0`, then all fermions in the representation `R`
arising from `Σ` arise in vector-like pairs, and can be given a mass term without
the presence of a Higgs like-particle.

For a 10d representation matter curve the non-zero chiral indices can be parameterized in terms
of two integers `M : ℤ` and `N : ℤ`. For the SM representation
-  `(3,2)_{1/6}` the chirality index is `M`
-  `(bar 3,1)_{-2/3}` the chirality index is `M - N`
-  `(1,1)_{1}` the chirality index is `M + N`
We call refer to `M` as the chirality flux of the 10d representation, and
`N` as the hypercharge flux. There exact definitions are given in (eq 19 of [1]).

Similarly, for the 5-bar representation matter curve the non-zero chiral indices can be
likewise be parameterized in terms of two integers `M : ℤ` and `N : ℤ`. For the SM representation
-  `(bar 3,1)_{1/3}` the chirality index is `M`
- `(1,2)_{-1/2}` the chirality index is `M + N`
We again refer to `M` as the chirality flux of the 5-bar representation, and
`N` as the hypercharge flux. The exact definitions are given in (eq 19 of [1]).

If one wishes to put the condition of no chiral exotics in the spectrum, then
we must ensure that the chiral indices above give the chiral content of the MSSM.
These correspond to the following conditions:
1. The two higgs `Hu` and `Hd` must arise from different 5d-matter curves. Otherwise
   they will give a `μ`-term.
2. The matter curve containing `Hu` must give one anti-chiral `(1,2)_{-1/2}` and
   no `(bar 3,1)_{1/3}`. Thus `N = -1` and `M = 0`.
3. The matter curve containing `Hd` must give one chiral `(1,2)_{-1/2}` and
    no `(bar 3,1)_{1/3}`. Thus `N = 1` and `M = 0`.
4. We should have no anti-chiral `(3,2)_{1/6}` and anti-chiral `(bar 3,1)_{-2/3}`.
   Thus `0 ≤ M ` for all 10d-matter curves and 5d matter curves.
5. For the 10d-matter curves we should have no anti-chiral `(bar 3,1)_{-2/3}`
    and no anti-chiral `(1,1)_{1}`. Thus `-M ≤ N ≤ M` for all 10d-matter curves.
6. For the 5d-matter curves we should have no anti-chiral `(1,2)_{-1/2}` (the only
   anti-chiral one present is the one from `Hu`) and thus
  `-M ≤ N` for all 5d-matter curves.
7. To ensure we have 3-families of fermions we must have that `∑ M = 3` and
   `∑ N = 0` for the matter 10d and 5bar matter curves, and in addition `∑ (M + N) = 3` for the
    matter 5d matter curves.
See the conditions in equation 26 - 28 of [1].

## Implmentation

The above theory is implemented by defining two data structures:
- `FluxesTen` of type `Multiset (ℤ × ℤ)` which contains the chirality `M` and hypercharge fluxes
  `N` of the 10d-matter curves.
- `FluxesFive` of type `Multiset (ℤ × ℤ)` which contains the chirality `M` and hypercharge fluxes
  `N` of the 5-bar-matter curves (excluding the higges).

Note: Neither `FluxesTen` or `FluxesFive` are fundamental to the theory,
they can be derived from other data structures.

## References

- [1] arXiv:1401.5084

-/
namespace FTheory

namespace SU5U1

end SU5U1

end FTheory
