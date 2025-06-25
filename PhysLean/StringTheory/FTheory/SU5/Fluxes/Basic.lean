/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
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
- `Q = (3,2)_{1/6}` the chirality index is `M`
- `U = (bar 3,1)_{-2/3}` the chirality index is `M - N`
- `E = (1,1)_{1}` the chirality index is `M + N`
We call refer to `M` as the chirality flux of the 10d representation, and
`N` as the hypercharge flux. There exact definitions are given in (eq 19 of [1]).

Similarly, for the 5-bar representation matter curve the non-zero chiral indices can be
likewise be parameterized in terms of two integers `M : ℤ` and `N : ℤ`. For the SM representation
- `D = (bar 3,1)_{1/3}` the chirality index is `M`
- `L = (1,2)_{-1/2}` the chirality index is `M + N`
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
- `FluxesTen` of type `Multiset (ℤ × ℤ)`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 10d-matter curves.
- `FluxesFive` of type `Multiset (ℤ × ℤ)`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 5-bar-matter curves (excluding the higges).

Note: Neither `FluxesTen` or `FluxesFive` are fundamental to the theory,
they can be derived from other data structures.

## Previous version

A previous version of this code was replaced in the PR #569.

## References

- [1] arXiv:1401.5084

-/
namespace FTheory

namespace SU5

/-!

## Fluxes of the 5d matter representation

-/

/-- The fluxes `(M, N)` of the 5-bar matter curves of a theory. -/
abbrev FluxesFive : Type := Multiset (ℤ × ℤ)

namespace FluxesFive

instance : DecidableEq FluxesFive :=
  inferInstanceAs (DecidableEq (Multiset (ℤ × ℤ)))

/-- The proposition on `FluxesFive` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesFive) : Prop := (0, 0) ∉ F

/-!

## The SM representation `D = (bar 3,1)_{1/3}`

-/

/-- The multiset of chiral indices of the representation `D = (bar 3,1)_{1/3}`
  arrising from the matter 5d representations. -/
def chiralIndicesOfD (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.1)

/-- The total number of chiral `D` representations arrising from the matter 5d
  representations. -/
def numChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => 0 ≤ x)).sum

/-- The total number of anti-chiral `D` representations arrising from the matter 5d
  representations. -/
def numAntiChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => x < 0)).sum

/-!

## The SM representation `L = (1,2)_{-1/2}`

-/

/-- The multiset of chiral indices of the representation `L = (1,2)_{-1/2}`
  arrising from the matter 5d representations. -/
def chiralIndicesOfL (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.1 + f.2)

/-- The total number of chiral `L` representations arrising from the matter 5d
  representations. -/
def numChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => 0 ≤ x)).sum

/-- The total number of anti-chiral `L` representations arrising from the matter 5d
  representations. -/
def numAntiChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => x < 0)).sum

/-!

## The condition for no exotics

-/

/-- The condition that the 5d-matter represenations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `L` representations and no anti-chiral `L` representations.
- There are 3 chiral `D` representations and no anti-chiral `D` representations.
-/
def NoExotics (F : FluxesFive) : Prop :=
  F.numChiralL = 3 ∧ F.numAntiChiralL = 0 ∧ F.numChiralD = 3 ∧ F.numAntiChiralD = 0

instance (F : FluxesFive) : Decidable (F.NoExotics) :=
  instDecidableAnd

end FluxesFive

/-!

## Fluxes of the 10d matter representation

-/

/-- The fluxes `(M, N)` of the 10d matter curves of a theory. -/
abbrev FluxesTen : Type := Multiset (ℤ × ℤ)

namespace FluxesTen

/-- The proposition on `FluxesTen` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesTen) : Prop := (0, 0) ∉ F

/-!

## The SM representation `Q = (3,2)_{1/6}`

-/

/-- The multiset of chiral indices of the representation `Q = (3,2)_{1/6}`
  arrising from the matter 10d representations, corresponding to `M`. -/
def chiralIndicesOfQ (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.1)

/-- The total number of chiral `Q` representations arrising from the matter 10d
  representations. -/
def numChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => 0 ≤ x)).sum

/-- The total number of anti-chiral `Q` representations arrising from the matter 10d
  representations. -/
def numAntiChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => x < 0)).sum

/-!

## The SM representation `U = (bar 3,1)_{-2/3}`

-/

/-- The multiset of chiral indices of the representation `U = (bar 3,1)_{-2/3}`
  arrising from the matter 10d representations, corresponding to `M - N` -/
def chiralIndicesOfU (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.1 - f.2)

/-- The total number of chiral `U` representations arrising from the matter 10d
  representations. -/
def numChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => 0 ≤ x)).sum

/-- The total number of anti-chiral `U` representations arrising from the matter 10d
  representations. -/
def numAntiChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => x < 0)).sum

/-!

## The SM representation `E = (1,1)_{1}`

-/

/-- The multiset of chiral indices of the representation `E = (1,1)_{1}`
  arrising from the matter 10d representations, corresponding to `M + N` -/
def chiralIndicesOfE (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.1 + f.2)

/-- The total number of chiral `E` representations arrising from the matter 10d
  representations. -/
def numChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => 0 ≤ x)).sum

/-- The total number of anti-chiral `E` representations arrising from the matter 10d
  representations. -/
def numAntiChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => x < 0)).sum

/-!

## The condition for no exotics

-/

/-- The condition that the 10d-matter represenations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `Q` representations and no anti-chiral `Q` representations.
- There are 3 chiral `U` representations and no anti-chiral `U` representations.
- There are 3 chiral `E` representations and no anti-chiral `E` representations.
-/
def NoExotics (F : FluxesTen) : Prop :=
  F.numChiralQ = 3 ∧ F.numAntiChiralQ = 0 ∧
  F.numChiralU = 3 ∧ F.numAntiChiralU = 0 ∧
  F.numChiralE = 3 ∧ F.numAntiChiralE = 0

instance (F : FluxesTen) : Decidable (F.NoExotics) :=
  instDecidableAnd

end FluxesTen

end SU5

end FTheory
