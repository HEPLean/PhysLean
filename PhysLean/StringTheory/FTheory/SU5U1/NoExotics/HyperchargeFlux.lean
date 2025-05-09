/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.Fluxes
/-!

# Hypercharge flux and no exotics

The condition on the matter content for there to be no exotics in the spectrum
leads to constraints on the allowed  `HyperchargeFlux` of the matter content.

This file contains these constraints for the 5-bar and
10d matter representations.

Note: the module depends on `NoExotics.Fluxes`.

## Important results

-/
namespace FTheory

namespace SU5U1

namespace MatterContent

variable {I : CodimensionOneConfig} {𝓜 : MatterContent I}


/-- The condition of no exotics in the matter spectrum constrains the allowed
  values of the `HyperChargeFlux` carried by the 5bar matter representations to be one
  of the following 22 different Multisets:

- `{-1, -1, -1, 1, 2}`, `{-1, -1, 0, 1, 1}`, `{-1, -2, 1, 1, 1}`.
- `{-3, 1, 1, 1}`, `{-2, -1, 1, 2}`, `{-2, 0, 1, 1}`, `{-1, -1, -1, 3}`,
  `{-1, -1, 0, 2}`, `{-1, -1, 1, 1}`, `{0, 0, -1, 1}`.
- `{-3, 1, 2}`, `{-2, -1, 3}`, `{-2, 0, 2}`, `{-2, 1, 1}`,
  `{-1, -1, 2}`, `{-1, 0, 1}`, `{0, 0, 0}`.
- `{-3, 3}`, `{-2, 2}`, `{-1, 1}`, `{0, 0}`.
- `{0}`.
-/
lemma quantaBarFiveMatter_N_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (h3L : 𝓜.ThreeLeptonDoublets) :
    𝓜.quantaBarFiveMatter.map QuantaBarFive.N ∈ ({
    -- card 5 (3 cases)
    {-1, -1, -1, 1, 2}, {-1, -1, 0, 1, 1}, {-1, -2, 1, 1, 1},
    -- card 4 (7 cases)
    {-3, 1, 1, 1}, {-2, -1, 1, 2},
    {-2, 0, 1, 1}, {-1, -1, -1, 3},
    {-1, -1, 0, 2}, {-1, -1, 1, 1}, {0, 0, -1, 1},
    -- card 3 (7 cases)
    -- Corresponding to 6 + 6 + 6 + 3 + 3 + 6 + 1 = 31 ACC conditions.
    {-3, 1, 2}, {-2, -1, 3}, {-2, 0, 2}, {-2, 1, 1},
    {-1, -1, 2}, {-1, 0, 1}, {0, 0, 0},
    -- card 2 (4 cases)
    -- Corresponding to 2 + 2 + 2 + 1 = 7 ACC conditions.
    {-3, 3}, {-2, 2}, {-1, 1}, {0, 0},
    -- card 1 (1 case)
    -- Corresponding to 1 ACC condition.
    {0}} : Finset (Multiset ℤ)) := by
  have hr := quantaBarFiveMatter_MN_mem he h3 h3L
  have hn : 𝓜.quantaBarFiveMatter.map QuantaBarFive.N =
    (Multiset.map QuantaBarFive.MN 𝓜.quantaBarFiveMatter).map Prod.snd := by
    simp
  rw [hn]
  generalize (Multiset.map QuantaBarFive.MN 𝓜.quantaBarFiveMatter) = S at *
  clear hn
  revert S
  decide


/-- The condition of no exotics in the matter spectrum constrains the allowed
  values of the `HyperChargeFlux` carried by the 10d representations to be one
  of the following Multisets:

 `{0, 0, 0}`, `{1, -1, 0}`, `{0}`, `{-1, 1}`, `{0}`.
-/
lemma quantaTen_N_mem (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles) :
    𝓜.quantaTen.map QuantaTen.N ∈ ({
    {0, 0, 0}, {1, -1, 0}, {0, 0}, {-1, 1}, {0}} : Finset (Multiset ℤ)) := by
  have hr := quantaTen_MN_mem he h3
  have hn : 𝓜.quantaTen.map QuantaTen.N =
    (Multiset.map QuantaTen.MN 𝓜.quantaTen).map Prod.snd := by
    simp
  rw [hn]
  generalize (Multiset.map QuantaTen.MN 𝓜.quantaTen) = S at *
  clear hn
  revert S
  decide

end MatterContent

end SU5U1

end FTheory
