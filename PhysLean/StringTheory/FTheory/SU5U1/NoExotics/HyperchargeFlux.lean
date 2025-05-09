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

/-!

## Hypercharge fluxes as lists

-/


/--
For `N` a multiset of `HyperchargeFlux` for 5-bar matter
valid under the no-exotics constraints, `hyperchargeFluxLists N` is
an explicit form of `N.lists.dedup`.

This is defined since `N.lists.dedup` does not work well with decide.
This definition was produced with the help of e.g.
`#eval ([-1, -2, 1, 1, 1] : List ℤ).permutations.dedup`
-/
def hyperchargeFluxLists (N : Multiset ℤ) : Multiset (List ℤ) :=
  if N = {-1, -1, -1, 1, 2} then
     {[1, -1, -1, -1, 2], [-1, 1, -1, -1, 2], [-1, -1, 1, -1, 2], [-1, -1, -1, 1, 2],
    [1, -1, -1, 2, -1], [-1, 1, -1, 2, -1], [-1, -1, 1, 2, -1], [-1, -1, -1, 2, 1],
    [1, -1, 2, -1, -1], [-1, 1, 2, -1, -1], [-1, -1, 2, 1, -1], [-1, -1, 2, -1, 1],
    [1, 2, -1, -1, -1], [-1, 2, 1, -1, -1], [-1, 2, -1, 1, -1], [-1, 2, -1, -1, 1],
    [2, 1, -1, -1, -1], [2, -1, 1, -1, -1], [2, -1, -1, 1, -1], [2,-1, -1, -1, 1]}
  else if  N = {-1, -1, 0, 1, 1} then
    {[1, -1, -1, 0, 1], [-1, 1, -1, 0, 1], [-1, -1, 1, 0, 1], [-1, -1, 0, 1, 1], [1, -1, 0, -1, 1],
    [-1, 1, 0, -1, 1], [-1, 0, 1, -1, 1], [-1, 0, -1, 1, 1], [1, 0, -1, -1, 1], [0, 1, -1, -1, 1],
    [0, -1, 1, -1, 1], [0, -1, -1, 1, 1], [-1, 1, 1, 0, -1], [1, 1, -1, 0, -1], [1, -1, 1, 0, -1],
    [1, 1, 0, -1, -1], [1, -1, 0, 1, -1], [-1, 1, 0, 1, -1],  [-1, 0, 1, 1, -1], [1, 0, -1, 1, -1],
    [0, -1, 1, 1, -1], [1, 0, 1, -1, -1], [0, 1, 1, -1, -1], [0, 1, -1, 1, -1], [1, 1, -1, -1, 0],
    [1, -1, -1, 1, 0], [-1, -1, 1, 1, 0], [1, -1, 1, -1, 0], [-1, 1, 1, -1, 0], [-1, 1, -1, 1, 0]}
  else if N = {-1, -2, 1, 1, 1} then
    {[1, 1, 1, -2, -1], [-2, 1, 1, 1, -1], [1, 1, -2, 1, -1], [1, -2, 1, 1, -1], [-1, 1, 1, 1, -2],
    [1, -1, 1, 1, -2], [1, 1, 1, -1, -2], [1, 1, -1, 1, -2], [-1, 1, 1, -2, 1], [1, 1, -1, -2, 1],
    [1, -1, 1, -2, 1], [1, 1, -2, -1, 1], [1, -1, -2, 1, 1], [-1, 1, -2, 1, 1], [-1, -2, 1, 1, 1],
    [1, -2, -1, 1, 1], [-2, -1, 1, 1, 1], [1, -2, 1, -1, 1], [-2, 1, 1, -1, 1], [-2, 1, -1, 1, 1]}
  else if N = {-3, 1, 1, 1} then {[1, 1, -3, 1], [-3, 1, 1, 1], [1, -3, 1, 1], [1, 1, 1, -3]}
  else if N = {-2, -1, 1, 2} then
    {[-2, -1, 1, 2], [-1, -2, 1, 2], [1, -1, -2, 2], [-1, 1, -2, 2], [1, -2, -1, 2], [-2, 1, -1, 2],
    [2, 1, -1, -2], [1, 2, -1, -2], [1, -1, 2, -2], [2, -1, 1, -2], [-1, 2, 1, -2], [-1, 1, 2, -2],
    [2, -2, -1, 1], [-2, 2, -1, 1], [-2, -1, 2, 1], [2, -1, -2, 1], [-1, 2, -2, 1], [-1, -2, 2, 1],
    [2, -2, 1, -1], [-2, 2, 1, -1], [-2, 1, 2, -1], [2, 1, -2, -1], [1, 2, -2, -1], [1, -2, 2, -1]}
  else if N = {-2, 0, 1, 1} then
    {[1, 1, 0, -2], [1, 0, 1, -2], [0, 1, 1, -2], [1, -2, 0, 1], [-2, 1, 0, 1], [-2, 0, 1, 1],
    [1, 0, -2, 1], [0, 1, -2, 1], [0, -2, 1, 1], [-2, 1, 1, 0], [1, 1, -2, 0], [1, -2, 1, 0]}
  else if N = {-1, -1, -1, 3} then
    {[-1, -1, -1, 3], [3, -1, -1, -1], [-1, 3, -1, -1], [-1, -1, 3, -1]}
  else if N = {-1, -1, 0, 2} then {[-1, -1, 0, 2], [0, -1, -1, 2], [-1, 0, -1, 2], [2, -1, -1, 0],
    [-1, 2, -1, 0], [-1, -1, 2, 0], [2, -1, 0, -1],
    [-1, 2, 0, -1], [-1, 0, 2, -1], [2, 0, -1, -1], [0, 2, -1, -1], [0, -1, 2, -1]}
  else if N = {-1, -1, 1, 1} then {[1, -1, -1, 1], [-1, 1, -1, 1], [-1, -1, 1, 1], [-1, 1, 1, -1],
    [1, 1, -1, -1], [1, -1, 1, -1]}
  else if N = {0, 0, -1, 1}  then  {[0, 0, -1, 1], [-1, 0, 0, 1], [0, -1, 0, 1], [1, 0, 0, -1],
    [0, 1, 0, -1], [0, 0, 1, -1], [1, 0, -1, 0], [0, 1, -1, 0], [0, -1, 1, 0], [1, -1, 0, 0],
    [-1, 1, 0, 0], [-1, 0, 1, 0]}
  else if N = {-3, 1, 2} then {[-3, 1, 2], [1, -3, 2], [2, 1, -3], [1, 2, -3],
    [2, -3, 1], [-3, 2, 1]}
  else if N = {-2, -1, 3} then {[-2, -1, 3], [-1, -2, 3], [3, -1, -2], [-1, 3, -2], [3, -2, -1],
    [-2, 3, -1]}
  else if N = {-2, 0, 2} then {[-2, 0, 2], [0, -2, 2], [2, 0, -2], [0, 2, -2], [2, -2, 0],
    [-2, 2, 0]}
  else if N = {-2, 1, 1} then {[1, 1, -2], [1, -2, 1], [-2, 1, 1]}
  else if N = {-1, -1, 2} then {[-1, -1, 2], [2, -1, -1], [-1, 2, -1]}
  else if N = {-1, 0, 1} then {[-1, 0, 1], [0, -1, 1], [1, 0, -1], [0, 1, -1], [1, -1, 0],
    [-1, 1, 0]}
  else if N = {0, 0, 0} then {[0 ,0, 0]}
  else if N = {-3, 3} then {[-3, 3], [3, -3]}
  else if N = {-2, 2} then {[-2, 2], [2, -2]}
  else if N = {-1, 1} then {[-1, 1], [1, -1]}
  else if N = {0, 0} then {[0, 0]}
  else if N = {0} then {[0]}
  else ∅

lemma hyperchargeFlux_lists_eq_hyperchargeFluxLists (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles) (h3L : 𝓜.ThreeLeptonDoublets) :
    (𝓜.quantaBarFiveMatter.map QuantaBarFive.N).lists.dedup =
    hyperchargeFluxLists (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) := by
  have h2 := 𝓜.quantaBarFiveMatter_N_mem he h3 h3L
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.N) = N at *
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.nodup_dedup N.lists
  · revert N
    decide
  intro l
  rw [Multiset.mem_dedup, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe]
  constructor
  · intro hNl
    have hlen : l.length = N.card := by
      rw [← Multiset.coe_card, ← hNl]
    match l with
    | [] =>
      rw [List.length_nil] at hlen
      subst hNl
      apply False.elim
      revert h2
      decide
    | q1 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add] at hlen
      revert hNl; revert q1;  revert N
      decide
    | q1 :: q2 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2;
      revert N
      decide
    | q1 :: q2 :: q3 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      have hq4 : q4 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: q5 :: []  =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      have hq4 : q4 ∈ N.dedup := by simp [hNl]
      have hq5 : q5 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3; revert q4; revert q5
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: l =>
      simp at hlen
      have hn : 6 ≤ N.card := by omega
      clear hlen hNl
      apply False.elim
      revert N
      decide
  · revert l
    revert N
    decide

/--
For `N` a multiset of `HyperchargeFlux` for 10d matter
valid under the no-exotics constraints, `hyperchargeFluxLists N` is
an explicit form of `N.lists.dedup`.

This is defined since `N.lists.dedup` does not work well with decide.
This definition was produced with the help of e.g.
`#eval ([-1, -2, 1, 1, 1] : List ℤ).permutations.dedup`
-/
def hyperchargeFluxListsTen (N : Multiset ℤ) : Multiset (List ℤ) :=
  if N = {0, 0, 0} then {[0, 0, 0]}
  else if  N = {1, -1, 0} then {[-1, 1, 0], [1, -1, 0], [0, 1, -1], [1, 0, -1],
    [0, -1, 1], [-1, 0, 1]}
  else if N = {0, 0} then {[0, 0]}
  else if N = {-1, 1} then {[-1, 1], [1, -1]}
  else if N = {0} then {[0]}
  else ∅

lemma hyperchargeFlux_lists_eq_hyperchargeFluxListsTen (he : 𝓜.NoExotics)
    (h3 : 𝓜.ThreeChiralFamiles)  :
    (𝓜.quantaTen.map QuantaBarFive.N).lists.dedup =
    hyperchargeFluxListsTen (𝓜.quantaTen.map QuantaBarFive.N) := by
  have h2 := 𝓜.quantaTen_N_mem he h3
  generalize (𝓜.quantaTen.map QuantaTen.N) = N at *
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.nodup_dedup N.lists
  · revert N
    decide
  intro l
  rw [Multiset.mem_dedup, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe]
  constructor
  · intro hNl
    have hlen : l.length = N.card := by
      rw [← Multiset.coe_card, ← hNl]
    match l with
    | [] =>
      rw [List.length_nil] at hlen
      subst hNl
      apply False.elim
      revert h2
      decide
    | q1 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add] at hlen
      revert hNl; revert q1;  revert N
      decide
    | q1 :: q2 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2;
      revert N
      decide
    | q1 :: q2 :: q3 :: [] =>
      have hq1 : q1 ∈ N.dedup := by simp [hNl]
      have hq2 : q2 ∈ N.dedup := by simp [hNl]
      have hq3 : q3 ∈ N.dedup := by simp [hNl]
      simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hlen
      revert hNl
      revert q1; revert q2; revert q3;
      revert N
      decide
    | q1 :: q2 :: q3 :: q4 :: l =>
      simp at hlen
      have hn : 4 ≤ N.card := by omega
      clear hlen hNl
      apply False.elim
      revert N
      decide
  · revert l
    revert N
    decide

end MatterContent

end SU5U1

end FTheory
