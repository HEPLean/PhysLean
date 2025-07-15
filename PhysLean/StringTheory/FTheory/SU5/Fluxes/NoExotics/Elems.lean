/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Fluxes.Basic
/-!

# Elements of `FluxesFive` and `FluxesTen` with no chiral exotics

There are only a finite number of elements of `FluxesFive` and `FluxesTen` which
do not lead to chiral exotics in the spectrum.

These elements are given in the definitions `elemsNoExotics` in the respective namespaces.

For `FluxesFive` there are `31` such elements, and for `FluxesTen` there are `6` such elements.

-/
namespace FTheory

namespace SU5

namespace FluxesFive

/-- The elements of `FluxesFive` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesFive := {
    {(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)},
    {(1, -1), (1, -1), (1, -1), (0, 1), (0, 2)},
    {(1, -1), (1, -1), (1, 0), (0, 1), (0, 1)},
    {(1, 1), (1, -1), (1, -1), (0, 1)},
    {(1, 0), (1, 0), (1, -1), (0, 1)},
    {(1, -1), (1, 0), (1, -1), (0, 2)},
    {(1, -1), (1, -1), (1, -1), (0, 3)},
    {(1, -1), (1, -1), (1, 2)},
    {(1, -1), (1, 0), (1, 1)}, {(1, 0), (1, 0), (1, 0)},
    {(1, -1), (2, -2), (0, 1), (0, 1), (0, 1)},
    {(1, -1), (2, -2), (0, 1), (0, 2)},
    {(1, -1), (2, -1), (0, 1), (0, 1)},
    {(1, 0), (2, -2), (0, 1), (0, 1)},
    {(1, 1), (2, -2), (0, 1)}, {(1, 0), (2, -1), (0, 1)},
    {(1, 0), (2, -2), (0, 2)}, {(1, -1), (2, 0), (0, 1)},
    {(1, -1), (2, -1), (0, 2)}, {(1, -1), (2, -2), (0, 3)},
    {(1, -1), (2, 1)}, {(1, 0), (2, 0)}, {(1, 1), (2, -1)},
    {(1, 2), (2, -2)},
    {(3, -3), (0, 1), (0, 1), (0, 1)},
    {(3, -3), (0, 1), (0, 2)}, {(3, -2), (0, 1), (0, 1)},
    {(3, -3), (0, 3)}, {(3, -2), (0, 2)}, {(3, -1), (0, 1)},
    {(3, 0)}}

lemma elemsNoExotics_card : elemsNoExotics.card = 31 := by
  decide

lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide

lemma noExotics_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide

lemma toFinset_card_le_four_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 4 := by
  revert F h
  decide

lemma card_le_six_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.card ≤ 6 := by
  revert F h
  decide

lemma sum_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.sum = (3, 0) := by
  revert F h
  decide

lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide

end FluxesFive

namespace FluxesTen

/-- The elements of `FluxesTen` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesTen := {{(1, 0), (1, 0), (1, 0)},
  {(1, 1), (1, -1), (1, 0)}, {(1, 0), (2, 0)},
  {(1, -1), (2, 1)}, {(1, 1), (2, -1)},
  {(3, 0)}}

lemma elemsNoExotics_card : elemsNoExotics.card = 6 := by
  decide

lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide

lemma noExotics_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide

lemma toFinset_card_le_three_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 3 := by
  revert F h
  decide

lemma sum_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.sum = (3, 0) := by
  revert F h
  decide

lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide

end FluxesTen

end SU5

end FTheory
