/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Defs
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
import PhysLean.Meta.Linters.Sorry
/-!

# ZMod charges

In this module we investigate the possible ℤ₂ charges that one can assign
to charges associated with ℤ₂ we can assign to particles in the SU(5) model, whilst
keeping charges anomaly free.

-/

namespace SuperSymmetry

namespace SU5
namespace ChargeSpectrum

/-- The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModCharges (n : ℕ) [NeZero n] : Finset (ChargeSpectrum (ZMod n)) :=
  let S : Finset (ChargeSpectrum (ZMod n)) := ofFinset Finset.univ Finset.univ
  S.filter (fun x => IsComplete x ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

/-- This lemma corresponds to the statement that there are no choices of `ℤ₁` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_one_eq : ZModCharges 1 = ∅:= by decide

set_option maxRecDepth 2000 in
/-- This lemma corresponds to the statement that there are no choices of `ℤ₂` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_two_eq : ZModCharges 2 = ∅ := by decide

/-- This lemma corresponds to the statement that there are no choices of `ℤ₃` representations
  which give a phenomenologically viable theory. -/
@[pseudo]
lemma ZModCharges_three_eq : ZModCharges 3 = ∅ := by native_decide

@[pseudo]
lemma ZModCharges_four_eq : ZModCharges 4 = {⟨some 0, some 2, {1}, {3}⟩,
    ⟨some 0, some 2, {3}, {1}⟩, ⟨some 1, some 2, {0}, {3}⟩, ⟨some 3, some 2, {0}, {1}⟩} := by
  native_decide

/-- This lemma corresponds to the statement that there are no choices of `ℤ₅` representations
  which give a phenomenologically viable theory. -/
@[pseudo]
lemma ZModCharges_five_eq : ZModCharges 5 = ∅ := by native_decide

@[pseudo]
lemma ZModCharges_six_eq : ZModCharges 6 = {⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩, ⟨some 1, some 0, {2}, {3}⟩, ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 4, {0}, {5}⟩, ⟨some 1, some 4, {3}, {2}⟩, ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 4, {5}, {5}⟩, ⟨some 3, some 2, {5}, {4}⟩, ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {5}, {3}⟩, ⟨some 4, some 2, {1}, {1}⟩, ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩, ⟨some 5, some 2, {3}, {4}⟩, ⟨some 5, some 4, {2}, {5}⟩} := by
  native_decide

/-- The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModZModCharges (n m : ℕ) [NeZero n] [NeZero m] : Finset (ChargeSpectrum (ZMod n × ZMod m)) :=
  let S : Finset (ChargeSpectrum (ZMod n × ZMod m)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => IsComplete x ∧
  ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

/-- The additive monoid homomorphism from `ℤ` to `ZMod n` obtained by
  taking the modulo. -/
def intToZMod (n : ℕ) : ℤ →+ ZMod n where
  toFun := Int.cast
  map_zero' := Int.cast_zero
  map_add' := Int.cast_add

/-- The non-trivial additive monoid homomorphism from `ZMod 4` to `ZMod 2`. -/
def zModFourToZModTwo:
    ZMod 4 →+ ZMod 2 where
  toFun x :=
    match x with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | 3 => 1
  map_zero' := by simp
  map_add' := by
    intros x y
    fin_cases x
    all_goals fin_cases y
    all_goals decide

end ChargeSpectrum
end SU5

end SuperSymmetry
