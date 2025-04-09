/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.ProperTime
/-!
# Twin Paradox

-/

noncomputable section

namespace SpecialRelativity

open Matrix
open Real
open Lorentz
open Vector

/-- The twin paradox assuming instantaneous acceleration. -/
structure InstantaneousTwinParadox where
  /-- The starting point of both twins. -/
  startPoint : SpaceTime 3
  /-- The end point of both twins. -/
  endPoint : SpaceTime 3
  /-- The point twin B travels to between the start point and the end point. -/
  twinBMid : SpaceTime 3
  endPoint_causallyFollows_startPoint : causallyFollows startPoint endPoint
  twinBMid_causallyFollows_startPoint : causallyFollows startPoint twinBMid
  endPoint_causallyFollows_twinBMid : causallyFollows twinBMid endPoint

namespace InstantaneousTwinParadox
variable (T: InstantaneousTwinParadox)
open SpaceTime

/-- The proper time experienced by twin A travelling at constant speed
  from `T.startPoint` to `T.endPoint`. -/
def properTimeTwinA : ℝ := SpaceTime.properTime T.startPoint T.endPoint

/-- The proper time experienced by twin B travelling at constant speed
  from `T.startPoint` to `T.twinBMid`, and then from `T.twinBMid`
  to `T.endPoint`. -/
def properTimeTwinB : ℝ := SpaceTime.properTime T.startPoint T.twinBMid +
  SpaceTime.properTime T.twinBMid T.endPoint

/-- The proper time of twin A minus the proper time of twin B. -/
def ageGap : ℝ := T.properTimeTwinA - T.properTimeTwinB

TODO "6V2UQ" "Find the conditions for which the age gap for the twin paradox is zero."

/-!

## Example 1

-/

/-- The twin paradox in which:
- Twin A starts at `0` and travels at constant
  speed to `[15, 0, 0, 0]`.
- Twin B starts at `0` and travels at constant speed to
  `[7.5, 6, 0, 0]` and then at (different) constant speed to `[15, 0, 0, 0]`. -/
def example1 : InstantaneousTwinParadox where
  startPoint := 0
  endPoint := toCoord.symm (fun
    | Sum.inl 0 => 15
    | Sum.inr i => 0)
  twinBMid := toCoord.symm (fun
    | Sum.inl 0 => 7.5
    | Sum.inr 0 => 6
    | Sum.inr i => 0)
  endPoint_causallyFollows_startPoint := by
    simp [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_setOf_eq,
      LinearEquiv.apply_symm_apply, Nat.ofNat_pos, and_true]
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [innerProduct_toCoord]
    simp
  twinBMid_causallyFollows_startPoint := by
    simp only [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_setOf_eq,
      LinearEquiv.apply_symm_apply]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [innerProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num
  endPoint_causallyFollows_twinBMid := by
    simp [causallyFollows]
    left
    simp [interiorFutureLightCone]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [innerProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num

@[simp]
lemma example1_properTimeTwinA : example1.properTimeTwinA = 15 := by
  simp [properTimeTwinA, example1, properTime, innerProduct_toCoord]

@[simp]
lemma example1_properTimeTwinB : example1.properTimeTwinB = 9 := by
  simp only [properTimeTwinB, properTime, example1, sub_zero, innerProduct_toCoord, Fin.isValue,
    LinearEquiv.apply_symm_apply, Fin.sum_univ_three, mul_zero, add_zero, map_sub, Pi.sub_apply,
    zero_sub, mul_neg, neg_mul, neg_neg]
  rw [show √(7.5 * 7.5 - 6 * 6) = √20.25 by norm_num]
  rw [show √((15 - 7.5) * (15 - 7.5) - 6 * 6) = √20.25 by norm_num]
  rw [show √20.25 = 4.5 from sqrt_eq_cases.mpr (by norm_num)]
  norm_num

lemma example1_ageGap : example1.ageGap = 6 := by
  simp [ageGap]
  norm_num

end InstantaneousTwinParadox

end SpecialRelativity

end
