/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.AnomalyCancellation.Basic
/-!

# Anomaly cancellation charges

-/

namespace FTheory

namespace SU5U1
open SuperSymmetry.SU5
variable {I : CodimensionOneConfig}

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-!

## Anomaly cancellation on charges

-/

namespace Charges

open SuperSymmetry.SU5.Charges


abbrev AnomalyFreeCharges [DecidableEq 𝓩] (x : Charges 𝓩) (𝓩' : Type) [DecidableEq 𝓩']  [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') : Prop :=
  if x.2.2.1 = ∅ ∨ x.2.2.2 = ∅ then False else
  if 6 < x.2.2.1.card ∨ 3 < x.2.2.2.card then False else
  let S53 : Multiset (Multiset 𝓩) := toMultisetsThree x.2.2.1
  let S5p : Multiset (Multiset 𝓩 × Multiset 𝓩) :=
    (S53.product S53).filter fun y => x.2.2.1.val ≤ y.1 + y.2
  let Fp : Multiset (FiveQuanta 𝓩) :=
    S5p.map (fun y => y.1.map (fun z => (z, 1, -1)) + y.2.map (fun z => (z, 0, 1)))
  let AccHdHu5 : Multiset (𝓩 × 𝓩') :=
    Fp.map (fun F => HdAnomalyCoefficentGen 𝓩' f x.1 + HuAnomalyCoefficentGen 𝓩' f x.2.1 +
      F.anomalyCoefficentGen 𝓩' f)
  -- the {(1, 0), (1, 0), (1, 0)} case fo Q10
  if (0, 0) ∈ AccHdHu5 then True else
  let Q10 : Finset (𝓩 × 𝓩 × 𝓩) := (x.2.2.2.product <| x.2.2.2.product x.2.2.2).filter
    fun y => x.2.2.2 ≤ {y.1, y.2.1, y.2.2}
  -- the {(1, 1), (1, -1), (1, 0)} for Q10
  let F10 : Finset (TenQuanta 𝓩) :=
    Q10.image (fun y => {(y.1, 1, 1), (y.2.1, 1 ,-1), (y.2.2, 1, 0)})
  let AccHdHu510 : Multiset (𝓩 × 𝓩') :=
    AccHdHu5.product F10.val |> .map (fun y => y.1 + y.2.anomalyCoefficentGen 𝓩' f)
  (0, 0) ∈ AccHdHu510

lemma anomalyFreeCharges_iff_exists_quanta [DecidableEq 𝓩] (x : Charges 𝓩) (𝓩' : Type)
    [DecidableEq 𝓩'] [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') :
    AnomalyFreeCharges x 𝓩' f ↔
    ∃ Q : Quanta 𝓩, AnomalyCancellationGen 𝓩' f Q.1 Q.2.1 Q.2.2.1 Q.2.2.2
    ∧ Q.toCharges = x := by
  sorry

/-!

## Testing

-/

-- {some -3, some 0, {-2, -1}, {-3, 0}}

def ZModZModACC (n : ℕ) [NeZero n]  : Finset (Charges (ZMod n × ZMod n)) :=
  let S : Finset (Charges (ZMod n × ZMod n)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => AnomalyFreeCharges x (ZMod n × ZMod n) (fun x => x * x))

example : AnomalyFreeCharges (𝓩 := ZMod 2) (some 0, some 0, {1}, {1}) (ZMod 2) (fun _ => 0) := by
  decide

def S4 := ((preimageOfFinset (Finset.univ) (Finset.univ) zModFourToZModTwo  (some 0, some 0, {1}, {1})).filter
  fun x => AnomalyFreeCharges x (ZMod 4) (fun x => x * x))

def S4' : Finset (Charges (ZMod 4)) := {(some 0, some 0, {1}, {1}),
  (some 0, some 0, {1}, {3}), (some 0, some 0, {1}, {1, 3}),
  (some 0, some 0, {3}, {1}), (some 0, some 0, {3}, {3}),
  (some 0, some 0, {3}, {1, 3}),
  (some 0, some 0, {1, 3}, {1}),
  (some 0, some 0, {1, 3}, {3}),
  (some 0, some 0, {1, 3}, {1, 3}),
  (some 0, some 2, {1}, {1, 3}),
  (some 0, some 2, {3}, {1, 3}),
  (some 0, some 2, {1, 3}, {1}),
  (some 0, some 2, {1, 3}, {3}),
  (some 0, some 2, {1, 3}, {1, 3}),
  (some 2, some 0, {1}, {1, 3}),
  (some 2, some 0, {3}, {1, 3}),
  (some 2, some 0, {1, 3}, {1}),
  (some 2, some 0, {1, 3}, {3}),
  (some 2, some 0, {1, 3}, {1, 3}),
  (some 2, some 2, {1}, {1}),
  (some 2, some 2, {1}, {3}),
  (some 2, some 2, {1}, {1, 3}),
  (some 2, some 2, {3}, {1}),
  (some 2, some 2, {3}, {3}),
  (some 2, some 2, {3}, {1, 3}),
  (some 2, some 2, {1, 3}, {1}),
  (some 2, some 2, {1, 3}, {3}),
  (some 2, some 2, {1, 3}, {1, 3})}

lemma S4_eq_S4' : S4 = S4' := by decide

def zModEightToZModFour:
    ZMod 8 →+ ZMod 4 where
  toFun x :=
    match x with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 0
    | 5 => 1
    | 6 => 2
    | 7 => 3
  map_zero' := by simp
  map_add' := by
    intros x y
    fin_cases x
    all_goals fin_cases y
    all_goals decide

def S8 := S4'.biUnion fun y =>
    ((preimageOfFinset (Finset.univ) (Finset.univ) zModEightToZModFour  y).filter
    fun x =>x.AllowsTerm .topYukawa
    ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1 ∧  AnomalyFreeCharges x (ZMod 8) (fun x => x * x) )
#eval S8.card
def S8' : Finset (Charges (ZMod 8)) := {(some 6, some 2, {1, 3}, {1}),
 (some 6, some 2, {3, 5}, {5}),
 (some 6, some 2, {1, 7}, {1}),
 (some 6, some 2, {5, 7}, {5}),
 (some 2, some 6, {1, 3}, {3}),
 (some 2, some 6, {3, 5}, {3}),
 (some 2, some 6, {1, 7}, {7}),
 (some 2, some 6, {5, 7}, {7})}


def zModSixteenToZModEight:
    ZMod 16 →+ ZMod 8 where
  toFun x := ZMod.cast x
  map_zero' := by simp
  map_add' := by
    intros x y
    fin_cases x
    all_goals fin_cases y
    all_goals decide

def S16 :=   ((preimageOfFinset (Finset.univ) (Finset.univ) zModSixteenToZModEight  (some 6, some 2, {3, 5}, {5})).filter
    fun x =>
      ¬ x.YukawaGeneratesDangerousAtLevel 2 ∧  AnomalyFreeCharges x (ZMod 16) (fun x => x * x) )

#eval S16

def S2S2 : Finset (Charges (ZMod 2 × ZMod 2)) :=
  let S : Finset (Charges (ZMod 2 × ZMod 2)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => IsComplete x
    ∧ x.AllowsTerm .topYukawa ∧
    ¬ x.IsPhenoConstrained ∧
    ¬ x.YukawaGeneratesDangerousAtLevel 1
    ∧ AnomalyFreeCharges x ((ZMod 2 × ZMod 2) × ZMod 2) (fun x => (x * x, x.1 * x.2)))

def S4S4 := ((preimageOfFinset (Finset.univ) (Finset.univ)
  (zModFourToZModTwo.prodMap zModFourToZModTwo)  (some (1, 0), some (0, 0), {(0, 1)}, {(1, 1)})).filter
  fun x => x.AllowsTerm .topYukawa ∧
  ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1 ∧
  AnomalyFreeCharges x ((ZMod 4 × ZMod 4) × ZMod 4) (fun x => (x * x, x.1 * x.2)))

-- (some (0, 1), some (0, 0), {(1, 0)}, {(1, 1)})

-- (some (0, 0), some (0, 2), {(0, 1), (0, 3)}, {(1, 1), (3, 1)})
def S8S8 :=  ((preimageOfFinset (Finset.univ) (Finset.univ)
  (zModEightToZModFour.prodMap zModEightToZModFour) (some (0, 0), some (0, 2), {(0, 1), (0, 3)}, {(1, 1), (3, 1)})).filter
  fun x => x.AllowsTerm .topYukawa ∧
  ¬ x.IsPhenoConstrained ∧
  AnomalyFreeCharges x ((ZMod 8 × ZMod 8) × ZMod 8) (fun x => (x * x, x.1 * x.2)))


def SR := S4'.biUnion fun y =>
    ((preimageOfFinset ({-3, -2, -1, 0, 1, 2, 3}) ({-3, -2, -1, 0, 1, 2, 3}) (intToZMod 4)  y).filter
    fun x => AnomalyFreeCharges x ℤ (fun x => x * x) )

def prod (x y : Charges ℤ) : Finset (Charges (ℤ × ℤ)) :=
  let x5 := x.2.2.1
  let y5 := y.2.2.1
  let prod5 := ({1, 2, 3} : Finset ℕ).biUnion fun n =>
    ((x5.product y5).powersetCard n).filter fun z =>
    z.image (fun z => z.1) = x5 ∧ z.image (fun z => z.2) = y5
  let x10 := x.2.2.2
  let y10 := y.2.2.2
  let prod10 := ({1, 2} : Finset ℕ).biUnion fun n =>
    ((x10.product y10).powersetCard n).filter fun z =>
    z.image (fun z => z.1) = x10 ∧ z.image (fun z => z.2) = y10
  let prod := prod5.product prod10
  let zHd :  Option (ℤ × ℤ) :=
    match x.1, y.1 with
    | none, none => none
    | some xHd, some yHd => some (xHd, yHd)
    | _, _ => none
  let zHu : Option (ℤ × ℤ) :=
    match x.2.1, y.2.1 with
    | none, none => none
    | some xHu, some yHu => some (xHu, yHu)
    | _, _ => none
  prod.image fun (z5, z10) => (zHd, zHu, z5, z10)

def combined : ℕ :=
  let SR' := (SR).filter fun x => ¬ x.IsPhenoConstrained
  let SP := SR'.product SR'
  (SP.biUnion fun (x, y) => prod x y).card

def St : Finset (ℤ × ℤ) :=
  let S' : Finset ℤ := {-3, -2, -1, 0, 1, 2, 3}
  S'.product S'

def intDiag : ℤ × ℤ →+ ℤ where
  toFun x := x.1 + x.2
  map_zero' := by simp
  map_add' := by
    intros x y
    simp
    ring

/-
{(some 6, some 10, {1, 3}, {9}),
 (some 6, some 10, {3, 9}, {1}),
 (some 6, some 10, {1, 11}, {9}),
 (some 6, some 10, {9, 11}, {1}),
 (some 14, some 2, {1, 3}, {9}),
 (some 14, some 2, {3, 9}, {1}),
 (some 14, some 2, {1, 11}, {9}),
 (some 14, some 2, {9, 11}, {1})}

-/
def Z2Z2 :=  ((preimageOfFinset St St ((intToZMod 16).comp intDiag)  (some 6, some 2, {3, 5}, {5})).filter
    fun x =>  AnomalyFreeCharges x ((ℤ × ℤ) × ℤ) (fun x => (x * x, x.2 * x.1)))

-- example : Z2Z2.card = 39 := by native_decide
def int4Diag : ZMod 4 × ZMod 4 →+ ZMod 4 where
  toFun x := x.1 + x.2
  map_zero' := by simp
  map_add' := by
    intros x y
    simp
    ring

end Charges
end SU5U1

end FTheory
