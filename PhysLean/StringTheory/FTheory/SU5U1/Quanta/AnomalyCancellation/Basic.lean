/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.FromParts
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimallyAllowsTerm.FinsetTerms
import PhysLean.Particles.SuperSymmetry.SU5.Charges.ZMod
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Map
import Mathlib.Data.ZMod.Basic
/-!

# Anomaly cancellation

There are two anomaly cancellation conditions in the SU(5)×U(1) model which involve the
`U(1)` charges. These are

- `∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar represenations and the second
  is over all 10d representations.
- `∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar represenations and the
  second is over all 10d representations.

According to arXiv:1401.5084 it is unclear whether this second condition should necessarily be
imposed.

-/

namespace FTheory

namespace SU5U1
open SuperSymmetry.SU5
variable {I : CodimensionOneConfig}

variable {𝓩 : Type} [AddCommGroup 𝓩]

/--
  The anomaly coefficent of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084.
-/
def FiveQuanta.anomalyCoefficent (F : FiveQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, (F.map fun x => x.1 * x.1 * x.2.2).sum)

def FiveQuanta.anomalyCoefficentGen (F : FiveQuanta 𝓩)
  (𝓩' : Type) [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') : 𝓩 × 𝓩' :=
  (F.map fun x => (x.2.2 • x.1, x.2.2 • f x.1)).sum

lemma FiveQuanta.anomalyCoefficent_eq_anomalyCoefficentGen (F : FiveQuanta ℤ) :
    F.anomalyCoefficent = F.anomalyCoefficentGen ℤ (fun x => x * x) := by
  simp [FiveQuanta.anomalyCoefficent, FiveQuanta.anomalyCoefficentGen]
  ext
  · simp [Multiset.fst_sum]
    congr
    funext x
    ring
  · simp [Multiset.snd_sum]
    congr
    funext x
    ring
/--
  The anomaly coefficent of a `TenQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
    see equation (23) of arXiv:1401.5084.
-/
def TenQuanta.anomalyCoefficent (F : TenQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, 3 * (F.map fun x => x.1 * x.1 * x.2.2).sum)

def TenQuanta.anomalyCoefficentGen (F : TenQuanta 𝓩)
  (𝓩' : Type) [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') : 𝓩 × 𝓩' :=
  (F.map fun x => (x.2.2 • x.1, 3 • x.2.2 • f x.1)).sum

lemma TenQuanta.anomalyCoefficent_eq_anomalyCoefficentGen (F : TenQuanta ℤ) :
    F.anomalyCoefficent = F.anomalyCoefficentGen ℤ (fun x => x * x) := by
  simp [TenQuanta.anomalyCoefficent, TenQuanta.anomalyCoefficentGen]
  ext
  · simp [Multiset.fst_sum]
    congr
    funext x
    ring
  · simp [Multiset.snd_sum]
    rw [Multiset.sum_map_mul_left]
    congr
    funext x
    ring

/-!

## Anomaly cancellation conditions

-/

/-- The pair of anomaly cancellation coefficents associated with the `Hd` particle. -/
def HdAnomalyCoefficent (qHd : Option ℤ) : ℤ × ℤ :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)

def HdAnomalyCoefficentGen (𝓩' : Type) [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') (qHd : Option 𝓩) :
    𝓩 × 𝓩' :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, f qHd)

lemma HdAnomalyCoefficent_eq_HdAnomalyCoefficentGen (qHd : Option ℤ) :
    HdAnomalyCoefficent qHd = HdAnomalyCoefficentGen ℤ (fun x => x * x) qHd := by
  cases qHd
  · rfl
  · simp [HdAnomalyCoefficent, HdAnomalyCoefficentGen]
    ring

/-- The pair of anomaly cancellation coefficents associated with the `Hu` particle. -/
def HuAnomalyCoefficent (qHu : Option ℤ) : ℤ × ℤ :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)

def HuAnomalyCoefficentGen (𝓩' : Type) [AddCommGroup 𝓩'] (f : 𝓩 → 𝓩') (qHu : Option 𝓩) :
    𝓩 × 𝓩' :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -f qHu)

lemma HuAnomalyCoefficent_eq_HuAnomalyCoefficentGen (qHu : Option ℤ) :
    HuAnomalyCoefficent qHu = HuAnomalyCoefficentGen ℤ (fun x => x * x) qHu := by
  cases qHu
  · rfl
  · simp [HuAnomalyCoefficent, HuAnomalyCoefficentGen]
    ring

/-- The anomaly cancellation conditions on quanta making up the fields present in
  the theory. This corresponds to the conditions that:

- `∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar represenations and the second
  is over all 10d representations.
- `∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar represenations and the
  second is over all 10d representations.
-/
def AnomalyCancellation (qHd qHu : Option ℤ) (F : FiveQuanta) (T : TenQuanta) : Prop :=
  HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu + F.anomalyCoefficent +
    T.anomalyCoefficent = (0, 0)

instance {qHd qHu F T} : Decidable (AnomalyCancellation qHd qHu F T) :=
  inferInstanceAs (Decidable ((HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu
    + F.anomalyCoefficent + T.anomalyCoefficent) = (0, 0)))

def AnomalyCancellationGen (𝓩' : Type) [AddCommGroup 𝓩']
    (f : 𝓩 → 𝓩') (qHd qHu : Option 𝓩) (F : FiveQuanta 𝓩) (T : TenQuanta 𝓩) : Prop :=
  HdAnomalyCoefficentGen 𝓩' f qHd + HuAnomalyCoefficentGen 𝓩' f qHu +
    F.anomalyCoefficentGen 𝓩' f + T.anomalyCoefficentGen 𝓩' f = (0, 0)

instance [DecidableEq 𝓩] (𝓩' : Type) [AddCommGroup 𝓩'] [DecidableEq 𝓩']
    (f : 𝓩 → 𝓩') (qHd qHu : Option 𝓩) (F : FiveQuanta 𝓩) (T : TenQuanta 𝓩) :
    Decidable (AnomalyCancellationGen 𝓩' f qHd qHu F T) :=
  inferInstanceAs <| Decidable <|
    HdAnomalyCoefficentGen 𝓩' f qHd + HuAnomalyCoefficentGen 𝓩' f qHu +
    F.anomalyCoefficentGen 𝓩' f + T.anomalyCoefficentGen 𝓩' f = (0, 0)

lemma anomalyCoefficent_snd_eq_zero_of_anomalyCancellation
    {qHd qHu : Option ℤ} {F : FiveQuanta} {T : TenQuanta} (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2) = 0 := by
  trans ((HdAnomalyCoefficent qHd)+ (HuAnomalyCoefficent qHu)
    + (F.anomalyCoefficent) + (T.anomalyCoefficent)).2
  · simp
  rw [h]

lemma five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation
    {qHd qHu : Option ℤ} {F : FiveQuanta} {T : TenQuanta} (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2) % 3 = 0 := by
  trans ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2) % 3
  swap
  · rw [anomalyCoefficent_snd_eq_zero_of_anomalyCancellation h]
    simp
  simp [TenQuanta.anomalyCoefficent]

end SU5U1

end FTheory
