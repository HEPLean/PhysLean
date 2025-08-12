/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.FromParts
import PhysLean.Particles.SuperSymmetry.SU5.Charges.MinimallyAllowsTerm.FinsetTerms
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

/-!

## Anomaly cancellation conditions

-/

/-- The pair of anomaly cancellation coefficents associated with the `Hd` particle. -/
def HdAnomalyCoefficent (qHd : Option ℤ) : ℤ × ℤ :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)

/-- The pair of anomaly cancellation coefficents associated with the `Hu` particle. -/
def HuAnomalyCoefficent (qHu : Option ℤ) : ℤ × ℤ :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)

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

instance : Decidable (AnomalyCancellation qHd qHu F T) :=
  inferInstanceAs (Decidable ((HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu
    + F.anomalyCoefficent + T.anomalyCoefficent) = (0, 0)))

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

/-!

## Anomaly cancellation on charges tree

-/

namespace Charges
namespace Tree
open PhysLean FourTree

/-- Given charges `qHd` and `qHu` filters a twig of `Q5` and `Q10` charges
  by the anomaly cancellation condition. -/
def Twig.filterAnomalyCancellation (I : CodimensionOneConfig) (qHd qHu : Option ℤ) :
    Twig (Finset ℤ) (Finset ℤ) → Twig (Finset ℤ) (Finset ℤ) := fun (.twig Q5 leafsList) =>
  -- Anomaly cancellation on ust qHd, qHu and Q5 by mod 3.
  let l := ((FiveQuanta.ofCharges I Q5.val).filter fun F =>
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2) % 3 = 0).map fun F =>
    (HdAnomalyCoefficent qHd) + (HuAnomalyCoefficent qHu)
    + (F.anomalyCoefficent)
  if l = ∅ then
    .twig Q5 {}
  else
    .twig Q5 <| leafsList.filter fun (.leaf Q10) =>
      let l10 := (TenQuanta.ofCharges I Q10.val).countP fun T =>
        - T.anomalyCoefficent ∈ l
      l10 ≠ 0

/-- Given charges `qHd` filters a branch of `qHu`, `Q5` and `Q10` charges
  by the anomaly cancellation condition. -/
def Branch.filterAnomalyCancellation (I : CodimensionOneConfig) (qHd : Option ℤ) :
    Branch (Option ℤ) (Finset ℤ) (Finset ℤ) →
    Branch (Option ℤ) (Finset ℤ) (Finset ℤ) := fun (.branch qHu twigsList) =>
  .branch qHu <| twigsList.map fun t => Twig.filterAnomalyCancellation I qHd qHu t

/-- Filters a trunk of `qHd`, `qHu`, `Q5` and `Q10` charges
  by the anomaly cancellation condition. -/
def Trunk.filterAnomalyCancellation (I : CodimensionOneConfig) :
    Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) →
    Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
    fun (.trunk qHd branchList) =>
  .trunk qHd <| branchList.map fun b => Branch.filterAnomalyCancellation I qHd b

/-- Filters a tree of `qHd`, `qHu`, `Q5` and `Q10` charges
  by the anomaly cancellation condition. -/
def filterAnomalyCancellation (I : CodimensionOneConfig) :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) →
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) := fun (.root tunksList) =>
  root <| tunksList.map fun t => Trunk.filterAnomalyCancellation I t

lemma mem_filterAnomalyCancellation_iff {I : CodimensionOneConfig}
    {T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)} {x : Charges} :
    x ∈ filterAnomalyCancellation I T ↔ x ∈ T ∧
    ∃ F : FiveQuanta, ∃ T : TenQuanta,
      F ∈ FiveQuanta.ofCharges I x.2.2.1.val ∧ T ∈ TenQuanta.ofCharges I x.2.2.2.val ∧
      AnomalyCancellation x.1 x.2.1 F T := by
  constructor
  · intro h
    rw [mem_iff_mem_toMultiset] at h
    simp [toMultiset] at h
    obtain ⟨trunkA, htrunkA, branchA, hbranchA, twigA, htwigA, leafA, hleafA, heq⟩ := h
    simp [filterAnomalyCancellation, root] at htrunkA
    obtain ⟨trunkT, trunkT_mem, trunkA_eq⟩ := htrunkA
    subst trunkA_eq
    simp [Trunk.filterAnomalyCancellation] at hbranchA
    simp [Trunk.filterAnomalyCancellation] at heq
    obtain ⟨branchT, branchT_mem, branchA_eq⟩ := hbranchA
    subst branchA_eq
    simp [Branch.filterAnomalyCancellation] at htwigA
    simp [Branch.filterAnomalyCancellation] at heq
    obtain ⟨twigT, twigT_mem, twigA_eq⟩ := htwigA
    subst twigA_eq
    simp [Twig.filterAnomalyCancellation] at hleafA heq
    split_ifs at * with hMod3
    · simp at hleafA
    simp at hleafA
    obtain ⟨leafA_mem, leaf_count_neq_zero⟩ := hleafA
    rw [Multiset.countP_eq_zero] at leaf_count_neq_zero
    simp at leaf_count_neq_zero
    obtain ⟨T10, T10_mem, F, F_mem, hAccMod, hacc⟩ := leaf_count_neq_zero
    constructor
    · exact mem_of_parts trunkT branchT twigT leafA trunkT_mem branchT_mem twigT_mem
        leafA_mem heq.symm
    · use F, T10
      subst heq
      simp_all
      rw [AnomalyCancellation, hacc]
      simp
      rfl
  · intro ⟨h, h2⟩
    rw [mem_iff_mem_toMultiset] at h
    simp [toMultiset] at h
    obtain ⟨trunkT, htrunkT, branchT, hbranchT, twigT, htwigT, leafT, hleafT, heq⟩ := h
    refine mem_of_parts (Trunk.filterAnomalyCancellation I trunkT)
      (Branch.filterAnomalyCancellation I trunkT.1 branchT)
      (Twig.filterAnomalyCancellation I trunkT.1 branchT.1 twigT) leafT ?_ ?_ ?_ ?_ ?_
    · simp [filterAnomalyCancellation, root]
      use trunkT
    · simp [Trunk.filterAnomalyCancellation]
      use branchT
    · simp [Branch.filterAnomalyCancellation]
      use twigT
    · simp [Twig.filterAnomalyCancellation]
      obtain ⟨F, T10, F_mem, T10_mem, hacc⟩ := h2
      subst heq
      simp_all
      rw [if_neg]
      · simp_all
        rw [Multiset.countP_eq_zero]
        simp only [Multiset.mem_map, Multiset.mem_filter, not_exists, not_and, and_imp, not_forall,
          Classical.not_imp, Decidable.not_not]
        use T10
        simp_all
        use F
        simp_all
        constructor
        · exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc
        · exact Eq.symm (neg_eq_of_add_eq_zero_left hacc)
      · rw [Multiset.filter_eq_nil]
        simp only [not_forall, Classical.not_imp, Decidable.not_not]
        use F
        simp_all
        exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc
    · subst x
      simp [Trunk.filterAnomalyCancellation, Branch.filterAnomalyCancellation,
        Twig.filterAnomalyCancellation, filterAnomalyCancellation]
      rw [if_neg]
      rw [Multiset.filter_eq_nil]
      simp only [not_forall, Classical.not_imp, Decidable.not_not]
      obtain ⟨F, T10, F_mem, T10_mem, hacc⟩ := h2
      use F
      simp_all
      exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc

end Tree
end Charges
end SU5U1

end FTheory
