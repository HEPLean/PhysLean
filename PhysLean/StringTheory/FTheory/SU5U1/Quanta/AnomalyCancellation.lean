/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Quanta.FromParts
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Basic
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/--
  The anomaly coefficent of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084.
-/
def FiveQuanta.anomalyCoefficent (F : FiveQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, (F.map fun x => x.1 * x.1 * x.2.2).sum)


/--
  The anomaly coefficent of a `TenQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
    see equation (23) of arXiv:1401.5084.
-/
def TenQuanta.anomalyCoefficent (F : TenQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, 3 * (F.map fun x => x.1 * x.1 * x.2.2).sum)

/-!

## Anomaly cancellation conditions

-/

def HdAnomalyCoefficent (qHd : Option ℤ) : ℤ × ℤ :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)

def HuAnomalyCoefficent (qHu : Option ℤ) : ℤ × ℤ :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)

def AnomalyCancellation (qHd qHu : Option ℤ) (F : FiveQuanta) (T : TenQuanta) : Prop :=
  HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu + F.anomalyCoefficent +
    T.anomalyCoefficent = (0, 0)

instance : Decidable (AnomalyCancellation qHd qHu F T) :=
  inferInstanceAs (Decidable ((HdAnomalyCoefficent qHd + HuAnomalyCoefficent qHu
    + F.anomalyCoefficent + T.anomalyCoefficent) = (0, 0)))

lemma anomalyCoefficent_snd_eq_zero_of_anomalyCancellation
    {qHd qHu : Option ℤ} {F : FiveQuanta} {T : TenQuanta} (h : AnomalyCancellation qHd qHu F T) :
    ((HdAnomalyCoefficent qHd).2 + (HuAnomalyCoefficent qHu).2
    + (F.anomalyCoefficent).2 + (T.anomalyCoefficent).2)  = 0 := by
  trans  ((HdAnomalyCoefficent qHd)+ (HuAnomalyCoefficent qHu)
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

def Twig.filterAnomalyCancellation (I : CodimensionOneConfig) (qHd qHu : Option ℤ) :
    Twig → Twig := fun (.twig Q5 leafsList) =>
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
      let l10 :=  (TenQuanta.ofCharges I Q10.val).countP fun T =>
        - T.anomalyCoefficent ∈ l
      l10 ≠ 0

def Branch.filterAnomalyCancellation (I : CodimensionOneConfig) (qHd : Option ℤ) :
    Branch → Branch := fun (.branch qHu twigsList) =>
  .branch qHu <| twigsList.map fun t => t.filterAnomalyCancellation I qHd qHu

def Trunk.filterAnomalyCancellation  (I : CodimensionOneConfig) : Trunk → Trunk :=
    fun (.trunk qHd branchList) =>
  .trunk qHd <| branchList.map fun b => b.filterAnomalyCancellation I qHd

def filterAnomalyCancellation (I : CodimensionOneConfig) :
    Tree → Tree := fun (root tunksList) =>
  root <| tunksList.map fun t => t.filterAnomalyCancellation I

lemma mem_filterAnomalyCancellation_iff {I : CodimensionOneConfig} {T : Tree} {x : Charges}  :
    x ∈ filterAnomalyCancellation I T ↔ x ∈ T ∧
    ∃ F : FiveQuanta, ∃ T : TenQuanta,
      F ∈ FiveQuanta.ofCharges I x.2.2.1.val ∧ T ∈ TenQuanta.ofCharges I x.2.2.2.val ∧
      AnomalyCancellation x.1 x.2.1 F T := by
  constructor
  · intro h
    rw [mem_iff_mem_toMultiset] at h
    simp [toMultiset] at h
    obtain ⟨trunkA, htrunkA, branchA, hbranchA, twigA, htwigA, leafA, hleafA, heq⟩ := h
    simp [filterAnomalyCancellation] at htrunkA
    obtain ⟨trunkT, trunkT_mem, trunkA_eq⟩ := htrunkA
    subst trunkA_eq
    simp [Trunk.filterAnomalyCancellation] at hbranchA
    simp [Trunk.filterAnomalyCancellation] at heq
    obtain ⟨branchT, branchT_mem, branchA_eq⟩ := hbranchA
    subst branchA_eq
    simp [Branch.filterAnomalyCancellation] at htwigA
    simp [Branch.filterAnomalyCancellation]  at heq
    obtain ⟨twigT, twigT_mem, twigA_eq⟩ := htwigA
    subst twigA_eq
    simp [Twig.filterAnomalyCancellation]  at hleafA heq
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
    refine mem_of_parts (trunkT.filterAnomalyCancellation I)
      (branchT.filterAnomalyCancellation I trunkT.1)
      (twigT.filterAnomalyCancellation I trunkT.1 branchT.1) leafT ?_ ?_ ?_ ?_ ?_
    · simp [filterAnomalyCancellation]
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
        simp
        use T10
        simp_all
        use F
        simp_all
        constructor
        · exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc
        · exact Eq.symm (neg_eq_of_add_eq_zero_left hacc)
      · rw [Multiset.filter_eq_nil]
        simp
        use F
        simp_all
        exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc
    · subst x
      simp [Trunk.filterAnomalyCancellation, Branch.filterAnomalyCancellation,
        Twig.filterAnomalyCancellation, filterAnomalyCancellation]
      rw [if_neg]
      rw [Multiset.filter_eq_nil]
      simp
      obtain ⟨F, T10, F_mem, T10_mem, hacc⟩ := h2
      use F
      simp_all
      exact five_anomalyCoefficent_mod_three_zero_of_anomalyCancellation hacc

end Tree
end Charges
end SU5U1

end FTheory
