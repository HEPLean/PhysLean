/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Elems
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Insert
/-!

# Pheno constrained charges

We say a charge is pheno-constrained if it leads to allows proton decay or
R-parity violating terms.

We are actually intrested in the charges which are not pheno-constrained.

-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile

/-- A charge is pheno-constrained if it leads to the presence of any term causing proton decay
  ` {W1, Λ, W2, K1}` or R-parity violation `{β, Λ, W2, W4, K1, K2}`. -/
def IsPhenoConstrained (x : Charges) : Prop :=
  IsPresent μ (toChargeProfile μ x) ∨
  IsPresent β (toChargeProfile β x) ∨
  IsPresent Λ (toChargeProfile Λ x) ∨
  IsPresent W2 (toChargeProfile W2 x) ∨
  IsPresent W4 (toChargeProfile W4 x) ∨
  IsPresent K1 (toChargeProfile K1 x) ∨
  IsPresent K2 (toChargeProfile K2 x) ∨
  IsPresent W1 (toChargeProfile W1 x)

instance decidableIsPhenoConstrained (x : Charges) : Decidable x.IsPhenoConstrained :=
  inferInstanceAs (Decidable (IsPresent μ (toChargeProfile μ x) ∨
    IsPresent β (toChargeProfile β x) ∨
    IsPresent Λ (toChargeProfile Λ x) ∨
    IsPresent W2 (toChargeProfile W2 x) ∨
    IsPresent W4 (toChargeProfile W4 x) ∨
    IsPresent K1 (toChargeProfile K1 x) ∨
    IsPresent K2 (toChargeProfile K2 x) ∨
    IsPresent W1 (toChargeProfile W1 x)))

lemma isPhenoConstrained_of_subset {x y : Charges} (h : x ⊆ y)
    (hx : x.IsPhenoConstrained) : y.IsPhenoConstrained := by
  simp [IsPhenoConstrained] at *
  rcases hx with hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    have h' := isPresent_of_subset (toChargeProfile_subset_of_subset _ h) hr
    simp_all

/-!

## Inserting charges into trees, with pheno constraints

We define two functions `phenoInsertQ10` and `phenoInsertQ5` which for a tree
`T` respectively give all not pheno-constrained new charges obtained by inserting a
`q10` or `q5` charge into the charges in `T`.

This is related to the `insertQ10` and `insertQ5` functions, which insert a charge into a tree
`T`, but do not check if the new charges is pheno-constrained.

-/

namespace Tree

/-!

### Inserting `q10` charges into trees

-/

/-- The twig obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a twig. This assumes that all existing charges in the twig are
  already not pheno constrained. -/
def Twig.phenoInsertQ10 (t : Twig) (qHd : Option ℤ) (x : ℤ) : Twig :=
  match t with
  | .twig Q5 leafs =>
    if IsPresent Λ (Q5, {x}) then
      .twig Q5 {}
    else
      let leafFinst := leafs.map (fun (.leaf ys) => ys)
      let sub : Multiset (Finset ℤ) := leafFinst.filterMap (fun ys =>
        if ¬ insert x ys ∈ leafFinst then
          some (insert x ys)
        else
          none)
      let subFilter := sub.filter (fun ys =>
        ¬ IsPresent W1 (Q5, ys) ∧ ¬ IsPresent K1 (Q5, ys)
        ∧ ¬ IsPresent W2 (qHd, ys))
      .twig Q5 (subFilter.map (fun ys => .leaf ys))

/-- The branch obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a branch. This assumes that all existing charges in the branch are
  already not pheno constrained. -/
def Branch.phenoInsertQ10 (b : Branch) (qHd : Option ℤ) (x : ℤ) : Branch :=
  match b with
  | .branch qHu twigs =>
      if IsPresent K2 (qHd, qHu, {x}) then
          .branch qHu {}
      else
        .branch qHu (twigs.map fun t => Twig.phenoInsertQ10 t qHd x)

/-- The trunk obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a trunk. This assumes that all existing charges in the trunk are
  already not pheno constrained. -/
def Trunk.phenoInsertQ10 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun b => Branch.phenoInsertQ10 b qHd x)

/-- The tree obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a tree. This assumes that all existing charges in the tree are
  already not pheno constrained. -/
def phenoInsertQ10 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ10 ts x))

lemma mem_insertQ10_and_not_isPresent_of_mem_phenoInsertQ10 (T : Tree) (q10 : ℤ) (C : Charges)
    (h : C ∈ (phenoInsertQ10 T q10)) : C ∈ (T.insertQ10 q10)
      ∧ ¬ IsPresent K2 (C.1, C.2.1, {q10})
      ∧ ¬ IsPresent Λ (C.2.2.1, {q10})
      ∧ ¬ IsPresent W1 (C.2.2.1, C.2.2.2) ∧ ¬ IsPresent K1 (C.2.2.1, C.2.2.2)
      ∧ ¬ IsPresent W2 (C.1, C.2.2.2) := by
  -- We first recover the trunk, branch, twig and leaf in T which corresponds to C.
  simp [phenoInsertQ10, Membership.mem, mem] at h
  obtain ⟨trunkP, trunkP_mem, hC⟩ := h
  change trunkP ∈ (Multiset.map (fun ts => ts.phenoInsertQ10 q10) T.1) at trunkP_mem
  simp [Multiset.mem_map] at trunkP_mem
  -- trunkT is the trunk in T which corresponds to C. C does not live in this trunk.
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkP_mem
  simp [Trunk.mem] at hC
  obtain ⟨C_fst, branchP, branchP_mem, hC⟩ := hC
  simp [Trunk.phenoInsertQ10] at branchP_mem
  -- branchT is the branch in trunkT which corresponds to C. C does not live in this branch.
  -- C lives in branchP
  obtain ⟨branchT, branchT_mem, branchP_eq⟩ := branchP_mem
  by_cases hK2 : IsPresent K2 (trunkT.1, branchT.1, {q10})
  · simp_all [Branch.phenoInsertQ10]
    rw [← branchP_eq] at hC
    simp [Branch.mem] at hC
  simp_all [Branch.phenoInsertQ10]
  match branchP with
  | .branch qHu twigsP =>
  simp at branchP_eq
  obtain ⟨rfl, twigsP_eq⟩ := branchP_eq
  simp [Branch.mem] at hC
  obtain ⟨c_qHu_eq, twigP, twigP_mem, hC⟩ := hC
  -- getting twigT
  rw [← twigsP_eq] at twigP_mem
  simp at twigP_mem
  obtain ⟨twigT, twigT_mem, twigP_eq⟩ := twigP_mem
  -- The condition on Λ
  by_cases hΛ : IsPresent Λ (twigT.1, {q10})
  · simp_all [Twig.phenoInsertQ10]
    rw [← twigP_eq] at hC
    simp [Twig.mem] at hC
  simp_all [Twig.phenoInsertQ10]
  -- Getting leafP
  match twigP with
  | .twig Q5 leafsP =>
  simp at twigP_eq
  obtain ⟨rfl, leafsP_eq⟩ := twigP_eq
  simp [Twig.mem] at hC
  obtain ⟨c_Q5_eq, leafP, leafP_mem, hC⟩ := hC
  -- Getting leafT
  rw [← leafsP_eq] at leafP_mem
  simp at leafP_mem
  obtain ⟨Q10P, ⟨⟨leafT, leafT_mem, h1⟩, hPresent⟩, h2⟩ := leafP_mem
  have hQ10P : Q10P = C.2.2.2 := by
    simp [Leaf.mem] at hC
    rw [← hC, ← h2]
  -- The goal
  apply And.intro
  · apply mem_of_parts (trunkT.insertQ10 q10) (branchT.insertQ10 q10)
      (twigT.insertQ10 q10) (leafT.insertQ10 q10)
    · simp [insertQ10]
      use trunkT
    · simp [Trunk.insertQ10]
      use branchT
    · simp [Branch.insertQ10]
      use twigT
    · simp [Twig.insertQ10]
      use Q10P
      constructor
      · use leafT
      · rw [← h1.2]
        rfl
    · simp_all only [Trunk.insertQ10, Branch.insertQ10, Twig.insertQ10, Leaf.insertQ10,
        Trunk.phenoInsertQ10]
      simp [Leaf.mem] at hC
      rw [hC]
      rfl
  simp_all
  simp [Trunk.phenoInsertQ10] at C_fst
  simp_all

lemma mem_phenoInsertQ10_of_mem_isPresent (T : Tree) (q10 : ℤ) (C : Charges)
    (h : C ∈ (T.insertQ10 q10)) (hC : ¬ IsPresent K2 (C.1, C.2.1, {q10})
      ∧ ¬ IsPresent Λ (C.2.2.1, {q10})
      ∧ ¬ IsPresent W1 (C.2.2.1, C.2.2.2) ∧ ¬ IsPresent K1 (C.2.2.1, C.2.2.2)
      ∧ ¬ IsPresent W2 (C.1, C.2.2.2)) :
    C ∈ phenoInsertQ10 T q10 := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [insertQ10] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.insertQ10] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.insertQ10, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp only [Twig.insertQ10, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨Q10, ⟨leafT, leafT_mem, hQ10⟩, hPresent⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.insertQ10]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.insertQ10]
  have hC21 : C.2.2.1 = twigT.1 := by
    subst heq
    simp [Twig.insertQ10]
  have hC22 : C.2.2.2 = Q10 := by
    subst heq
    simp [Leaf.insertQ10, ← hPresent]
  have C_eq : C = (trunkT.1, branchT.1, twigT.1, Q10) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- Work on the goal
  apply mem_of_parts (trunkT.phenoInsertQ10 q10) (branchT.phenoInsertQ10
    (trunkT.phenoInsertQ10 q10).1 q10) (twigT.phenoInsertQ10 (trunkT.phenoInsertQ10 q10).1 q10)
    (.leaf Q10)
  · simp [phenoInsertQ10]
    use trunkT
  · simp [Trunk.phenoInsertQ10]
    use branchT
  · simp [Branch.phenoInsertQ10]
    rw [if_neg]
    · simp
      use twigT
    · simp [Trunk.phenoInsertQ10, ← hC1, ← hC2]
      exact hC.1
  · simp [Twig.phenoInsertQ10]
    rw [if_neg]
    swap
    · rw [← hC21]
      exact hC.2.1
    simp
    constructor
    · use leafT
    · rw [← hC21, ← hC22]
      simp_all [Trunk.phenoInsertQ10]
  · subst C_eq
    simp [Trunk.phenoInsertQ10, Branch.phenoInsertQ10]
    rw [if_neg]
    swap
    · simp_all
    simp [Twig.phenoInsertQ10]
    rw [if_neg]
    simp_all

/-!

### Inserting `q5` charges into trees

-/

/-- The branch obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q5` into all leafs of a branch. This assumes that all existing charges in the branch are
  already not pheno constrained. -/
def Branch.phenoInsertQ5 (b : Branch) (qHd : Option ℤ) (x : ℤ) : Branch :=
  match b with
  | .branch qHu twigs =>
    if IsPresent β (qHu, {x}) ∨ IsPresent W4 (qHd, qHu, {x}) then
          .branch qHu {}
        else
          let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (insert x Q5)
            (leafs.filter (fun (.leaf Q10) => ¬ IsPresent W1 ({x}, Q10) ∧ ¬ IsPresent K1 ({x}, Q10)
              ∧ ¬ IsPresent Λ ((insert x Q5), Q10) ∧
              ¬ Branch.mem (.branch qHu twigs) (qHu, (insert x Q5), Q10))))
          .branch qHu <| insertTwigs

/-- The trunk obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q5` into all leafs of a trunk. This assumes that all existing charges in the trunk are
  already not pheno constrained. -/
def Trunk.phenoInsertQ5 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun b => b.phenoInsertQ5 qHd x)

/-- The tree obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q5` into all leafs of a tree. This assumes that all existing charges in the tree are
  already not pheno constrained. -/
def phenoInsertQ5 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ5 ts x))

lemma mem_phenoInsertQ5_of_mem_isPresent (T : Tree) (q5 : ℤ) (C : Charges)
    (h : C ∈ (T.insertQ5 q5)) (hC : ¬ IsPresent β (C.2.1, {q5})
      ∧ ¬ IsPresent W4 (C.1, C.2.1, {q5}) ∧
      ¬ IsPresent W1 ({q5}, C.2.2.2) ∧ ¬ IsPresent K1 ({q5}, C.2.2.2)
      ∧ ¬ IsPresent Λ (C.2.2.1, C.2.2.2)) :
    C ∈ phenoInsertQ5 T q5 := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [insertQ5] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.insertQ5] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.insertQ5, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp [Twig.insertQ5, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨leftI_mem, h_not_mem⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.insertQ5]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.insertQ5]
  have hC21 : C.2.2.1 = insert q5 twigT.1 := by
    subst heq
    simp [Twig.insertQ5]
  have hC22 : C.2.2.2 = leafI.1 := by
    subst heq
    simp [Leaf.insertQ10]
  have C_eq : C = (trunkT.1, branchT.1, insert q5 twigT.1, leafI.1) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- Work on the goal
  apply mem_of_parts (trunkT.phenoInsertQ5 q5) (branchT.phenoInsertQ5
    (trunkT.phenoInsertQ5 q5).1 q5)
    (Twig.twig (insert q5 twigT.1)
        (Multiset.filter (fun (.leaf Q10) =>
        ¬ IsPresent W1 ({q5}, Q10) ∧ ¬ IsPresent K1 ({q5}, Q10)
          ∧ ¬ IsPresent Λ ((insert q5 twigT.1), Q10) ∧
          ¬(Branch.branch branchT.1 branchT.2).mem (branchT.1, insert q5 twigT.1, Q10))
          twigT.2)) (leafI)
  · simp [phenoInsertQ5]
    use trunkT
  · simp [Trunk.phenoInsertQ5]
    use branchT
  · simp [Branch.phenoInsertQ5]
    rw [if_neg]
    · simp
      use twigT
    · simp [Trunk.phenoInsertQ5, ← hC1, ← hC2]
      exact ⟨hC.1, hC.2.1⟩
  · simp_all
  · simp
    subst C_eq
    simp [Trunk.phenoInsertQ5, Branch.phenoInsertQ5]
    rw [if_neg]
    simp_all

end Tree

end Charges

end SU5U1

end FTheory
