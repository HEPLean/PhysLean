/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.Charges.Tree
import PhysLean.Particles.SuperSymmetry.SU5.Charges.AllowsTerm
/-!

# Pheno constrained charges

We say a charge is pheno-constrained if it leads to allows proton decay or
R-parity violating terms.

We are actually intrested in the charges which are not pheno-constrained.

-/
namespace SuperSymmetry

namespace SU5

namespace Charges
open SuperSymmetry.SU5
open PotentialTerm

/-- A charge is pheno-constrained if it leads to the presence of any term causing proton decay
  ` {W1, Λ, W2, K1}` or R-parity violation `{β, Λ, W2, W4, K1, K2}`. -/
def IsPhenoConstrained (x : Charges) : Prop :=
  x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2 ∨ x.AllowsTerm W4 ∨
  x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1

instance decidableIsPhenoConstrained (x : Charges) : Decidable x.IsPhenoConstrained :=
  inferInstanceAs (Decidable (x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2
    ∨ x.AllowsTerm W4 ∨ x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1))

lemma isPhenoConstrained_of_subset {x y : Charges} (h : x ⊆ y)
    (hx : x.IsPhenoConstrained) : y.IsPhenoConstrained := by
  simp [IsPhenoConstrained] at *
  rcases hx with hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    have h' := allowsTerm_of_subset h hr
    simp_all

/-- The collection of charges of super-potential terms leading to a pheno-constrained model. -/
def phenoConstrainingChargesSP (x : Charges) : Multiset ℤ :=
  x.ofPotentialTerm μ + x.ofPotentialTerm β + x.ofPotentialTerm Λ +
  x.ofPotentialTerm W2 + x.ofPotentialTerm W4 + x.ofPotentialTerm W1

@[simp]
lemma phenoConstrainingChargesSP_empty :
    phenoConstrainingChargesSP ∅ = ∅ := by
  simp [phenoConstrainingChargesSP]

lemma phenoConstrainingChargesSP_of_subset {x y : Charges} (h : x ⊆ y) :
    x.phenoConstrainingChargesSP ⊆ y.phenoConstrainingChargesSP := by
  simp only [phenoConstrainingChargesSP]
  refine Multiset.subset_iff.mpr ?_
  intro z
  simp [or_assoc]
  intro hr
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals
    have h' := ofPotentialTerm_subset_of_subset h _ hr
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
open PhysLean FourTree
/-!

### Inserting `q10` charges into trees

-/

/-- The twig obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a twig. This assumes that all existing charges in the twig are
  already not pheno constrained. -/
def Twig.phenoInsertQ10 (t : Twig (Finset ℤ) (Finset ℤ)) (qHd : Option ℤ) (x : ℤ) :
    Twig (Finset ℤ) (Finset ℤ) :=
  match t with
  | .twig Q5 leafs =>
    if AllowsTerm (none, none, Q5, {x}) Λ then
      .twig Q5 {}
    else
      let leafFinst := leafs.map (fun (.leaf ys) => ys)
      let sub : Multiset (Finset ℤ) := leafFinst.filterMap (fun ys =>
        if ¬ insert x ys ∈ leafFinst then
          some (insert x ys)
        else
          none)
      let subFilter := sub.filter (fun ys =>
        ¬ AllowsTerm (none, none, Q5, ys) W1 ∧ ¬ AllowsTerm (none, none, Q5, ys) K1
        ∧ ¬ AllowsTerm (qHd, none, ∅, ys) W2)
      .twig Q5 (subFilter.map (fun ys => .leaf ys))

/-- The branch obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a branch. This assumes that all existing charges in the branch are
  already not pheno constrained. -/
def Branch.phenoInsertQ10 (b : Branch (Option ℤ) (Finset ℤ) (Finset ℤ)) (qHd : Option ℤ) (x : ℤ) :
    Branch (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match b with
  | .branch qHu twigs =>
      if AllowsTerm (qHd, qHu, ∅, {x}) K2 then
          .branch qHu {}
      else
        .branch qHu (twigs.map fun t => Twig.phenoInsertQ10 t qHd x)

/-- The trunk obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a trunk. This assumes that all existing charges in the trunk are
  already not pheno constrained. -/
def Trunk.phenoInsertQ10 (T : Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (x : ℤ) :
    Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun b => Branch.phenoInsertQ10 b qHd x)

/-- The tree obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q10` into all leafs of a tree. This assumes that all existing charges in the tree are
  already not pheno constrained. -/
def phenoInsertQ10 (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (x : ℤ) :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ10 ts x))

lemma mem_phenoInsertQ10_of_mem_allowsTerm
    (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (q10 : ℤ) (C : Charges)
    (h : C ∈ (T.uniqueMap4 (insert q10))) (hC : ¬ AllowsTerm (C.1, C.2.1, ∅, {q10}) K2
      ∧ ¬ AllowsTerm (none, none, C.2.2.1, {q10}) Λ
      ∧ ¬ AllowsTerm (none, none, C.2.2.1, C.2.2.2) W1 ∧
      ¬ AllowsTerm (none, none, C.2.2.1, C.2.2.2) K1
      ∧ ¬ AllowsTerm (C.1, none, ∅, C.2.2.2) W2) :
    C ∈ phenoInsertQ10 T q10 := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [uniqueMap4] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.uniqueMap4] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.uniqueMap4, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp only [Twig.uniqueMap4, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨Q10, ⟨leafT, leafT_mem, hQ10⟩, hPresent⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.uniqueMap4]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.uniqueMap4]
  have hC21 : C.2.2.1 = twigT.1 := by
    subst heq
    simp [Twig.uniqueMap4]
  have hC22 : C.2.2.2 = Q10 := by
    subst heq
    simp [Leaf.uniqueMap4, ← hPresent]
  have C_eq : C = (trunkT.1, branchT.1, twigT.1, Q10) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- Work on the goal
  apply mem_of_parts (Trunk.phenoInsertQ10 trunkT q10) (Branch.phenoInsertQ10 branchT
    (Trunk.phenoInsertQ10 trunkT q10).1 q10)
    (Twig.phenoInsertQ10 twigT (Trunk.phenoInsertQ10 trunkT q10).1 q10)
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
    simp only [Multiset.mem_map, Multiset.mem_filter, Multiset.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and, Leaf.leaf.injEq,
      exists_eq_right]
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
def Branch.phenoInsertQ5 (b : Branch (Option ℤ) (Finset ℤ) (Finset ℤ)) (qHd : Option ℤ) (x : ℤ) :
    Branch (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match b with
  | .branch qHu twigs =>
    if AllowsTerm (none, qHu, {x}, ∅) β ∨ AllowsTerm (qHd, qHu, {x}, ∅) W4 then
          .branch qHu {}
        else
          let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (insert x Q5)
            (leafs.filter (fun (.leaf Q10) => ¬ AllowsTerm (none, none, {x}, Q10) W1 ∧
              ¬ AllowsTerm (none, none, {x}, Q10) K1
              ∧ ¬ AllowsTerm (none, none, (insert x Q5), Q10) Λ ∧
              ¬ Branch.mem (.branch qHu twigs) (qHu, (insert x Q5), Q10))))
          .branch qHu <| insertTwigs

/-- The trunk obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q5` into all leafs of a trunk. This assumes that all existing charges in the trunk are
  already not pheno constrained. -/
def Trunk.phenoInsertQ5 (T : Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (x : ℤ) :
    Trunk (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun b => Branch.phenoInsertQ5 b qHd x)

/-- The tree obtained by taking the new, not pheno-constrained, charges obtained by inserting
  `q5` into all leafs of a tree. This assumes that all existing charges in the tree are
  already not pheno constrained. -/
def phenoInsertQ5 (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ)) (x : ℤ) :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ5 ts x))

lemma mem_phenoInsertQ5_of_mem_allowsTerm (T : FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ))
    (q5 : ℤ) (C : Charges)
    (h : C ∈ (T.uniqueMap3 (insert q5))) (hC : ¬ AllowsTerm (none, C.2.1, {q5}, ∅) β
      ∧ ¬ AllowsTerm (C.1, C.2.1, {q5}, ∅) W4 ∧
      ¬ AllowsTerm (none, none, {q5}, C.2.2.2) W1 ∧ ¬ AllowsTerm (none, none, {q5}, C.2.2.2) K1
      ∧ ¬ AllowsTerm (none, none, C.2.2.1, C.2.2.2) Λ) :
    C ∈ phenoInsertQ5 T q5 := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [uniqueMap3] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.uniqueMap3] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.uniqueMap3, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp [Twig.uniqueMap3, Multiset.mem_map, not_exists, not_and, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨leftI_mem, h_not_mem⟩ := leafI_mem
  -- Properties of C
  have hC1 : C.1 = trunkT.1 := by
    subst heq
    simp [Trunk.uniqueMap3]
  have hC2 : C.2.1 = branchT.1 := by
    subst heq
    simp [Branch.uniqueMap3]
  have hC21 : C.2.2.1 = insert q5 twigT.1 := by
    subst heq
    simp [Twig.uniqueMap3]
  have hC22 : C.2.2.2 = leafI.1 := by
    subst heq
    simp
  have C_eq : C = (trunkT.1, branchT.1, insert q5 twigT.1, leafI.1) := by
    simp [← hC1, ← hC2, ← hC21, ← hC22]
  -- Work on the goal
  apply mem_of_parts (Trunk.phenoInsertQ5 trunkT q5) (Branch.phenoInsertQ5 branchT
    (Trunk.phenoInsertQ5 trunkT q5).1 q5)
    (Twig.twig (insert q5 twigT.1)
        (Multiset.filter (fun (.leaf Q10) =>
        ¬ AllowsTerm (none, none, {q5}, Q10) W1 ∧ ¬ AllowsTerm (none, none, {q5}, Q10) K1
          ∧ ¬ AllowsTerm (none, none, (insert q5 twigT.1), Q10) Λ ∧
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

end SU5

end SuperSymmetry
