/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Elems
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree.Basic
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
  ` {W1, Λ, W2, K1}` or R-parity violation `{β, Λ, W2, W4, K1, K2}`.   -/
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

## For trees

-/

def Tree.Trunk.IsPhenoConstrained (t : Tree.Trunk) : Prop :=
  match t with
  | Tree.Trunk.trunk qHd branches =>
    ∀ b ∈ branches,
      match b with
      | Tree.Branch.branch qHu twigs =>
      IsPresent μ (qHd, qHu) ∨
      ∀ t ∈ twigs,
        match t with
        | Tree.Twig.twig Q5 leafs =>
        IsPresent β (qHu, Q5) ∨
        IsPresent W4 (qHd, qHu, Q5) ∨
        ∀ l ∈ leafs,
          match l with
          | Tree.Leaf.leaf Q10 =>
          IsPresent W2 (qHd, Q10) ∨ IsPresent K2 (qHd, qHu, Q10) ∨
          IsPresent W1 (Q5, Q10) ∨ IsPresent Λ (Q5, Q10)
          ∨ IsPresent K1 (Q5, Q10)

instance (t : Tree.Trunk) : Decidable (Tree.Trunk.IsPhenoConstrained t) :=
  match t with
  | Tree.Trunk.trunk qHd branches =>
    inferInstanceAs (Decidable (∀ b ∈ branches,
      match b with
      | Tree.Branch.branch qHu twigs =>
        IsPresent μ (qHd, qHu) ∨
        ∀ t ∈ twigs,
          match t with
          | Tree.Twig.twig Q5 leafs =>
            IsPresent β (qHu, Q5) ∨
            IsPresent W4 (qHd, qHu, Q5) ∨
            ∀ l ∈ leafs,
              match l with
              | Tree.Leaf.leaf Q10 =>
                IsPresent W2 (qHd, Q10) ∨ IsPresent K2 (qHd, qHu, Q10) ∨
                IsPresent W1 (Q5, Q10) ∨ IsPresent Λ (Q5, Q10)
                ∨ IsPresent K1 (Q5, Q10)))

def Tree.IsPhenoConstrained (T : Tree) : Prop :=
  match T with
  | Tree.root trunks =>
    ∀ t ∈ trunks,
      t.IsPhenoConstrained

instance (T : Tree) : Decidable (Tree.IsPhenoConstrained T) :=
  match T with
  | Tree.root trunks =>
    inferInstanceAs (Decidable (∀ t ∈ trunks, t.IsPhenoConstrained))



def Tree.Trunk.IsPhenoConstrainedQ10 (t : Tree.Trunk) : Prop :=
  match t with
  | Tree.Trunk.trunk qHd branches =>
    ∀ b ∈ branches,
      match b with
      | Tree.Branch.branch qHu twigs =>
      ∀ t ∈ twigs,
        match t with
        | Tree.Twig.twig Q5 leafs =>
        ∀ l ∈ leafs,
          match l with
          | Tree.Leaf.leaf Q10 =>
          IsPresent W2 (qHd, Q10) ∨ IsPresent K2 (qHd, qHu, Q10) ∨
          IsPresent W1 (Q5, Q10) ∨ IsPresent Λ (Q5, Q10)
          ∨ IsPresent K1 (Q5, Q10)

instance (t : Tree.Trunk) : Decidable (Tree.Trunk.IsPhenoConstrainedQ10 t) :=
  match t with
  | Tree.Trunk.trunk qHd branches =>
    inferInstanceAs (Decidable (∀ b ∈ branches,
      match b with
      | Tree.Branch.branch qHu twigs =>
        ∀ t ∈ twigs,
          match t with
          | Tree.Twig.twig Q5 leafs =>
            ∀ l ∈ leafs,
              match l with
              | Tree.Leaf.leaf Q10 =>
                IsPresent W2 (qHd, Q10) ∨ IsPresent K2 (qHd, qHu, Q10) ∨
                IsPresent W1 (Q5, Q10) ∨ IsPresent Λ (Q5, Q10)
                ∨ IsPresent K1 (Q5, Q10)))

def Tree.IsPhenoConstrainedQ10 (T : Tree) : Prop :=
  match T with
  | Tree.root trunks =>
    ∀ t ∈ trunks,
      t.IsPhenoConstrainedQ10

instance (T : Tree) : Decidable (Tree.IsPhenoConstrainedQ10 T) :=
  match T with
  | Tree.root trunks =>
    inferInstanceAs (Decidable (∀ t ∈ trunks, t.IsPhenoConstrainedQ10))

/-!

## phenoInsert10

-/
namespace Tree

def Trunk.phenoInsertQ10 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>

    .trunk qHd (branches.map fun bs =>
      match bs with
      | .branch qHu twigs =>
        if IsPresent K2 (qHd, qHu, {x}) then
          .branch qHu {}
        else
          .branch qHu (twigs.map fun ts =>
            match ts with
            | .twig Q5 leafs =>
              if IsPresent Λ (Q5, {x}) then
                .twig Q5 {}
              else
             let leafFinst := leafs.map (fun l => match l with
              | .leaf ys => ys)
            let sub : Multiset (Finset ℤ) := leafFinst.filterMap (fun ys =>
              if ¬ insert x ys ∈ leafFinst then
                some (insert x ys)
              else
                none)
            let subFilter := sub.filter (fun ys =>
              ¬ IsPresent W1 (Q5, ys) ∧ ¬ IsPresent K1 (Q5, ys)
              ∧ ¬ IsPresent W2 (qHd, ys))
            (.twig Q5 (subFilter.map (fun ys => .leaf ys)))
     ))

def phenoInsertQ10 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ10 ts x))


def Trunk.phenoInsertQ5 (T : Trunk) (x : ℤ) : Trunk :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun bs =>
      match bs with
      | .branch qHu twigs =>
        if IsPresent β (qHu, {x}) ∨ IsPresent W4 (qHd, qHu, {x})  then
          .branch qHu {}
        else
          let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (insert x Q5)
            (leafs.filter (fun (.leaf Q10) => ¬ IsPresent W1 ({x}, Q10) ∧ ¬ IsPresent K1 ({x}, Q10)
             ∧ ¬ IsPresent Λ ((insert x Q5), Q10)  ∧
             ¬  Branch.mem (.branch qHu twigs) (qHu, (insert x Q5), Q10)

             )))

          .branch qHu <| insertTwigs



    )

def phenoInsertQ5 (T : Tree) (x : ℤ) : Tree :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (Trunk.phenoInsertQ5 ts x))


end Tree

end Charges

end SU5U1

end FTheory
