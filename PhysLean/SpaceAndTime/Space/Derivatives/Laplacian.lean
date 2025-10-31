/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Div
/-!

# Laplacian on Space


-/

namespace Space

/-!

## A. Laplacian on functions to ℝ

-/

/-- The scalar `laplacian` operator. -/
noncomputable def laplacian {d} (f : Space d → ℝ) :
    Space d → ℝ := fun x =>
  -- second derivative of f in i-th coordinate
  -- ∂²f/∂xᵢ²
  let df2 i x := ∂[i] (∂[i] f) x
  ∑ i, df2 i x

@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian

/-!

### A.1. Relation between laplacian and divergence of gradient

-/

lemma laplacian_eq_div_of_grad (f : Space → ℝ) :
    Δ f = ∇ ⬝ ∇ f := by
  unfold laplacian div grad Finset.sum coord basis
  simp only [Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero,
    EuclideanSpace.basisFun_apply, PiLp.inner_apply, EuclideanSpace.single_apply,
    RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-!

## B. Laplacian on vector valued functions

-/


/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x i =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  Δ (fi i) x

@[inherit_doc laplacianVec]
scoped[Space] notation "Δ" => laplacianVec


end Space
