/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
/-!

# Unbounded operators

-/

namespace QuantumMechanics

noncomputable section

open LinearPMap

-- Nothing here uses any specific properties of this particular Hilbert space
abbrev hilbSp d := SpaceDHilbertSpace d

/-- An `UnboundedOperator` is a linear map from a submodule of the Hilbert space
  to the Hilbert space, assumed to be both densely defined and closable. -/
@[ext]
structure UnboundedOperator (d : ℕ) where
  /-- The LinearPMap defining the unbounded operator. -/
  toLinearPMap : LinearPMap ℂ (hilbSp d) (hilbSp d)
  /-- The domain of the unbounded operator is dense in the Hilbert space. -/
  dense_domain : Dense (toLinearPMap.domain : Set (hilbSp d))
  /-- The unbounded operator is closable. -/
  is_closable : toLinearPMap.IsClosable

namespace UnboundedOperator

variable {d : ℕ} (U : UnboundedOperator d)

/-- Domain of `UnboundedOperator`. -/
def domain : Submodule ℂ (hilbSp d) := U.toLinearPMap.domain

/-- `UnboundedOperator` as a function. -/
@[coe]
def toFun : U.domain → (hilbSp d) := U.toLinearPMap.toFun

instance : CoeFun (UnboundedOperator d)
  (fun U : UnboundedOperator d ↦ U.domain → (hilbSp d)) := ⟨toFun⟩

@[simp]
lemma toFun_eq_coe (x : U.domain) : U.toFun x = U.toLinearPMap.toFun x := rfl

/-!
## Construction of unbounded operators
-/

variable
  {E : Submodule ℂ (hilbSp d)}
  {hE : Dense (E : Set (hilbSp d))}

/-- An `UnboundedOperator` constructed from a symmetric linear map on a dense submodule `E`. -/
def ofSymmetric (f : E →ₗ[ℂ] E) (hf : f.IsSymmetric) : UnboundedOperator d where
  toLinearPMap := LinearPMap.mk E (E.subtype ∘ₗ f)
  dense_domain := hE
  is_closable := by
    -- TODO: symmetric ∧ dense ⇒ closable
    unfold Dense at hE
    unfold LinearMap.IsSymmetric at hf
    sorry

@[simp]
lemma ofSymmetric_apply {f : E →ₗ[ℂ] E} {hf : f.IsSymmetric} (ψ : E) :
  (ofSymmetric (hE := hE) f hf).toLinearPMap ψ = E.subtypeL (f ψ) := rfl

/-!
## Closure
-/

/-- The closure of an unbounded operator. -/
def closure : UnboundedOperator d where
  toLinearPMap := U.toLinearPMap.closure
  dense_domain := by
    refine Dense.mono ?_ U.dense_domain
    exact HasCore.le_domain (closureHasCore U.toLinearPMap)
  is_closable := IsClosed.isClosable (IsClosable.closure_isClosed U.is_closable)

lemma closure_toLinearPMap : U.closure.toLinearPMap = U.toLinearPMap.closure := rfl

def IsClosed : Prop := U.toLinearPMap.IsClosed

lemma closure_isClosed : U.closure.IsClosed := IsClosable.closure_isClosed U.is_closable

/-!
## Adjoints
-/

/-- The adjoint of an unbounded operator, denoted as `U†`. -/
def adjoint : UnboundedOperator d where
  toLinearPMap := U.toLinearPMap.adjoint
  dense_domain := by sorry
  is_closable := IsClosed.isClosable (adjoint_isClosed U.dense_domain)

@[inherit_doc]
scoped postfix:1024 "†" => UnboundedOperator.adjoint

instance instStar : Star (UnboundedOperator d) where
  star := fun U ↦ U.adjoint

lemma adjoint_toLinearPMap : U†.toLinearPMap = U.toLinearPMap† := rfl

lemma isSelfAdjoint_def : IsSelfAdjoint U ↔ U† = U := Iff.rfl

lemma isSelfAdjoint_iff : IsSelfAdjoint U ↔ IsSelfAdjoint U.toLinearPMap := by
  rw [isSelfAdjoint_def, LinearPMap.isSelfAdjoint_def]
  constructor <;> intro h
  · rw [← adjoint_toLinearPMap, h]
  · rwa [UnboundedOperator.ext_iff, adjoint_toLinearPMap]

lemma adjoint_isClosed : (U†).IsClosed := LinearPMap.adjoint_isClosed U.dense_domain

/-
TODO: Rework below using `PiLp 2` (see [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html])
so that `hilbSp × hilbSp` has the structure of an inner product space.
-/

abbrev hilbSp2 (d : ℕ) := hilbSp d × hilbSp d

def inner2 (f g : hilbSp2 d) : ℂ := inner ℂ f.1 g.1 + inner ℂ f.2 g.2

lemma closure_adjoint_eq_adjoint : U.closure† = U† := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.closure.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]

  -- Remains to show `(graph.closure)^⟂ = graph^⟂`, which is exactly `Submodule.orthogonal_closure`.
  -- Need to "translate" to orthogonal complements and use inner product structure on `hilbSp2`.
  sorry

lemma adjoint_adjoint_eq_closure : U†† = U.closure := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U†.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]

  ext ψUψ
  simp only [Submodule.mem_adjoint_iff]

  -- Flip the sign of either `a` or `b` (which are general elements of `hilbSp` anyways)
  -- and package conditions into statements of orthogonality in `hilbSp × hilbSp`
  trans ∀ (f : hilbSp2 d), (∀ g ∈ U.toLinearPMap.graph, inner2 f g = 0) → inner2 f ψUψ = 0
  · constructor <;> intro h
    · intro f h1
      have h2 := h (-f.2) f.1
      simp only [inner_neg_left, sub_neg_eq_add] at h2
      apply h2
      intro a b hab
      rw [sub_eq_zero]
      nth_rw 1 [← InnerProductSpace.conj_inner_symm]
      nth_rw 2 [← InnerProductSpace.conj_inner_symm]
      apply RingHom.congr_arg
      rw [inner_neg_left, neg_eq_iff_add_eq_zero, add_comm]
      exact h1 (a, b) hab
    · intro a b h1
      rw [sub_eq_add_neg, ← inner_neg_left]
      apply h (b, -a)
      intro g hg
      unfold inner2
      rw [inner_neg_left, add_neg_eq_zero]
      nth_rw 1 [← InnerProductSpace.conj_inner_symm]
      nth_rw 2 [← InnerProductSpace.conj_inner_symm]
      apply RingHom.congr_arg
      apply Eq.symm
      rw [← sub_eq_zero]
      exact h1 g.1 g.2 hg

  -- Remains to show that `(graph^⟂)^⟂ = graph.topologicalClosure`,
  -- which is exactly `Submodule.orthogonal_orthogonal_eq_closure`.
  -- Need to "translate" to orthogonal complements and use inner product structure on `hilbSp2`.
  sorry

/-!
## Generalized eigenvectors
-/

/-- A map `F : D(U) →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U`
  if there is an eigenvalue `c` such that for all `ψ ∈ D(U)`, `F (U ψ) = c ⬝ F ψ`. -/
def IsGeneralizedEigenvector (F : U.domain →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : U.domain, ∃ ψ' : U.domain, ψ' = U ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSymmetric_iff
    {f : E →ₗ[ℂ] E} {hf : f.IsSymmetric} (F : E →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSymmetric (hE := hE) f hf) F c ↔ ∀ ψ : E, F (f ψ) = c • F ψ := by
  constructor <;> intro h ψ
  · obtain ⟨ψ', hψ', hψ''⟩ := h ψ
    apply SetLike.coe_eq_coe.mp at hψ'
    subst hψ'
    exact hψ''
  · use f ψ
    exact ⟨by simp, h ψ⟩

end UnboundedOperator

end
end QuantumMechanics
