/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Pseudo-Riemannian Metrics on Smooth Manifolds

This file formalizes the fundamental notion of pseudo-Riemannian metrics on smooth manifolds
and establishes their basic properties. A pseudo-Riemannian metric equips a manifold with a
smoothly varying, non-degenerate, symmetric bilinear form on each tangent space, generalizing
the concept of an inner product space to curved spaces.

## Main Definitions

* `PseudoRiemannianMetric I n M`: A structure representing a `C^n` pseudo-Riemannian metric
  on a manifold `M` modelled on `(E, H)` with model with corners `I`. It consists of a family
  of non-degenerate, symmetric, continuous bilinear forms `gₓ` on each tangent space `TₓM`,
  varying `C^n`-smoothly with `x`. The base field `𝕜` is required to be `RCLike`, the model
  space `E` must be finite-dimensional, and the manifold `M` must be `C^{n+1}` smooth.

* `PseudoRiemannianMetric.flatEquiv g x`: The "musical isomorphism" from the tangent space at `x`
  to its dual space, representing the canonical isomorphism induced by the metric.

* `PseudoRiemannianMetric.sharpEquiv g x`: The inverse of the flat isomorphism, mapping from
  the dual space back to the tangent space.

## Implementation Notes

* The bilinear form `gₓ` at a point `x` is represented as a `ContinuousLinearMap`
  `val x : TₓM →L[𝕜] (TₓM →L[𝕜] 𝕜)`. This curried form `v ↦ (w ↦ gₓ(v, w))` encodes both
  the bilinear structure and its continuity.

* Smoothness is defined by requiring that for any two `C^n` vector fields `X, Y`, the scalar
  function `x ↦ gₓ(X x, Y x)` is `C^n` smooth (`ContMDiff n`).

* The manifold `M` must be `C^{n+1}` smooth (`IsManifold I (n + 1) M`) to ensure the tangent
  bundle is a `C^n` vector bundle, making the notion of `C^n` vector fields well-defined.

* Finite-dimensionality of the model space (`FiniteDimensional 𝕜 E`) guarantees that tangent
  spaces are finite-dimensional, which is necessary for establishing that non-degeneracy implies
  the existence of an isomorphism between the tangent space and its dual.
-/

section PseudoRiemannianMetric

noncomputable section

universe u v w

open Bundle Set Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

/-- Convert a continuous linear map representing a bilinear form to a `LinearMap.BilinForm`. -/
def ContinuousLinearMap.toBilinForm
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    (f : E →L[𝕜] (E →L[𝕜] 𝕜)) : LinearMap.BilinForm 𝕜 E :=
  LinearMap.mk₂ 𝕜 (fun v w => (f v) w)
    (fun v₁ v₂ w => by dsimp; rw [f.map_add]; rfl)
    (fun a v w => by dsimp; rw [f.map_smul]; rfl)
    (fun v w₁ w₂ => by dsimp; rw [(f v).map_add];)
    (fun a v w => (f v).map_smul a w)

-- We use Real-like fields for InnerProductSpace in Riemannian Metric
variable {𝕜 : Type u} [RCLike 𝕜] -- Stronger assumption, implies NontriviallyNormedField
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type w} [TopologicalSpace H] -- Chart space
-- Manifold M and ChartedSpace for E
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞} -- Model with corners and smoothness level

/-- A pseudo-Riemannian metric of smoothness class `C^n` on a manifold `M` modelled on `(E, H)`
    with model `I`. This structure defines a smoothly varying, non-degenerate, symmetric,
    continuous bilinear form `gₓ` on the tangent space `TₓM` at each point `x`.
    Requires `M` to be `C^{n+1}` smooth.
-/
@[ext]
structure PseudoRiemannianMetric
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    -- Instances ensuring the tangent bundle is a well-defined smooth vector bundle
    [TopologicalSpace (TangentBundle I M)]
    [FiberBundle E (TangentSpace I : M → Type _)]
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    [IsManifold I (n + 1) M] -- Manifold is C^{n+1}
    -- Tangent bundle is C^n
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I] : Type (max u v w) where
  /-- The metric tensor at each point `x : M`, represented as a continuous linear map
      `TₓM →L[𝕜] (TₓM →L[𝕜] 𝕜)`. Applying it twice, `(val x v) w`, yields `gₓ(v, w)`. -/
  protected val : ∀ (x : M), TangentSpace I x →L[𝕜] (TangentSpace I x →L[𝕜] 𝕜)
  /-- The metric is symmetric: `gₓ(v, w) = gₓ(w, v)`. -/
  protected symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v
  /-- The metric is non-degenerate: if `gₓ(v, w) = 0` for all `w`, then `v = 0`. -/
  protected nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w : TangentSpace I x,
    (val x v) w = 0) → v = 0
  /-- The metric varies smoothly: `x ↦ gₓ(Xₓ, Yₓ)` is a `C^n` function for `C^n`
      vector fields `X, Y`. -/
  protected smooth : ∀ (X Y : ContMDiffSection I E n (TangentSpace I)),
    ContMDiff I (modelWithCornersSelf 𝕜 𝕜) n (fun x => val x (X x) (Y x))

namespace PseudoRiemannianMetric

instance TangentSpace.addCommGroup (x : M) : AddCommGroup (TangentSpace I x) := by infer_instance
instance TangentSpace.module (x : M) : Module 𝕜 (TangentSpace I x) := by infer_instance

/-- If two vector spaces are linearly equivalent, and one is finite-dimensional,
    then so is the other. This version transfers the finite-dimensional property
    via a continuous linear equivalence. -/
lemma FiniteDimensional.of_equiv
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {F : Type w} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [FiniteDimensional 𝕜 E]
    (e : E ≃L[𝕜] F) : FiniteDimensional 𝕜 F :=
  LinearEquiv.finiteDimensional e.toLinearEquiv

/-- If two vector spaces are linearly equivalent, and one is finite-dimensional,
    then so is the other. This version works with a linear equivalence. -/
lemma FiniteDimensional.of_linearEquiv
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [AddCommGroup E] [Module 𝕜 E]
    {F : Type w} [AddCommGroup F] [Module 𝕜 F]
    [FiniteDimensional 𝕜 E]
    (e : E ≃ₗ[𝕜] F) : FiniteDimensional 𝕜 F := by
  exact Finite.equiv e

lemma VectorBundle.finiteDimensional_fiber
    (𝕜 : Type u) [RCLike 𝕜]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {B : Type w} [TopologicalSpace B]
    {E_bundle : B → Type*} [∀ x, AddCommGroup (E_bundle x)] [∀ x, Module 𝕜 (E_bundle x)]
    [TopologicalSpace (Bundle.TotalSpace F E_bundle)]
    [∀ x, TopologicalSpace (E_bundle x)]
    [FiberBundle F E_bundle] [VectorBundle 𝕜 F E_bundle]
    (x : B) : FiniteDimensional 𝕜 (E_bundle x) :=
  let triv := trivializationAt F E_bundle x
  let hx := mem_baseSet_trivializationAt F E_bundle x
  have h_linear : triv.IsLinear 𝕜 := VectorBundle.trivialization_linear' triv
  haveI : triv.IsLinear 𝕜 := h_linear
  let linear_equiv := triv.continuousLinearEquivAt 𝕜 x hx
  FiniteDimensional.of_equiv linear_equiv.symm

instance TangentSpace.finiteDimensional
  [FiniteDimensional 𝕜 E]
  [∀ x : M, TopologicalSpace (TangentSpace I x)]
  [TopologicalSpace (Bundle.TotalSpace E (TangentSpace I : M → Type _))]
  [FiberBundle E (TangentSpace I : M → Type _)]
  [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
  (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) :=
  VectorBundle.finiteDimensional_fiber 𝕜 (F := E) (E_bundle := TangentSpace I) x

variable
    [inst_top : TopologicalSpace (TangentBundle I M)]
    [inst_fib : FiberBundle E (TangentSpace I : M → Type _)]
    [inst_vec : VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    [inst_mani : IsManifold I (n + 1) M]
    [inst_cmvb : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]

/-- Convert the continuous linear map representation `val x` to the algebraic `LinearMap.BilinForm`.
    This is useful for leveraging lemmas about `BilinForm`. -/
def toBilinForm
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    LinearMap.BilinForm 𝕜 (TangentSpace I x) :=
  (g.val x).toBilinForm

/-- Coercion from PseudoRiemannianMetric to its function representation. -/
instance : CoeFun (@PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
        inst_fib inst_vec inst_mani inst_cmvb)
        (fun _ => ∀ x : M, TangentSpace I x →L[𝕜] (TangentSpace I x →L[𝕜] 𝕜)) where
           coe g := g.val

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
@[simp] lemma toBilinForm_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v w : TangentSpace I x) :
  g.toBilinForm x v w = g.val x v w := rfl

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
@[simp] lemma toBilinForm_isSymm
    (g : PseudoRiemannianMetric I n) (x : M) : (g.toBilinForm x).IsSymm := by
  intro v w
  simp only [toBilinForm_apply]
  exact g.symm x v w

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
@[simp] lemma toBilinForm_nondegenerate
    (g : PseudoRiemannianMetric I n) (x : M) :
    (g.toBilinForm x).Nondegenerate := by
  intro v hv
  simp_rw [toBilinForm_apply] at hv
  exact g.nondegenerate x v hv

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
lemma symm'
    (g : PseudoRiemannianMetric I n) (x : M) (v w : TangentSpace I x) :
    (g.val x v) w = (g.val x w) v :=
  g.symm x v w

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
lemma nondegenerate'
    (g : PseudoRiemannianMetric I n) (x : M) (v : TangentSpace I x)
    (h : ∀ w : TangentSpace I x, (g.val x v) w = 0) : v = 0 :=
  g.nondegenerate x v h

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
lemma smooth'
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (X Y : ContMDiffSection I E n (TangentSpace I)) :
    ContMDiff I (modelWithCornersSelf 𝕜 𝕜) n (fun x => (g.val x (X x)) (Y x)) :=
  g.smooth X Y

/-- Convert a pseudo-Riemannian metric at a point to a quadratic form. -/
@[simp] def toQuadraticForm
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    QuadraticForm 𝕜 (TangentSpace I x) where
  toFun v := g.val x v v
  toFun_smul a v := by
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul, pow_two]
  exists_companion' :=
      ⟨ LinearMap.mk₂ 𝕜 (fun v y => g.val x v y + g.val x y v)
        (fun v₁ v₂ y => by -- Additivity in v
          simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
          ring)
        (fun a v y => by -- Homogeneity in v
          simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
          ring_nf
          exact Eq.symm (DistribSMul.smul_add a (((g.val x) v) y) (((g.val x) y) v)))
        (fun v y₁ y₂ => by -- Additivity in y
          simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
          ring)
        (fun a v y => by -- Homogeneity in y
          simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
          ring_nf
          exact Eq.symm (DistribSMul.smul_add a (((g.val x) v) y) (((g.val x) y) v))),
            by
              intro v y
              simp only [LinearMap.mk₂_apply, ContinuousLinearMap.map_add,
                ContinuousLinearMap.add_apply, g.symm x]
              ring⟩

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
lemma toQuadraticForm_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v : TangentSpace I x) :
    g.toQuadraticForm x v = g.val x v v := rfl

/-- The "musical" isomorphism (index lowering) from the tangent space to its dual,
    induced by a pseudo-Riemannian metric. -/
def flat
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    TangentSpace I x →ₗ[𝕜] (TangentSpace I x →L[𝕜] 𝕜) :=
  { toFun := λ v => g.val x v,
    map_add' := λ v w => by simp only [ContinuousLinearMap.map_add],
    map_smul' := λ a v => by simp only [ContinuousLinearMap.map_smul]; exact rfl }

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
@[simp] lemma flat_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v w : TangentSpace I x) :
    (g.flat x v) w = g.val x v w := rfl

/-- The musical isomorphism as a continuous linear map. -/
def flatL
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    TangentSpace I x →L[𝕜] (TangentSpace I x →L[𝕜] 𝕜) :=
  { g.flat x with
    cont := ContinuousLinearMap.continuous (g.val x) }

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
@[simp] lemma flatL_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v w : TangentSpace I x) :
    (g.flatL x v) w = g.val x v w := rfl

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
/-- The linear map `flat` is injective due to non-degeneracy. -/
@[simp] lemma flat_inj
    (g : PseudoRiemannianMetric I n) (x : M) :
    Function.Injective (g.flat x) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply g.nondegenerate' x v
  intro w
  exact DFunLike.congr_fun hv w

omit [FiniteDimensional 𝕜 E] [ChartedSpace H E] in
/-- The continuous linear map `flatL` is injective. -/
@[simp] lemma flatL_inj
    (g : PseudoRiemannianMetric I n) (x : M) :
    Function.Injective (g.flatL x) := by
  intro v₁ v₂ h
  apply flat_inj g x
  exact h

omit [ChartedSpace H E] in
/-- The continuous linear map `flatL` is surjective because the tangent space is
    finite dimensional. -/
@[simp] lemma flatL_surj
    (g : PseudoRiemannianMetric I n) (x : M) :
    Function.Surjective (g.flatL x) := by
  haveI : FiniteDimensional 𝕜 (TangentSpace I x) := TangentSpace.finiteDimensional x
  have h_finrank_eq : finrank 𝕜 (TangentSpace I x) = finrank 𝕜 (TangentSpace I x →L[𝕜] 𝕜) := by
    have h_dual_eq : finrank 𝕜 (TangentSpace I x →L[𝕜] 𝕜) = finrank 𝕜 (Module.Dual 𝕜
    (TangentSpace I x)) := by
      let to_dual : (TangentSpace I x →L[𝕜] 𝕜) → Module.Dual 𝕜 (TangentSpace I x) :=
        fun f => f.toLinearMap
      let from_dual : Module.Dual 𝕜 (TangentSpace I x) → (TangentSpace I x →L[𝕜] 𝕜) := fun f =>
        ContinuousLinearMap.mk f (by
          apply LinearMap.continuous_of_finiteDimensional)
      let equiv : (TangentSpace I x →L[𝕜] 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 (TangentSpace I x) :=
      { toFun := to_dual,
        invFun := from_dual,
        map_add' := fun f g => by
          ext v; unfold to_dual; simp only [LinearMap.add_apply]; rfl,
        map_smul' := fun c f => by
          ext v; unfold to_dual; simp only [LinearMap.smul_apply]; rfl,
        left_inv := fun f => by
          ext v; unfold to_dual from_dual; simp,
        right_inv := fun f => by
          ext v; unfold to_dual from_dual; simp }
      exact LinearEquiv.finrank_eq equiv
    rw [h_dual_eq, ← Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq).mp (flatL_inj g x)

/-- The "musical" isomorphism (index lowering) from the tangent space to its dual,
    as a continuous linear equivalence. -/
@[simp] def flatEquiv
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb)
    (x : M) :
    TangentSpace I x ≃L[𝕜] (TangentSpace I x →L[𝕜] 𝕜) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective
      ((g.flatL x).toLinearMap)
      ⟨g.flatL_inj x, g.flatL_surj x⟩)

omit [ChartedSpace H E] in
lemma coe_flatEquiv
    (g : PseudoRiemannianMetric I n) (x : M) :
    (g.flatEquiv x : TangentSpace I x →ₗ[𝕜] (TangentSpace I x →L[𝕜] 𝕜)) = g.flatL x := rfl

omit [ChartedSpace H E] in
@[simp] lemma flatEquiv_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v w : TangentSpace I x) :
    (g.flatEquiv x v) w = g.val x v w := rfl

/-- The "musical" isomorphism (index raising) from the dual of the tangent space to the
    tangent space, induced by a pseudo-Riemannian metric. This is the inverse of `flatEquiv`. -/
def sharpEquiv
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    (TangentSpace I x →L[𝕜] 𝕜) ≃L[𝕜] TangentSpace I x :=
  (g.flatEquiv x).symm
#lint
/-- The index raising map `sharp` as a continuous linear map. -/
def sharpL
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    (TangentSpace I x →L[𝕜] 𝕜) →L[𝕜] TangentSpace I x :=
  (g.sharpEquiv x).toContinuousLinearMap

omit [ChartedSpace H E] in
lemma sharpL_eq_toContinuousLinearMap
    (g : PseudoRiemannianMetric I n) (x : M) :
  g.sharpL x = (g.sharpEquiv x).toContinuousLinearMap := rfl

omit [ChartedSpace H E] in
lemma coe_sharpEquiv
    (g : PseudoRiemannianMetric I n) (x : M) :
    (g.sharpEquiv x : (TangentSpace I x →L[𝕜] 𝕜) →L[𝕜] TangentSpace I x) = g.sharpL x := rfl

/-- The index raising map `sharp` as a linear map. -/
noncomputable def sharp
    (g : @PseudoRiemannianMetric 𝕜 _ E _ _ H _ M _ _ I n inst_top
    inst_fib inst_vec inst_mani inst_cmvb) (x : M) :
    (TangentSpace I x →L[𝕜] 𝕜) →ₗ[𝕜] TangentSpace I x :=
  (g.sharpEquiv x).toLinearEquiv.toLinearMap

omit [ChartedSpace H E] in
@[simp] lemma sharpL_apply_flatL
    (g : PseudoRiemannianMetric I n) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v :=
  (g.flatEquiv x).left_inv v

omit [ChartedSpace H E] in
@[simp] lemma flatL_apply_sharpL
    (g : PseudoRiemannianMetric I n) (x : M) (ω : TangentSpace I x →L[𝕜] 𝕜) :
    g.flatL x (g.sharpL x ω) = ω :=
  (g.flatEquiv x).right_inv ω

omit [ChartedSpace H E] in
/-- Applying `sharp` then `flat` recovers the original covector. -/
@[simp] lemma flat_sharp_apply
    (g : PseudoRiemannianMetric I n) (x : M) (ω : TangentSpace I x →L[𝕜] 𝕜) :
    g.flat x (g.sharp x ω) = ω := by
  -- Use the continuous versions and coerce
  have := flatL_apply_sharpL g x ω
  -- Need to relate flat and flatL, sharp and sharpL
  simp only [sharp, sharpL, flat, flatL, coe_flatEquiv]; simp only [coe_sharpEquiv,
             ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe] at this ⊢
  exact this

omit [ChartedSpace H E] in
@[simp] lemma sharp_flat_apply
    (g : PseudoRiemannianMetric I n) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  -- Use the continuous versions and coerce
  have := sharpL_apply_flatL g x v
  simp only [sharp, sharpL, flat, flatL]; simp only [coe_flatEquiv, coe_sharpEquiv,
             ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe] at this ⊢
  exact this

omit [ChartedSpace H E] in
/-- The metric evaluated at `sharp ω₁` and `sharp ω₂`. -/
@[simp] lemma apply_sharp_sharp
    (g : PseudoRiemannianMetric I n) (x : M) (ω₁ ω₂ : TangentSpace I x →L[𝕜] 𝕜) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  rw [← flatL_apply g x (g.sharpL x ω₁)]
  rw [flatL_apply_sharpL g x ω₁]

omit [ChartedSpace H E] in
/-- The metric evaluated at `v` and `sharp ω`. -/
lemma apply_vec_sharp
    (g : PseudoRiemannianMetric I n) (x : M) (v : TangentSpace I x) (ω : TangentSpace I x →L[𝕜] 𝕜) :
    g.val x v (g.sharpL x ω) = ω v := by
  rw [g.symm' x v (g.sharpL x ω)]
  rw [← flatL_apply g x (g.sharpL x ω)]
  rw [flatL_apply_sharpL g x ω]

end PseudoRiemannianMetric
