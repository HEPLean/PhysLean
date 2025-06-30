/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import PhysLean.Meta.Linters.Sorry
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Space

This file contains `d`-dimensional space.

## Note on implementation

The definition of `Space d` currently inherits all instances of
`EuclideanSpace ℝ (Fin d)`.

This, in particular, automatically equips `Space d` with a
norm. This norm induces a metric on `Space d` which is the standard
Euclidean metric. Thus `Space d` automatically corresponds to
flat space.

The definition of `deriv` through `fderiv` explicitly uses this metric.

`Space d` also inherits instances of `EuclideanSpace ℝ (Fin d)` such as
a zero vector, the ability to add two space positions etc, which
are not really allowed operations on `Space d`.

-/

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

namespace Space

/-- The standard basis of Space based on `Fin d`. -/
noncomputable def basis : OrthonormalBasis (Fin d) ℝ (Space d) :=
  EuclideanSpace.basisFun (Fin d) ℝ

/-- The standard coordinate functions of Space based on `Fin d`.

The notation `𝔁 μ p` can be used for this. -/
noncomputable def coord (μ : Fin d) (p : Space d) : ℝ :=
  inner ℝ p (basis μ)

lemma coord_apply (μ : Fin d) (p : Space d) :
    coord μ p = p μ := by
  simp [coord, basis]

noncomputable def coordCLM {d} (μ : Fin d) : Space d →L[ℝ] ℝ where
  toFun := coord μ
  map_add' := fun p q => by
    simp [coord, basis, inner_add_left]
  map_smul' := fun c p => by
    simp [coord, basis, inner_smul_left]
  cont := by
    unfold coord
    fun_prop

open ContDiff

@[fun_prop]
lemma coord_contDiff {i} : ContDiff ℝ ∞ (fun x : Space d => x.coord i) := by
  change ContDiff ℝ ∞ (coordCLM i)
  fun_prop

lemma coordCLM_apply (μ : Fin d) (p : Space d) :
    coordCLM μ p = coord μ p := by
  rfl

@[inherit_doc coord]
scoped notation "𝔁" => coord

/-!

## Calculus

-/

/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) : Space d → M :=
  (fun x => fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)))

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)) := by
  rfl

@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)

/-- The vector calculus operator `grad`. -/
noncomputable def grad (f : Space d → ℝ) :
  Space d → EuclideanSpace ℝ (Fin d) := fun x i =>
    ∂[i] f x

@[inherit_doc grad]
scoped[Space] notation "∇" => grad

/-- The vector calculus operator `curl`. -/
noncomputable def curl (f : Space → EuclideanSpace ℝ (Fin 3)) :
    Space → EuclideanSpace ℝ (Fin 3) := fun x =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  -- derivative of i-th component in j-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i j x := ∂[j] (fi i) x
  fun i =>
    match i with
    | 0 => df 2 1 x - df 1 2 x
    | 1 => df 0 2 x - df 2 0 x
    | 2 => df 1 0 x - df 0 1 x

@[inherit_doc curl]
macro (name := curlNotation) "∇" "×" f:term:100 : term => `(curl $f)

/-- The vector calculus operator `div`. -/
noncomputable def div (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → ℝ := fun x =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  -- derivative of i-th component in i-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i x := ∂[i] (fi i) x
  ∑ i, df i x

@[inherit_doc div]
macro (name := divNotation) "∇" "⬝" f:term:100 : term => `(div $f)

/-- The scalar `laplacian` operator. -/
noncomputable def laplacian (f : Space d → ℝ) :
    Space d → ℝ := fun x =>
  -- second derivative of f in i-th coordinate
  -- ∂²f/∂xᵢ²
  let df2 i x := ∂[i] (∂[i] f) x
  ∑ i, df2 i x

@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian

/-- The vector `laplacian_vec` operator. -/
noncomputable def laplacian_vec (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x i =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  Δ (fi i) x

@[inherit_doc laplacian_vec]
scoped[Space] notation "Δ" => laplacian_vec

/-- Notion of direction where `unit` returns a unit vector in the direction specified. -/
structure Direction (d : ℕ := 3) where
  /-- Unit vector specifying the direction. -/
  unit : EuclideanSpace ℝ (Fin d)
  norm : ‖unit‖ = 1

/-- Direction of a `Space` value with respect to the origin. -/
noncomputable def toDirection {d : ℕ} (x : Space d) (h : x ≠ 0) : Direction d where
  unit := (‖x‖⁻¹) • (x)
  norm := norm_smul_inv_norm h

end Space
