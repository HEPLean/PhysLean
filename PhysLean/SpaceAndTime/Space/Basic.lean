/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.Meta.Linters.Sorry
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Geometry.Manifold.IsManifold.Basic
/-!

# Space

In this file, also called a module, we define the `d`-dimensional Euclidean space,
and prove some proerties about it.

PhysLean sits downstream of Mathlib, and above we import the necessary Mathlib modules
which contain (perhaps transitively through imports) the definitions and theorems we need.

-/

/-!

## The `Space` type

-/

TODO "HB6RR" "In the above documentation describe the notion of a type, and
  introduce the type `Space d`."

TODO "HB6VC" "Convert `Space` from an `abbrev` to a `def`."

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

namespace Space

/-!

## Instances

-/

TODO "HB6YZ" "In the above documentation describe what an instance is, and why
  it is useful to have instances for `Space d`."

TODO "HB6WN" "After TODO 'HB6VC', give `Space d` the necessary instances
  using `inferInstanceAs`."

/-!

## Inner product

-/

lemma inner_eq_sum {d} (p q : Space d) :
    inner ℝ p q = ∑ i, p i * q i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr
  funext x
  exact Lean.Grind.CommSemiring.mul_comm (q x) (p x)

/-!

## Basis

-/

TODO "HB6Z4" "In the above documentation describe the notion of a basis
  in Lean."

/-- The standard basis of Space based on `Fin d`. -/
noncomputable def basis {d} : OrthonormalBasis (Fin d) ℝ (Space d) :=
  EuclideanSpace.basisFun (Fin d) ℝ

lemma basis_apply {d} (i j : Fin d) :
    basis i j = if i = j then 1 else 0 := by
  simp [basis, EuclideanSpace.basisFun_apply, Fin.isValue]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

@[simp]
lemma basis_self {d} (i : Fin d) : basis i i = 1 := by
  simp [basis_apply, if_pos rfl]

@[simp]
lemma basis_repr {d} (p : Space d) : basis.repr p = p := by rfl

@[simp high]
lemma inner_basis {d} (p : Space d) (i : Fin d) :
    inner ℝ p (basis i) = p i := by
  simp [inner_eq_sum, basis_apply]

@[simp high]
lemma basis_inner {d} (i : Fin d) (p : Space d) :
    inner ℝ (basis i) p = p i := by
  simp [inner_eq_sum, basis_apply]

/-!

## Coordinates

-/

/-- The standard coordinate functions of Space based on `Fin d`.

The notation `𝔁 μ p` can be used for this. -/
noncomputable def coord (μ : Fin d) (p : Space d) : ℝ :=
  inner ℝ p (basis μ)

lemma coord_apply (μ : Fin d) (p : Space d) :
    coord μ p = p μ := by
  simp [coord]

/-- The standard coordinate functions of Space based on `Fin d`, as a continuous linear map. -/
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

## Derivatives

-/

TODO "HB63O" "In the above documentation describe the different notions
  of a derivative in Lean."

/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
noncomputable def deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) : Space d → M :=
  (fun x => fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)))

@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (EuclideanSpace.single μ (1:ℝ)) := by
  rfl

lemma deriv_eq_fderiv_basis [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by
  rw [deriv_eq]
  congr
  funext i
  simp only [EuclideanSpace.single_apply, basis_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

/-!

## Gradient

-/

/-- The vector calculus operator `grad`. -/
noncomputable def grad {d} (f : Space d → ℝ) :
  Space d → EuclideanSpace ℝ (Fin d) := fun x i => ∂[i] f x

@[inherit_doc grad]
scoped[Space] notation "∇" => grad

/-!

## Curl

-/

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

/-!

## Div

-/

/-- The vector calculus operator `div`. -/
noncomputable def div {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → ℝ := fun x =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  -- derivative of i-th component in i-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i x := ∂[i] (fi i) x
  ∑ i, df i x

@[inherit_doc div]
macro (name := divNotation) "∇" "⬝" f:term:100 : term => `(div $f)

/-!

## Laplacians

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

/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x i =>
  -- get i-th component of `f`
  let fi i x := coord i (f x)
  Δ (fi i) x

@[inherit_doc laplacianVec]
scoped[Space] notation "Δ" => laplacianVec

/-!

## Directions

-/

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
