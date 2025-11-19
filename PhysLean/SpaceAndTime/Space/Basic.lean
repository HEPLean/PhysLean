/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.Meta.Linters.Sorry
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!

# Space

In this module, we define the the type `Space d` which corresponds
to a `d`-dimensional Euclidean space and prove some properties about it.

PhysLean sits downstream of Mathlib, and above we import the necessary Mathlib modules
which contain (perhaps transitively through imports) the definitions and theorems we need.

-/

/-!

## The `Space` type

-/

TODO "HB6RR" "In the above documentation describe the notion of a type, and
  introduce the type `Space d`."

TODO "HB6VC" "Convert `Space` from an `abbrev` to a `def`."

/-- The type `Space d` represents `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`.

-/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

namespace Space

/-!

## Basic operations on `Space`.

-/
/-!

## Instances on `Space`

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

@[simp]
lemma sum_apply {ι : Type} [Fintype ι] (f : ι → Space d) (i : Fin d) :
    (∑ x, f x) i = ∑ x, f x i := by
  change (WithLp.linearEquiv 2 ℝ _ (∑ x, f x)) i = _
  simp [-WithLp.linearEquiv_apply]
  rfl

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
  simp [basis, EuclideanSpace.basisFun_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

@[simp]
lemma basis_self {d} (i : Fin d) : basis i i = 1 := by
  simp [basis_apply]

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

lemma basis_eq_single {d} (i : Fin d) :
    basis i = EuclideanSpace.single i 1 := by
  simp [basis]

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

@[simp]
lemma direction_unit_sq_sum {d} (s : Direction d) :
    ∑ i : Fin d, (s.unit i) ^ 2 = 1 := by
  trans (‖s.unit‖) ^ 2
  · rw [PiLp.norm_sq_eq_of_L2]
    simp
  · rw [s.norm]
    simp

/-!

## One equiv

-/

/-- The linear isometric equivalence between `Space 1` and `ℝ`. -/
noncomputable def oneEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun x := WithLp.toLp 2 fun _ => x
  left_inv x := by
    ext i; fin_cases i; simp
  right_inv x := by simp
  map_add' x y := by rfl
  map_smul' c x := by rfl
  norm_map' x := by
    simp only [Fin.isValue, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    rw [@PiLp.norm_eq_of_L2]
    simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero, Real.norm_eq_abs, sq_abs,
      Finset.sum_singleton]
    exact Eq.symm (Real.sqrt_sq_eq_abs (x 0))

lemma oneEquiv_coe :
    (oneEquiv : Space 1 → ℝ) = fun x => x 0 := by
  rfl

lemma oneEquiv_symm_coe :
    (oneEquiv.symm : ℝ → Space 1) = (fun x => WithLp.toLp 2 fun _ => x) := by
  rfl

lemma oneEquiv_symm_apply (x : ℝ) (i : Fin 1) :
    oneEquiv.symm x i = x := by
  fin_cases i
  rfl

lemma oneEquiv_continuous :
    Continuous (oneEquiv : Space 1 → ℝ) := by
  simp [oneEquiv_coe]
  fun_prop

lemma oneEquiv_symm_continuous :
    Continuous (oneEquiv.symm : ℝ → Space 1) := by
  simp [oneEquiv_symm_coe]
  fun_prop

/-- The continuous linear equivalence between `Space 1` and `ℝ`. -/
noncomputable def oneEquivCLE : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ where
  toLinearEquiv := oneEquiv
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    erw [oneEquiv_coe]
    fun_prop
  continuous_invFun := by
    simp only [LinearEquiv.invFun_eq_symm]
    erw [oneEquiv_symm_coe]
    fun_prop

open MeasureTheory
lemma oneEquiv_measurableEmbedding : MeasurableEmbedding oneEquiv where
  injective := oneEquiv.injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑oneEquivCLE '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact oneEquiv.symm.continuous.measurable hs

lemma oneEquiv_symm_measurableEmbedding : MeasurableEmbedding oneEquiv.symm where
  injective := oneEquiv.symm.injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑oneEquivCLE.symm '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact oneEquiv.continuous.measurable hs

lemma oneEquiv_measurePreserving : MeasurePreserving oneEquiv volume volume :=
  LinearIsometryEquiv.measurePreserving oneEquiv

lemma oneEquiv_symm_measurePreserving : MeasurePreserving oneEquiv.symm volume volume := by
  exact LinearIsometryEquiv.measurePreserving oneEquiv.symm

lemma volume_eq_addHaar {d} : (volume (α := Space d)) = Space.basis.toBasis.addHaar := by
  exact (OrthonormalBasis.addHaar_eq_volume _).symm

end Space
