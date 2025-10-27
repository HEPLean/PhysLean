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
structure Space (d : ℕ := 3) where
  val : Fin d → ℝ

namespace Space

lemma eq_of_val {d} {p q : Space d} (h : p.val = q.val ) :
    p = q := by
  cases p
  cases q
  congr

/-!

## B. Instances on `Space`

-/

/-!

## B.1. Instance of coercion to functions
-/

instance {d} : CoeFun (Space d) (fun _ => Fin d → ℝ) where
  coe p := p.val


@[ext]
lemma eq_of_apply {d} {p q : Space d}
    (h : ∀ i : Fin d, p i = q i) : p = q := by
  apply eq_of_val
  funext i
  exact h i

/-!

## B.1. Instance of an additive commutative monoid

-/

instance {d} : Add (Space d) where
  add p q := ⟨fun i => p.val i + q.val i⟩

@[simp]
lemma add_val {d: ℕ} (x y : Space d) :
    (x + y).val = x.val + y.val := rfl

@[simp]
lemma add_apply {d : ℕ} (x y : Space d) (i : Fin d) :
    (x + y) i = x i + y i := by
  simp [add_val]

instance {d} : Zero (Space d) where
  zero := ⟨fun _ => 0⟩

@[simp]
lemma zero_val {d : ℕ} : (0 : Space d).val = fun _ => 0 := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin d) :
    (0 : Space d) i = 0 := by
  simp [zero_val]

instance {d} : AddCommMonoid (Space d) where
  add_assoc a b c:= by
    apply eq_of_val
    simp only [add_val]
    ring
  zero_add a := by
    apply eq_of_val
    simp only [zero_val, add_val, add_eq_right]
    rfl
  add_zero a := by
    apply eq_of_val
    simp only [zero_val, add_val, add_eq_left]
    rfl
  add_comm a b := by
    apply eq_of_val
    simp only [add_val]
    ring
  nsmul n a := ⟨fun i => n • a.val i⟩

@[simp]
lemma nsmul_val {d : ℕ} (n : ℕ) (a : Space d) :
   (n • a).val = fun i => n • a.val i := rfl

@[simp]
lemma nsmul_apply {d : ℕ} (n : ℕ) (a : Space d) (i : Fin d) :
    (n • a) i = n • (a i) := by rfl

/-!

## B.2. Instance of a module over `ℝ`

-/

instance {d} : SMul ℝ (Space d) where
  smul c p := ⟨fun i => c * p.val i⟩

@[simp]
lemma smul_val {d : ℕ} (c : ℝ) (p : Space d) :
    (c • p).val = fun i => c * p.val i := rfl

@[simp]
lemma smul_apply {d : ℕ} (c : ℝ) (p : Space d) (i : Fin d) :
    (c • p) i = c * (p i) := by rfl

instance {d} : Module ℝ (Space d) where
  one_smul x := by
    ext i
    simp
  mul_smul a b x := by
    ext i
    simp
    ring
  smul_add a x y := by
    ext i
    simp
    ring
  smul_zero a := by
    ext i
    simp
  add_smul a b x := by
    ext i
    simp
    ring
  zero_smul x := by
    ext i
    simp

/-!

## B.3. Addition of Euclidean spaces

-/

noncomputable instance : VAdd (EuclideanSpace ℝ (Fin d)) (Space d) where
  vadd v s := ⟨fun i => v i + s.val i⟩

@[simp]
lemma vadd_val {d} (v : EuclideanSpace ℝ (Fin d)) (s : Space d) :
    (v +ᵥ s).val = fun i => v i + s.val i := rfl

@[simp]
lemma vadd_apply {d} (v : EuclideanSpace ℝ (Fin d))
    (s : Space d) (i : Fin d) :
    (v +ᵥ s) i = v i + s i := by rfl

lemma vadd_transitive {d} (s1 s2 : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), v +ᵥ s1 = s2 := by
  use fun i => s2 i - s1 i
  ext i
  simp

lemma eq_vadd_zero {d} (s : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), s = v +ᵥ (0 : Space d) := by
  obtain ⟨v, h⟩ := vadd_transitive 0 s
  use v
  rw [h]

@[simp]
lemma smul_vadd_zero {d} (k : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    k • (v +ᵥ (0 : Space d)) = (k • v) +ᵥ (0 : Space d) := by
  ext i
  simp

noncomputable instance : AddAction (EuclideanSpace ℝ (Fin d)) (Space d) where
  zero_vadd s := by
    ext i
    simp
  add_vadd v1 v2 s := by
    ext i
    simp
    ring

@[simp]
lemma add_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) + (v2 +ᵥ (0 : Space d))= (v1 + v2) +ᵥ (0 : Space d)  := by
  ext i
  simp

/-!

## B.3. Instance of an inner product space

-/

noncomputable instance {d} : Norm (Space d) where
  norm p := √ (∑ i, (p i)^2)

lemma norm_eq {d} (p : Space d) : ‖p‖ = √ (∑ i, (p i) ^ 2) := by
  rfl

lemma norm_sq_eq {d} (p : Space d) :
    ‖p‖ ^ 2 = ∑ i, (p i) ^ 2 := by
  rw [norm_eq]
  refine Real.sq_sqrt ?_
  positivity

@[simp]
lemma norm_vadd_zero {d} (v : EuclideanSpace ℝ (Fin d))  :
    ‖v +ᵥ (0 : Space d)‖ = ‖v‖ := by
  simp [norm_eq, PiLp.norm_eq_of_L2]


instance : Neg (Space d) where
  neg p := ⟨fun i => - (p.val i)⟩

@[simp]
lemma neg_val {d : ℕ} (p : Space d) :
    (-p).val = fun i => - (p.val i) := rfl

@[simp]
lemma neg_apply {d : ℕ} (p : Space d) (i : Fin d) :
    (-p) i = - (p i) := by rfl


noncomputable instance {d} : AddCommGroup (Space d) where
  zsmul z p := ⟨fun i => z * p.val i⟩
  neg_add_cancel p := by
    ext i
    simp
  zsmul_zero' p := by
    ext i
    simp
  zsmul_succ' n p := by
    ext i
    simp
    ring
  zsmul_neg' n p := by
    ext i
    simp
    ring

@[simp]
lemma sub_apply {d} (p q : Space d) (i : Fin d) :
    (p - q) i = p i - q i := by
  simp [sub_eq_add_neg, neg_apply, add_apply]

@[simp]
lemma sub_val {d} (p q : Space d) :
    (p - q).val = fun i => p.val i - q.val i := by rfl

@[simp]
lemma vadd_zero_sub_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) - (v2 +ᵥ (0 : Space d)) = (v1 - v2) +ᵥ (0 : Space d) := by
  ext i
  simp [sub_apply, vadd_apply]

noncomputable instance {d} : SeminormedAddCommGroup (Space d) where
  dist_self x := by
    simp [norm_eq]
  dist_comm x y := by
    simp [norm_eq]
    congr
    funext i
    ring
  dist_triangle := by
    intros x y z
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simp [vadd_zero_sub_vadd_zero, norm_vadd_zero]
    exact norm_sub_le_norm_sub_add_norm_sub v1 v2 v3

@[simp]
lemma dist_eq {d} (p q : Space d) :
    dist p q = ‖p - q‖ := by
  rfl

noncomputable instance : NormedAddCommGroup (Space d) where
  eq_of_dist_eq_zero := by
    intro x y h
    simp at h
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simp only [vadd_zero_sub_vadd_zero, norm_vadd_zero] at h
    congr
    exact eq_of_dist_eq_zero h

instance {d} : Inner ℝ (Space d) where
  inner p q := ∑ i, p i * q i

@[simp]
lemma inner_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (v1 +ᵥ (0 : Space d)) (v2 +ᵥ (0 : Space d)) = Inner.inner ℝ v1 v2 := by
  simp [inner, vadd_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inner_apply {d} (p q : Space d) :
    inner ℝ p q = ∑ i, p i * q i := by rfl


instance {d} : InnerProductSpace ℝ (Space d) where
  norm_smul_le a x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp
    exact norm_smul_le a v
  norm_sq_eq_re_inner x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp
    simpa using norm_sq_eq_re_inner (𝕜 := ℝ) v
  conj_inner_symm x y := by
    simp [inner_apply]
    congr
    funext i
    ring
  add_left x y z := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simp
    exact InnerProductSpace.add_left v1 v2 v3
  smul_left x y a := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simp
    exact InnerProductSpace.smul_left v1 v2 a




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
    inner ℝ p q = ∑ i, p i * q i := by rfl

@[simp]
lemma sum_apply {d} {ι : Type} [Fintype ι] (f : ι → Space d) (i : Fin d) :
    (∑ x, f x) i = ∑ x, f x i := by
  let P (ι : Type) [Fintype ι]  : Prop := ∀ (f : ι → Space d) (i : Fin d), (∑ x, f x) i = ∑ x, f x i
  have h1 : P ι := by
    apply  Fintype.induction_empty_option
    · intro α β h e h  f i
      rw [← @e.sum_comp _, h, ← @e.sum_comp _]
    · simp [P]
    · intro α _ h f i
      simp
      rw [h]
  exact h1 f i

/-!

## Basis

-/

TODO "HB6Z4" "In the above documentation describe the notion of a basis
  in Lean."

/-- The standard basis of Space based on `Fin d`. -/
noncomputable def basis {d} : OrthonormalBasis (Fin d) ℝ (Space d) where
  repr := {
    toFun := fun p i => p i
    invFun := fun v => ⟨v⟩
    left_inv := by
      intro p
      rfl
    right_inv := by
      intro v
      rfl
    map_add' := by
      intro v1 v2
      rfl
    map_smul' := by
      intro c v
      rfl
    norm_map' := by
      intro x
      simp [norm_eq, PiLp.norm_eq_of_L2]  }

lemma basis_eq_single {d} (i : Fin d) :
    basis i = ⟨EuclideanSpace.single i 1⟩ := by
  ext j
  simp [basis]
  change (EuclideanSpace.single i 1) j = _
  simp

lemma basis_apply {d} (i j : Fin d) :
    basis i j = if i = j then 1 else 0 := by
  simp [basis_eq_single]
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

@[simp]
lemma basis_self {d} (i : Fin d) : basis i i = 1 := by
  simp [basis_apply]

@[simp]
lemma basis_repr {d} (p : Space d) : basis.repr p = p.val := by rfl

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
  (fun x => fderiv ℝ f x (basis μ))

@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by
  rfl

lemma deriv_eq_fderiv_basis [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by
  rw [deriv_eq]

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
  let fi i x := f x i
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
  let fi i x := f x i
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
  let fi i x := f x i
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
  unit := (‖x‖⁻¹) • x.val
  norm := by
    simp [norm_smul]
    rw [@PiLp.norm_eq_of_L2]
    simp
    rw [← norm_eq]
    field_simp [h]


/-!

## One equiv

-/

/-- The linear isometric equivalence between `Space 1` and `ℝ`. -/
noncomputable def oneEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun x := ⟨fun _ => x⟩
  left_inv x := by ext i; fin_cases i; simp
  right_inv x := by simp
  map_add' x y := by rfl
  map_smul' c x := by rfl
  norm_map' x := by
    simp only [Fin.isValue, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    rw [@norm_eq]
    simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    exact Eq.symm (Real.sqrt_sq_eq_abs (x 0))

lemma oneEquiv_coe :
    (oneEquiv : Space 1 → ℝ) = fun x => x 0 := by
  rfl

lemma oneEquiv_symm_coe :
    (oneEquiv.symm : ℝ → Space 1) = fun x => fun _ => x := by
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
    rw [ContinuousLinearEquiv.image_eq_preimage]
    exact oneEquiv.symm.continuous.measurable hs

lemma oneEquiv_symm_measurableEmbedding : MeasurableEmbedding oneEquiv.symm where
  injective := oneEquiv.symm.injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑oneEquivCLE.symm '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage]
    exact oneEquiv.continuous.measurable hs

lemma oneEquiv_measurePreserving : MeasurePreserving oneEquiv volume volume :=
  LinearIsometryEquiv.measurePreserving oneEquiv

lemma oneEquiv_symm_measurePreserving : MeasurePreserving oneEquiv.symm volume volume := by
  exact LinearIsometryEquiv.measurePreserving oneEquiv.symm

end Space
