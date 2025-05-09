/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Bilinear Form Utilities

This file contains general lemmas and definitions related to bilinear forms,
particularly in the context of finite-dimensional normed spaces.
-/

namespace BilinearForm

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Given a bilinear map `B` and a linear map `A`, constructs the pullback of `B` by `A`,
which is the bilinear map `(v, w) ↦ B (A v) (A w)`. -/
abbrev pullback {F₁ F₂ R : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (B : F₂ →L[ℝ] F₂ →L[ℝ] R) (A : F₁ →L[ℝ] F₂) : F₁ →L[ℝ] F₁ →L[ℝ] R :=
  ContinuousLinearMap.bilinearComp B A A

/-- For a finite-dimensional space E with basis b, constructs elementary bilinear forms e_ij
    such that e_ij(v, w) = (b.coord i)(v) * (b.coord j)(w). -/
lemma elementary_bilinear_forms_def [FiniteDimensional ℝ E]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∃ (e : (Fin (Module.finrank ℝ E)) → (Fin (Module.finrank ℝ E)) → (E →L[ℝ] E →L[ℝ] ℝ)),
    ∀ (i j : Fin (Module.finrank ℝ E)) (v w : E),
    e i j v w = (b.coord i) v * (b.coord j) w := by
  let n := Module.finrank ℝ E
  let idx := Fin n
  let b_dual (i : idx) := b.coord i
  let e (i j : idx) : E →L[ℝ] E →L[ℝ] ℝ :=
    let fi : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b_dual i)
    let fj : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b_dual j)
    let mul_map : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
    ContinuousLinearMap.bilinearComp mul_map fi fj
  have h_prop : ∀ (i j : idx) (v w : E), e i j v w = (b.coord i) v * (b.coord j) w := by
    intro i j v w
    simp only [Basis.coord_apply]
    rfl
  exact ⟨e, h_prop⟩

/-- Every vector in a finite-dimensional space can be written as a sum
    of basis vectors with coordinates given by the dual basis. -/
lemma vector_basis_expansion
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (v : E) :
    v = ∑ i ∈ Finset.univ, (b.coord i) v • b i := by
  rw [← b.sum_repr v]
  congr
  ext i
  simp only [b.coord_apply, Finsupp.single_apply]
  rw [@Basis.repr_sum_self]

lemma sum_smul_left (L : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → E) (w : E) :
    L (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i • L (v i) w := by
  simp_rw [map_sum, ContinuousLinearMap.map_smul]
  exact ContinuousLinearMap.sum_apply s (fun d => c d • L (v d)) w

lemma sum_mul_left (L : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → E) (w : E) :
    L (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * L (v i) w := by
  rw [sum_smul_left L s c v w]
  simp_rw [smul_eq_mul]

lemma sum_smul_right (L : E →L[ℝ] E →L[ℝ] ℝ) (v : E) {ι : Type*}
    (t : Finset ι) (d : ι → ℝ) (w : ι → E) :
    L v (∑ j ∈ t, d j • w j) = ∑ j ∈ t, d j • L v (w j) := by
  simp_rw [map_sum, ContinuousLinearMap.map_smul]

lemma sum_mul_right (L : E →L[ℝ] E →L[ℝ] ℝ) (v : E) {ι : Type*}
    (t : Finset ι) (d : ι → ℝ) (w : ι → E) :
    L v (∑ j ∈ t, d j • w j) = ∑ j ∈ t, d j * L v (w j) := by
  rw [sum_smul_right L v t d w]
  simp_rw [smul_eq_mul]

lemma sum_smul_left_right (L : E →L[ℝ] E →L[ℝ] ℝ) {ι₁ ι₂ : Type*}
    (s : Finset ι₁) (t : Finset ι₂)
    (c : ι₁ → ℝ) (v : ι₁ → E) (d : ι₂ → ℝ) (w : ι₂ → E) :
    L (∑ i ∈ s, c i • v i) (∑ j ∈ t, d j • w j) =
      ∑ i ∈ s, ∑ j ∈ t, c i • d j • L (v i) (w j) := by
  simp_rw [sum_smul_left, sum_smul_right, Finset.smul_sum]

lemma sum_mul_left_right (L : E →L[ℝ] E →L[ℝ] ℝ) {ι₁ ι₂ : Type*}
    (s : Finset ι₁) (t : Finset ι₂)
    (c : ι₁ → ℝ) (v : ι₁ → E) (d : ι₂ → ℝ) (w : ι₂ → E) :
    L (∑ i ∈ s, c i • v i) (∑ j ∈ t, d j • w j) =
      ∑ i ∈ s, ∑ j ∈ t, c i * d j * L (v i) (w j) := by
  rw [sum_smul_left_right L s t c v d w]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [smul_eq_mul, mul_assoc]

lemma on_basis_expansions
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    L v w = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
      (b.coord i v) * (b.coord j w) * L (b i) (b j) := by
  rw [vector_basis_expansion b v, vector_basis_expansion b w]
  rw [sum_mul_left_right L Finset.univ Finset.univ
    (fun i => b.coord i v) b (fun j => b.coord j w) b]
  simp only [←vector_basis_expansion b v, ←vector_basis_expansion b w]

/-- The sum of elementary bilinear forms weighted by coefficients,
    when applied to vectors, equals a weighted sum of the products of
    coordinate functions. -/
lemma elementary_bilinear_forms_sum_apply
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e : (Fin (Module.finrank ℝ E)) → (Fin (Module.finrank ℝ E)) → (E →L[ℝ] E →L[ℝ] ℝ))
    (h_e : ∀ i j v w, e i j v w = (b.coord i) v * (b.coord j) w)
    (c : (Fin (Module.finrank ℝ E)) → (Fin (Module.finrank ℝ E)) → ℝ)
    (v w : E) :
    ((∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, c i j • e i j) v) w =
    ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, c i j * ((b.coord i) v * (b.coord j) w) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr
  exact h_e i j v w

/-- A simple algebraic identity for rearranging terms in double sums with multiple scalars. -/
lemma Finset.rearrange_double_sum_coefficients {α β R : Type*} [CommSemiring R]
    {s : Finset α} {t : Finset β} {f : α → β → R} {g : α → β → R} {h : α → β → R} :
    (∑ i ∈ s, ∑ j ∈ t, f i j * g i j * h i j) =
    (∑ i ∈ s, ∑ j ∈ t, h i j * (f i j * g i j)) := by
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Any bilinear form can be decomposed as a sum of elementary bilinear forms
    weighted by the form's values on basis elements. -/
theorem decomposition [FiniteDimensional ℝ E] (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∀ (L : E →L[ℝ] E →L[ℝ] ℝ),
    ∃ (e : (Fin (Module.finrank ℝ E)) → (Fin (Module.finrank ℝ E)) → (E →L[ℝ] E →L[ℝ] ℝ)),
    (∀ i j v w, e i j v w = (b.coord i) v * (b.coord j) w) ∧
    L = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, L (b i) (b j) • e i j := by
  intro L
  obtain ⟨e, h_e⟩ := elementary_bilinear_forms_def b
  have h_decomp : L = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, L (b i) (b j) • e i j := by
    ext v w
    have expansion := on_basis_expansions b L v w
    have right_side := elementary_bilinear_forms_sum_apply b e h_e (λ i j => L (b i) (b j)) v w
    rw [expansion, Finset.rearrange_double_sum_coefficients]
    exact right_side.symm
  exact ⟨e, ⟨h_e, h_decomp⟩⟩

/-- Given two vectors `v` and `w`, `eval_vectors_continuousLinear v w` is the continuous linear map
that evaluates a bilinear form `B` at `(v, w)`. -/
def eval_vectors_continuousLinear (v w : E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  { toFun := fun B => B v w,
    map_add' := fun f g => by simp [ContinuousLinearMap.add_apply],
    map_smul' := fun c f => by simp [ContinuousLinearMap.smul_apply] }

namespace ContinuousLinearMap

lemma map_sum_clm {R S M M₂ : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂]
    {σ : R →+* S} [Module R M] [Module S M₂] (f : M →ₛₗ[σ] M₂) {ι : Type*} (t : Finset ι)
    (g : ι → M) : f (∑ i ∈ t, g i) = ∑ i ∈ t, f (g i) :=
  _root_.map_sum f g t

lemma map_finset_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) {ι : Type*} (s : Finset ι) (g : ι → E) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  _root_.map_sum f g s

end ContinuousLinearMap
