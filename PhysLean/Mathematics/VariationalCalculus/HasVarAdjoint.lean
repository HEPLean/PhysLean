/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.InnerProductSpace.ProdL2

import PhysLean.ClassicalMechanics.Space.Basic
import PhysLean.Mathematics.VariationalCalculus.Basic
/-!
# Variational adjoint

Definition of adjoint of linear function between function spaces. It is inspired by the definition
of distributional adjoint of linear maps between test functions as described here:
https://en.wikipedia.org/wiki/Distribution_(mathematics) under 'Preliminaries: Transpose of a linear
operator' but we require that the adjoint is function between test functions too.

The key results are:
  - variational adjoint is unique on test functions
  - variational adjoint of identity is identity, `HasVarAdjoint.id`
  - variational adjoint of composition is composition of adjoint in reverse order,
    `HasVarAdjoint.comp`
  - variational adjoint of deriv is `- deriv`, `HasVarAdjoint.deriv`
  - variational adjoint of algebraic operations is algebraic operation of adjoints,
    `HasVarAdjoint.neg`, `HasVarAdjoint.add`, `HasVarAdjoint.sub`, `HasVarAdjoint.mul_left`,
    `HasVarAdjoint.mul_right`, `HasVarAdjoint.smul_left`, `HasVarAdjoint.smul_right`
-/

open InnerProductSpace MeasureTheory ContDiff

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {U} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {V} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {W} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Map `F` from `(X → U)` to `(X → V)` has a variational adjoint `F'` if it preserves
test functions and satisfies the adjoint relation `⟪F φ, ψ⟫ = ⟪φ, F' ψ⟫`for all test functions
`φ` and `ψ` for `⟪φ, ψ⟫ = ∫ x, ⟪φ x, ψ x⟫_ℝ ∂μ`.

The canonical example is the function `F = deriv` that has adjoint `F' = - deriv`.

This notion of adjoint allows us to do formally variational calculus as often encountered in physics
textbooks. In mathematical literature, the adjoint is often defined for unbounded operators, but
such formal treatement is unnecessarily complicated for physics applications.
-/
structure HasVarAdjoint
    (F : (X → U) → (X → V)) (F' : (X → V) → (X → U)) (μ : Measure X := by volume_tac) where
  test_fun_preserving : ∀ φ, IsTestFunction φ → IsTestFunction (F φ)
  test_fun_preserving' : ∀ φ, IsTestFunction φ → IsTestFunction (F' φ)
  adjoint : ∀ φ ψ, IsTestFunction φ → IsTestFunction ψ →
    ∫ x, ⟪F φ x, ψ x⟫_ℝ ∂μ = ∫ x, ⟪φ x, F' ψ x⟫_ℝ ∂μ
  ext : ∀ (K : Set X) (_ : IsCompact K), ∃ L : Set X,
    IsCompact L ∧ K ⊆ L ∧ ∀ (φ φ' : X → V), (∀ x ∈ L, φ x = φ' x) → ∀ x ∈ K, F' φ x = F' φ' x

namespace HasVarAdjoint

variable {μ : Measure X}

lemma id : HasVarAdjoint (fun φ : X → U => φ) (fun φ => φ) μ where
  test_fun_preserving _ hφ := hφ
  test_fun_preserving' _ hφ := hφ
  adjoint _ _ _ _ := rfl
  ext := fun K cK => ⟨K,cK,subset_refl _,fun _ _ h => h⟩

lemma zero : HasVarAdjoint (fun (_ : X → U) _ => (0 : V)) (fun _ _ => 0) μ where
  test_fun_preserving _ hφ := by fun_prop
  test_fun_preserving' _ hφ := by fun_prop
  adjoint _ _ _ _ := by simp
  ext := fun K cK => ⟨K,cK,subset_refl _,fun _ _ h _ _ => rfl⟩

lemma comp {F : (X → V) → (X → W)} {G : (X → U) → (X → V)} {F' G'}
    (hF : HasVarAdjoint F F' μ) (hG : HasVarAdjoint G G' μ) :
    HasVarAdjoint (fun φ => F (G φ)) (fun φ => G' (F' φ)) μ where
  test_fun_preserving _ hφ := hF.test_fun_preserving _ (hG.test_fun_preserving _ hφ)
  test_fun_preserving' _ hφ := hG.test_fun_preserving' _ (hF.test_fun_preserving' _ hφ)
  adjoint φ ψ hφ hψ := by
    rw [hF.adjoint _ _ (hG.test_fun_preserving φ hφ) hψ]
    rw [hG.adjoint _ _ hφ (hF.test_fun_preserving' _ hψ)]
  ext := by
    intro K cK
    obtain ⟨K', cK', sK', h'⟩ := hG.ext K cK
    obtain ⟨K'', cK'', sK'', h''⟩ := hF.ext K' cK'
    use K''
    constructor
    · exact cK''
    constructor
    · exact sK'.trans sK''
    · intro φ φ' hφ
      apply h' _ _ (fun _ hx' => h'' _ _ hφ _ hx')

protected lemma deriv :
    HasVarAdjoint (fun φ : ℝ → U => deriv φ) (fun φ x => - deriv φ x) where
  test_fun_preserving _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · fun_prop
    · exact HasCompactSupport.deriv h'
  test_fun_preserving' _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · fun_prop
    · apply HasCompactSupport.neg'
      apply HasCompactSupport.deriv h'
  adjoint φ ψ hφ hψ := by
    trans ∫ (x : ℝ), ⟪deriv φ x, ψ x⟫_ℝ
    · congr
    suffices ∫ (x : ℝ), deriv (fun x' => ⟪φ x', ψ x'⟫_ℝ) x = 0 by sorry
    rw[MeasureTheory.integral_of_hasDerivAt_of_tendsto (m:=0) (n:=0)
       (f:=(fun x' => ⟪φ x', ψ x'⟫_ℝ))]
    · simp
    · sorry
    · sorry
    · sorry
    · sorry
  ext := by
    intro K cK
    use (Metric.cthickening 1 K)
    constructor
    · exact IsCompact.cthickening cK
    constructor
    · exact Metric.self_subset_cthickening K
    · intro φ φ' hφ
      have h : ∀ x ∈ K, φ =ᶠ[nhds x] φ' := by
        intro x hx
        apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
        refine mem_interior_iff_mem_nhds.mp ?_
        rw [@mem_interior]
        use Metric.thickening 1 K
        simp only [subset_refl, true_and]
        apply And.intro
        · exact Metric.isOpen_thickening
        · rw [@Metric.mem_thickening_iff_exists_edist_lt]
          use x
          simpa using hx
        · intro x hx
          have hx' : x ∈ Metric.cthickening 1 K := Metric.thickening_subset_cthickening 1 K hx
          exact hφ x hx'
      intro x hx; congr 1
      apply (h x hx).deriv_eq

lemma congr_fun {F G : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {μ : Measure X}
    (h : HasVarAdjoint G F' μ) (h' : ∀ φ, IsTestFunction φ → F φ = G φ) :
    HasVarAdjoint F F' μ where
  test_fun_preserving φ hφ := by
    rw[h' _ hφ]
    exact h.test_fun_preserving φ hφ
  test_fun_preserving' φ hφ := h.test_fun_preserving' φ hφ
  adjoint φ ψ hφ hψ := by
    rw [h' φ hφ]
    exact h.adjoint φ ψ hφ hψ
  ext := h.ext

/-- Variational adjoint is unique only when applied to test functions. -/
lemma unique_on_test_functions {F : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace X] (hF' : HasVarAdjoint F F' μ) (hG' : HasVarAdjoint F G' μ) :
    ∀ φ, IsTestFunction φ → F' φ = G' φ := by
  obtain ⟨F_preserve_test, F'_preserve_test, F'_adjoint⟩ := hF'
  obtain ⟨F_preserve_test, G'_preserve_test, G'_adjoint⟩ := hG'
  intro φ hφ
  rw [← zero_add (G' φ)]
  rw [← sub_eq_iff_eq_add]
  change (F' - G') φ = 0
  apply fundamental_theorem_of_variational_calculus μ
  · simp
    apply IsTestFunction.sub
    · exact F'_preserve_test φ hφ
    · exact G'_preserve_test φ hφ
  · intro ψ hψ
    simp [inner_sub_left]
    rw [MeasureTheory.integral_sub]
    · conv_lhs =>
        enter [2, 2, a]
        rw [← inner_conj_symm]
      conv_lhs =>
        enter [1, 2, a]
        rw [← inner_conj_symm]
      simp[← F'_adjoint ψ φ hψ hφ,G'_adjoint ψ φ hψ hφ]
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · exact F'_preserve_test φ hφ
      · exact hψ
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · exact G'_preserve_test φ hφ
      · exact hψ

/-- Variational adjoint is unique only when applied to smooth functions. -/
lemma unique
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X]
    {F : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] [OpensMeasurableSpace X]
    (hF : HasVarAdjoint F F' μ) (hG : HasVarAdjoint F G' μ) :
    ∀ f, ContDiff ℝ ∞ f → F' f = G' f := by

  intro f hf; funext x

  obtain ⟨K, cK, sK, hK⟩ := hF.ext {x} (isCompact_singleton)
  obtain ⟨L, cL, sL, hL⟩ := hG.ext {x} (isCompact_singleton)
  -- have hK : x ∈ {x} K := by
  -- exact? Set.mem_singleton x
  have hnonempty : Set.Nonempty (K ∪ L) := by
    apply Set.Nonempty.inl
    use x; simp_all only [Set.singleton_subset_iff, Set.mem_singleton_iff, forall_eq]

  -- prepare test function that is one on `D ∪ D'`
  let r := sSup ((fun x => ‖x‖) '' (K ∪ L))
  have : 0 ≤ r := by
    obtain ⟨x, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := K ∪ L)
      (IsCompact.union cK cL) hnonempty
      (f := fun x => ‖x‖) (by fun_prop)
    unfold r
    apply le_of_le_of_eq (b := ‖x‖)
    · exact norm_nonneg x
    · rw [← h2]

  let φ : ContDiffBump (0 : X) := {
    rIn := r + 1,
    rOut := r + 2,
    rIn_pos := by linarith,
    rIn_lt_rOut := by linarith}

  -- few properties about `φ`
  let φ' := fun x => φ.toFun x
  have hφ : IsTestFunction (fun x : X => φ x) := by
    constructor
    apply ContDiffBump.contDiff
    apply ContDiffBump.hasCompactSupport
  have hφ' : ∀ x, x ∈ K ∪ L → x ∈ Metric.closedBall 0 φ.rIn := by
    intro x hx
    simp [φ, r]
    obtain ⟨y, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := K ∪ L)
      (IsCompact.union cK cL) hnonempty
      (f := fun x => ‖x‖) (by fun_prop)
    rw [h2]
    have h3' := h3 x hx
    apply le_trans h3'
    simp

  let ψ := fun x => φ x • f x
  have hψ : IsTestFunction (fun x : X => ψ x) := by fun_prop
  have hψK : ∀ x ∈ K, f x = ψ x := by
    intros x hx; unfold ψ
    rw[ContDiffBump.one_of_mem_closedBall]
    · simp
    · apply hφ'; simp [hx]
  have hψL : ∀ x ∈ L, f x = ψ x := by
    intros x hx; unfold ψ
    rw[ContDiffBump.one_of_mem_closedBall]
    · simp
    · apply hφ'; simp [hx]

  simp only [hK f ψ hψK x rfl, hL f ψ hψL x rfl, unique_on_test_functions hF hG ψ hψ]

lemma neg {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)}
    {μ : Measure X}
    (hF : HasVarAdjoint F F' μ) :
    HasVarAdjoint (fun φ x => - F φ x) (fun φ x => - F' φ x) μ where
  test_fun_preserving _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · apply ContDiff.neg
      apply (hF.test_fun_preserving _ hφ).smooth
    · apply HasCompactSupport.neg'
      apply (hF.test_fun_preserving _ hφ).supp
  test_fun_preserving' _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · apply ContDiff.neg
      apply (hF.test_fun_preserving' _ hφ).smooth
    · apply HasCompactSupport.neg'
      apply (hF.test_fun_preserving' _ hφ).supp
  adjoint _ _ _ _ := by
    simp [integral_neg]
    rw[hF.adjoint _ _ (by assumption) (by assumption)]
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    exact ⟨L,cL,sL,by intro _ _ _ _ _; congr 1; apply h <;> simp_all⟩

lemma add {F G : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : HasVarAdjoint F F' μ) (hG : HasVarAdjoint G G' μ) :
    HasVarAdjoint (fun φ x => F φ x + G φ x) (fun φ x => F' φ x + G' φ x) μ where
  test_fun_preserving _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · apply ContDiff.add
      apply (hF.test_fun_preserving _ hφ).smooth
      apply (hG.test_fun_preserving _ hφ).smooth
    · apply HasCompactSupport.add
      apply (hF.test_fun_preserving _ hφ).supp
      apply (hG.test_fun_preserving _ hφ).supp
  test_fun_preserving' _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · apply ContDiff.add
      apply (hF.test_fun_preserving' _ hφ).smooth
      apply (hG.test_fun_preserving' _ hφ).smooth
    · apply HasCompactSupport.add
      apply (hF.test_fun_preserving' _ hφ).supp
      apply (hG.test_fun_preserving' _ hφ).supp
  adjoint _ _ _ _ := by
    simp[inner_add_left,inner_add_right]
    rw[MeasureTheory.integral_add]
    rw[MeasureTheory.integral_add]
    rw[hF.adjoint _ _ (by assumption) (by assumption)]
    rw[hG.adjoint _ _ (by assumption) (by assumption)]
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact h)
      · (expose_names; exact hF.test_fun_preserving' x_1 h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact h)
      · (expose_names; exact hG.test_fun_preserving' x_1 h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact hF.test_fun_preserving x h)
      · (expose_names; exact h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact hG.test_fun_preserving x h)
      · (expose_names; exact h_1)
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    obtain ⟨L',cL',sL',h'⟩ := hG.ext K cK
    use L ∪ L'
    constructor
    · exact cL.union cL'
    constructor
    · exact Set.subset_union_of_subset_left sL _
    · intro φ φ' hφ
      have hL : ∀ x ∈ L, φ x = φ' x := by
        intro x hx; apply hφ; simp_all
      have hL' : ∀ x ∈ L', φ x = φ' x := by
        intro x hx; apply hφ; simp_all
      simp +contextual (disch:=assumption) [h φ φ', h' φ φ']

lemma sub {F G : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : HasVarAdjoint F F' μ) (hG : HasVarAdjoint G G' μ) :
    HasVarAdjoint (fun φ x => F φ x - G φ x) (fun φ x => F' φ x - G' φ x) μ := by
  simp [sub_eq_add_neg]
  apply add hF (neg hG)

lemma mul_left {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ} {F' : (X → ℝ) → (X → ℝ)}
    {μ : Measure X}
    (hF : HasVarAdjoint F F' μ) (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x * F φ x) (fun φ x => F' (fun x => ψ x * φ x) x) μ where
  test_fun_preserving φ hφ := by
    apply IsTestFunction.mul_left
    · exact hψ
    · exact hF.test_fun_preserving φ hφ
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving'
    apply IsTestFunction.mul_left
    · exact hψ
    · exact hφ
  adjoint φ ψ' hφ hψ' := by
    rw [← hF.adjoint]
    · congr; funext x; simp; ring
    · exact hφ
    · apply IsTestFunction.mul_left
      · exact hψ
      · exact hψ'
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    exact ⟨L,cL,sL,by intro _ _ hφ _ _; apply h <;> simp_all⟩

lemma mul_right {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ} {F' : (X → ℝ) → (X → ℝ)}
    {μ : Measure X}
    (hF : HasVarAdjoint F F' μ) (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => F φ x * ψ x) (fun φ x => F' (fun x => φ x * ψ x) x) μ where
  test_fun_preserving φ hφ := by
    apply IsTestFunction.mul_right
    · exact hF.test_fun_preserving φ hφ
    · exact hψ
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving'
    apply IsTestFunction.mul_right
    · exact hφ
    · exact hψ
  adjoint φ ψ' hφ hψ' := by
    rw [← hF.adjoint]
    · congr; funext x; simp; ring
    · exact hφ
    · apply IsTestFunction.mul_right
      · exact hψ'
      · exact hψ
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    exact ⟨L,cL,sL,by intro _ _ hφ _ _; apply h <;> simp_all⟩

lemma smul_left {F : (X → U) → (X → V)} {ψ : X → ℝ} {F' : (X → V) → (X → U)}
    {μ : Measure X}
    (hF : HasVarAdjoint F F' μ) (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x • F φ x) (fun φ x => F' (fun x' => ψ x' • φ x') x) μ where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving φ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving' _ _
    fun_prop
  adjoint φ ψ hφ hψ := by
    simp_rw[inner_smul_left, ← inner_smul_right]
    rw [hF.adjoint]
    · rfl
    · exact hφ
    · simp; fun_prop
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    exact ⟨L,cL,sL,by intro _ _ hφ _ _; apply h <;> simp_all⟩

lemma smul_right {F : (X → U) → (X → V)} {ψ : X → ℝ} {F' : (X → V) → (X → U)}
    {μ : Measure X}
    (hF : HasVarAdjoint F F' μ) (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x • F φ x) (fun φ x => F' (fun x' => ψ x' • φ x') x) μ where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving φ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving' _ _
    fun_prop
  adjoint φ ψ hφ hψ := by
    simp_rw[inner_smul_left, ← inner_smul_right]
    rw [hF.adjoint]
    · rfl
    · exact hφ
    · simp; fun_prop
  ext := by
    intro K cK
    obtain ⟨L,cL,sL,h⟩ := hF.ext K cK
    exact ⟨L,cL,sL,by intro _ _ hφ _ _; apply h <;> simp_all⟩

lemma clm_apply [CompleteSpace U] [CompleteSpace V] {μ : Measure X} (f : X → (U →L[ℝ] V))
    (hf : ContDiff ℝ ∞ f) :
    HasVarAdjoint (fun (φ : X → U) x => f x (φ x)) (fun ψ x => (f x).adjoint (ψ x)) μ  where
  test_fun_preserving φ hφ := by
    constructor
    · fun_prop
    · sorry
  test_fun_preserving' φ hφ := by
    constructor
    · sorry
    · sorry
  adjoint φ ψ hφ hψ := by
    simp[ContinuousLinearMap.adjoint_inner_right]
  ext := by
   intro K cK
   exact ⟨K, cK, subset_refl _, by intro _ _ hφ _ _; simp_all⟩

lemma fderiv_apply {d} {dx} :
    HasVarAdjoint (fun φ : Space d → U => (fderiv ℝ φ · dx)) (fun φ x => - fderiv ℝ φ x dx) :=
  sorry

protected lemma gradient {d} :
    HasVarAdjoint (fun φ : Space d → ℝ => gradient φ) (fun φ x => - Space.div φ x) where
  test_fun_preserving φ hφ := by sorry
  test_fun_preserving' φ hφ := by sorry
  adjoint φ ψ hφ hψ := by
    simp [gradient,Space.div,Space.deriv,Space.coord]
    have := hψ.differentiable
    conv =>
      rhs;
      enter [2,x,1,1,2,i]
      rw[fderiv_sum (by fun_prop)]
      enter [1,2,j]
      rw[fderiv_const_mul (by fun_prop)]

    conv =>
      rhs;
      enter [2,x]
      rw[Finset.sum_mul]
      enter [1,2,i]
      rw[ContinuousLinearMap.sum_apply]
      rw[Finset.sum_mul]

    simp [integral_neg, integral_finset_sum _ (by sorry), mul_assoc, integral_const_mul]
    simp [Space.basis]

    have h : ∀ (i : Fin d),
      ∫ (x : Space d), (fderiv ℝ (ψ · i) x) (EuclideanSpace.single i 1) * φ x ∂volume
      =
      - ∫ (x : Space d), (ψ x i) * fderiv ℝ φ x (EuclideanSpace.single i 1) ∂volume := sorry

    simp [h]
    rw[← integral_finset_sum _ (by sorry)]
    simp only [← smul_eq_mul, ← map_smul, ← map_sum]
    congr; funext x; congr
    ext j
    rw[Finset.sum_apply]
    simp

  ext := by
    intro K cK
    use (Metric.cthickening 1 K)
    constructor
    · exact IsCompact.cthickening cK
    constructor
    · exact Metric.self_subset_cthickening K
    · intro φ φ' hφ
      have h : ∀ (i : Fin d), ∀ x ∈ K,
          (fun x => Space.coord i (φ x)) =ᶠ[nhds x] fun x => Space.coord i (φ' x) := by
        intro i x hx
        apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
        refine mem_interior_iff_mem_nhds.mp ?_
        rw [@mem_interior]
        use Metric.thickening 1 K
        simp only [subset_refl, true_and]
        apply And.intro
        · exact Metric.isOpen_thickening
        · rw [@Metric.mem_thickening_iff_exists_edist_lt]
          use x
          simpa using hx
        · intro x hx
          have hx' : x ∈ Metric.cthickening 1 K := Metric.thickening_subset_cthickening 1 K hx
          simp_all [hφ]
      intro x hx; congr 1
      simp [Space.div,Space.deriv]
      congr; funext i; congr 1
      exact Filter.EventuallyEq.fderiv_eq (h _ _ hx)

lemma div {d} :
    HasVarAdjoint
      (fun (φ : Space d → Space d) x => Space.div φ x)
      (fun ψ x => - gradient ψ x) := sorry

lemma prod {F : (X → U) → (X → V)} {G : (X → U) → (X → W)} {F' G'}
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : HasVarAdjoint F F' μ) (hG : HasVarAdjoint G G' μ) :
    HasVarAdjoint
      (fun φ x => (WithLp.equiv 2 _).symm (F φ x, G φ x))
      (fun φ x => F' (fun x' => (φ x').1) x + G' (fun x' => (φ x').2) x) μ := sorry

lemma fst {F : (X → U) → (X → WithLp 2 (W×V))}
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : HasVarAdjoint F F' μ) :
    HasVarAdjoint
      (fun φ x => (F φ x).1)
      (fun φ x => F' (fun x' => (WithLp.equiv 2 _).symm (φ x', 0)) x) μ := sorry

lemma snd {F : (X → U) → (X → WithLp 2 (W×V))}
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : HasVarAdjoint F F' μ) :
    HasVarAdjoint
      (fun φ x => (F φ x).2)
      (fun φ x => F' (fun x' => (WithLp.equiv 2 _).symm (0, φ x')) x) μ := sorry
