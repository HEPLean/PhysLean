/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Meta.TODO.Basic
/-!

# The infinite well submodule

The submodule of the Hilbert space spanned by functions
`ℝ → ℂ` which are continuous, supported in the interval `(a, b)`, and
are smooth in the interior of the interval.

This is the submodule on which the Hamiltonian operator of the infinite potential
wel is defined on as an unbounded operator.

The submodule itself is `infiniteWellSubmodule` which is equivalent
through `infiniteWellSubmoduleEquiv` to the submodule of functions
`ℝ → ℂ` which are continuous, supported in the interval `(a, b)`, and
are smooth in the interior of the interval, which is `infiniteWellFunSubmodule`.

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open HilbertSpace
open MeasureTheory

/-- The submodule of the Hilbert space of those wavefunctions which are
  continuous, supported on `(a, b)` and are smooth in the interior of this interval. -/
def infiniteWellSubmodule (a b : ℝ) : Submodule ℂ HilbertSpace where
  carrier ψ := ∃ ψ' : ℝ → ℂ,
    ψ =ᶠ[ae volume] ψ' ∧
    Continuous ψ' ∧
    Function.support ψ' ⊆ Set.Ioo a b
    ∧ ∀ x ∈ Set.Ioo a b, ContDiffAt ℝ ⊤ ψ' x
  zero_mem' := by
    use 0
    exact ⟨Lp.coeFn_zero ℂ 2 volume, continuous_zero,
      Function.support_subset_iff'.mpr fun x => congrFun rfl, fun x hx =>
        ContDiff.contDiffAt contDiff_zero_fun⟩
  add_mem' {ψ1 ψ2} h1 h2 := by
    obtain ⟨ψ1', h1ae, h1c, h1s, h1d⟩ := h1
    obtain ⟨ψ2', h2ae, h2c, h2s, h2d⟩ := h2
    use ψ1' + ψ2'
    refine ⟨(Lp.coeFn_add ψ1 ψ2).trans (h1ae.add h2ae),
      h1c.add h2c, ?_, fun x hx => (h1d x hx).add (h2d x hx)⟩
    intro x
    simp only [Function.mem_support, Pi.add_apply, ne_eq, Set.mem_Ioo]
    intro h
    by_cases h1 : ¬ ψ1' x = 0 <;> by_cases h2 : ¬ ψ2' x = 0
    · exact h1s h1
    · exact h1s h1
    · exact h2s h2
    · simp_all
  smul_mem' c ψ h := by
    obtain ⟨ψ', hae, hc, hs, hd⟩ := h
    use c • ψ'
    refine ⟨(Lp.coeFn_smul c ψ).trans (hae.const_smul c), hc.const_smul c, ?_,
      fun x hx => (hd x hx).const_smul c⟩
    intro x
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or,
      Set.mem_Ioo, and_imp]
    intro h
    simp at hs
    exact hs x

/-- The submodule of the `ℝ → ℂ` of those functions which are
  continuous, supported on `(a, b)` and are smooth in the interior of this interval. -/
def infiniteWellFunSubmodule (a b : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier ψ :=
    Continuous ψ ∧
    Function.support ψ ⊆ Set.Ioo a b
    ∧ ∀ x ∈ Set.Ioo a b, ContDiffAt ℝ ⊤ ψ x
  zero_mem' := by
    exact ⟨continuous_zero,
      Function.support_subset_iff'.mpr fun x => congrFun rfl, fun x hx =>
        ContDiff.contDiffAt contDiff_zero_fun⟩
  add_mem' {ψ1 ψ2} h1 h2 := by
    refine ⟨
      h1.1.add h2.1, ?_, fun x hx => (h1.2.2 x hx).add (h2.2.2 x hx)⟩
    intro x
    simp only [Function.mem_support, Pi.add_apply, ne_eq, Set.mem_Ioo]
    intro h
    have h1s := h1.2.1
    have h2s := h2.2.1
    by_cases h1 : ¬ ψ1 x = 0 <;> by_cases h2 : ¬ ψ2 x = 0
    · exact h1s h1
    · exact h1s h1
    · exact h2s h2
    · simp_all
  smul_mem' c ψ h := by
    refine ⟨h.1.const_smul c, ?_,
      fun x hx => (h.2.2 x hx).const_smul c⟩
    intro x
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or,
      Set.mem_Ioo, and_imp]
    intro hc
    have hs := h.2.1
    simp at hs
    exact hs x

lemma continuous_of_infiniteWellFunSubmodule {a b : ℝ} (ψ : infiniteWellFunSubmodule a b) :
    Continuous ψ.1 := ψ.2.1

lemma memHS_of_infiniteWellFunSubmodule {a b : ℝ} (ψ : infiniteWellFunSubmodule a b) :
    MemHS ψ := by
  rw [memHS_iff]
  refine ⟨?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_of_infiniteWellFunSubmodule ψ
  · rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset (s := Set.Icc a b)]
    · apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
      · apply ContinuousOn.locallyIntegrableOn
        · have h1 := continuous_of_infiniteWellFunSubmodule ψ
          fun_prop
        · exact measurableSet_Icc
      · exact isCompact_Icc
    · simp
      intro x hx
      have hs := ψ.2.2.1
      simp at hs
      exact ⟨le_of_lt (hs x hx).1, le_of_lt (hs x hx).2⟩

lemma sin_mem_infiniteWellFunSubmodule :
    (fun x => if x ∈ Set.Ioo (-1) 1 then Real.sin (Real.pi * x) else (0 : ℂ) : ℝ → ℂ)
    ∈ infiniteWellFunSubmodule (-1) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · refine continuous_if ?_ ?_ ?_
    · intro a ha
      have h1 : frontier (Set.Ioo (-1) (1 : ℝ)) = {-1, 1} := by
        rw [frontier_Ioo]
        simp
      erw [h1] at ha
      simp at ha
      rcases ha with rfl | rfl
      · simp
      · simp
    · fun_prop
    · fun_prop
  · simp
    intro x h1 h2 h
    simp_all
  · intro x hx
    apply ContDiffAt.congr_of_eventuallyEq (f := (fun x => Real.sin (Real.pi * x) : ℝ → ℂ))
    · refine ContDiffAt.fun_comp x ?_ ?_
      · apply ContDiff.contDiffAt
        change ContDiff ℝ ⊤ Complex.ofRealCLM
        fun_prop
      · apply ContDiff.contDiffAt
        apply ContDiff.sin
        fun_prop
    · rw [Filter.eventuallyEq_iff_exists_mem]
      use Set.Ioo (-1) 1
      constructor
      · simp at hx
        exact Ioo_mem_nhds hx.1 hx.2
      · intro x hx
        simp at hx
        simp_all

/-- The equivalence between the submodule of the Hilbert space and the submodule
  of functions `ℝ → ℂ` which are continuous, supported on `(a, b)` and are smooth within
  this interval. -/
def infiniteWellSubmoduleEquiv {a b : ℝ} :
    infiniteWellSubmodule a b ≃ₗ[ℂ] infiniteWellFunSubmodule a b where
  toFun ψ := ⟨Classical.choose ψ.2,
    have hs := Classical.choose_spec ψ.2
    ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩⟩
  invFun ψ := ⟨HilbertSpace.mk (memHS_of_infiniteWellFunSubmodule ψ),
    ⟨ψ, ⟨coe_mk_ae (memHS_of_infiniteWellFunSubmodule ψ), ψ.2.1, ψ.2.2.1, ψ.2.2.2⟩⟩⟩
  left_inv ψ := by
    simp only [Function.support_subset_iff, ne_eq, Set.mem_Ioo, and_imp]
    ext1
    simp only
    apply ext_iff.mpr
    apply (coe_mk_ae _).trans
    simpa using (Classical.choose_spec ψ.2).1.symm
  right_inv ψ := by
    let ψ' : infiniteWellSubmodule a b := ⟨HilbertSpace.mk (memHS_of_infiniteWellFunSubmodule ψ),
      ⟨ψ, ⟨coe_mk_ae (memHS_of_infiniteWellFunSubmodule ψ), ψ.2.1, ψ.2.2.1, ψ.2.2.2⟩⟩⟩
    simp only [Function.support_subset_iff, ne_eq, Set.mem_Ioo]
    ext1
    simp only
    rw [← Continuous.ae_eq_iff_eq (μ := MeasureTheory.volume)]
    · trans (HilbertSpace.mk (memHS_of_infiniteWellFunSubmodule ψ) : ℝ → ℂ)
      · simpa using (Classical.choose_spec ψ'.2).1.symm
      · exact (coe_mk_ae _)
    · change Continuous (Classical.choose ψ'.2)
      exact (Classical.choose_spec ψ'.2).2.1
    · exact ψ.2.1
  map_add' ψ1 ψ2 := by
    ext1
    simp only [Submodule.coe_add, AddSubgroup.coe_add, Function.support_subset_iff, ne_eq,
      Set.mem_Ioo, AddMemClass.mk_add_mk]
    rw [← Continuous.ae_eq_iff_eq (μ := MeasureTheory.volume)]
    · exact (Classical.choose_spec (ψ1 + ψ2).2).1.symm.trans <|
        (MeasureTheory.AEEqFun.coeFn_add _ _).trans <|
        (Classical.choose_spec ψ1.2).1.add (Classical.choose_spec ψ2.2).1
    · exact (Classical.choose_spec (ψ1 + ψ2).2).2.1
    · exact (Classical.choose_spec ψ1.2).2.1.add (Classical.choose_spec ψ2.2).2.1
  map_smul' a ψ := by
    ext1
    rw [← Continuous.ae_eq_iff_eq (μ := MeasureTheory.volume)]
    · exact (Classical.choose_spec (a • ψ).2).1.symm.trans <|
        (MeasureTheory.AEEqFun.coeFn_smul _ _).trans <|
        (Classical.choose_spec ψ.2).1.const_smul a
    · exact (Classical.choose_spec (a • ψ).2).2.1
    · exact (Classical.choose_spec ψ.2).2.1.const_smul a

/-- The construction of an element of the submodule `infiniteWellSubmodule a b` of
  the hilbert space from a function `ℝ → ℂ` which is smooth and is zero at `a` and `b`. -/
def infiniteWellSubmoduleOfSmooth {a b : ℝ} (h : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ⊤ f) (hf0 : f a = 0) (hf1 : f b = 0) :
    infiniteWellSubmodule a b := infiniteWellSubmoduleEquiv.symm
  ⟨(fun x => if x ∈ Set.Ioo a b then f x else (0 : ℂ)), by
    refine ⟨?_, ?_, ?_⟩
    · refine continuous_if ?_ ?_ ?_
      · intro c hc
        have h1 : frontier (Set.Ioo a b) = {a, b} := by
          rw [frontier_Ioo]
          exact h
        erw [h1] at hc
        simp at hc
        rcases hc with rfl | rfl
        · exact hf0
        · exact hf1
      · have h1 := hf.continuous
        fun_prop
      · fun_prop
    · simp
      intro x h1 h2 h
      simp_all
    · intro x hx
      apply ContDiffAt.congr_of_eventuallyEq (f := f)
      · exact ContDiff.contDiffAt hf
      · rw [Filter.eventuallyEq_iff_exists_mem]
        use Set.Ioo a b
        constructor
        · simp at hx
          exact Ioo_mem_nhds hx.1 hx.2
        · intro x hx
          simp at hx
          simp_all⟩

TODO "GZYDF" "Define the momentum operator on the infinite well submodule of the Hilbert space
  in one-dimension."

end
end OneDimension
end QuantumMechanics
