/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.TODO.Basic
/-!

# Temperature

In this module we define the type `Temperature`, corresponding to the temperature in a given
(but arbitrary) set of units which have absolute zero at zero.

This is the version of temperature most often used in undergraduate and
non-mathematical physics.

The choice of units can be made on a case-by-case basis, as long as they are done consistently.

-/
open NNReal

/-- The type `Temperature` represents the temperature in a given (but arbitary) set of units
  (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals. -/
structure Temperature where
  /-- The nonnegative real value of the temperature. -/
  val : ℝ≥0

namespace Temperature
open Constants

/-- Coercion to `ℝ≥0`. -/
instance : Coe Temperature ℝ≥0 := ⟨fun T => T.val⟩

/-- The underlying real-number associated with the temperature. -/
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Coercion to `ℝ`. -/
noncomputable instance : Coe Temperature ℝ := ⟨toReal⟩

/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance : TopologicalSpace Temperature :=
  TopologicalSpace.induced (fun T : Temperature => (T.val : ℝ≥0)) inferInstance

instance : Zero Temperature := ⟨⟨0⟩⟩

@[ext] lemma ext {T₁ T₂ : Temperature} (h : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁; cases T₂; cases h; rfl

/-- The inverse temperature defined as `1/(kB * T)` in a given, but arbitary set of units.
  This has dimensions equivalent to `Energy`. -/
noncomputable def β (T : Temperature) : ℝ≥0 :=
  ⟨1 / (kB * (T : ℝ)), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · simp [toReal]⟩

/-- The temperature associated with a given inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ≥0) : Temperature :=
  ⟨⟨1 / (kB * β), by
      apply div_nonneg
      · exact zero_le_one
      · apply mul_nonneg
        · exact kB_nonneg
        · exact β.2⟩⟩

lemma ofβ_eq : ofβ = fun β => ⟨⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · exact β.2⟩⟩ := by
  rfl

@[simp]
lemma β_ofβ (β' : ℝ≥0) : β (ofβ β') = β' := by
  ext
  simp [β, ofβ, toReal]
  field_simp [kB_neq_zero]

@[simp]
lemma ofβ_β (T : Temperature) : ofβ (β T) = T := by
  ext
  change ((1 : ℝ) / (kB * ((β T : ℝ)))) = (T : ℝ)
  have : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := rfl
  simpa [this] using
    show (1 / (kB * (1 / (kB * (T : ℝ))))) = (T : ℝ) from by
      field_simp [kB_neq_zero]

/-- Positivity of `β` from positivity of temperature. -/
lemma beta_pos (T : Temperature) (hT_pos : 0 < T.val) : 0 < (T.β : ℝ) := by
  unfold Temperature.β
  have h_prod : 0 < (kB : ℝ) * T.val := mul_pos kB_pos hT_pos
  simpa [Temperature.β] using inv_pos.mpr h_prod

/-! ### Regularity of `ofβ` -/

open Filter Topology

lemma ofβ_continuousOn : ContinuousOn (ofβ : ℝ≥0 → Temperature) (Set.Ioi 0) := by
  rw [ofβ_eq]
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  have h1 : ContinuousAt (fun t : ℝ => 1 / (kB * t)) x.1 := by
    refine ContinuousAt.div₀ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · simp
      constructor
      · exact kB_neq_zero
      · exact ne_of_gt hx
  have hℝ : ContinuousAt (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) x :=
    h1.comp (continuous_subtype_val.continuousAt)
  have hNN :
      ContinuousAt (fun b : ℝ≥0 =>
          (⟨(1 : ℝ) / (kB * (b : ℝ)),
            by
              have hb : 0 ≤ kB * (b : ℝ) :=
                mul_nonneg kB_nonneg (by exact_mod_cast (show 0 ≤ b from b.2))
              exact div_nonneg zero_le_one hb⟩ : ℝ≥0)) x :=
    hℝ.codRestrict (fun b => by
      have hb : 0 ≤ kB * (b : ℝ) :=
        mul_nonneg kB_nonneg (by exact_mod_cast (show 0 ≤ b from b.2))
      exact div_nonneg zero_le_one hb)
  have hind : Topology.IsInducing (fun T : Temperature => (T.val : ℝ≥0)) := ⟨rfl⟩
  have : Tendsto (fun b : ℝ≥0 => ofβ b) (𝓝 x) (𝓝 (ofβ x)) := by
    simp [hind.nhds_eq_comap, ofβ_eq]
    simp_all only [Set.mem_Ioi, one_div, mul_inv_rev, val_eq_coe]
    exact hNN
  exact this

lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (x : ℝ) => ((ofβ (Real.toNNReal x)).val : ℝ)) (Set.Ioi 0) := by
  refine DifferentiableOn.congr (f := fun x => 1 / (kB * x)) ?_ ?_
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (by simpa using hx)
      simp [mul_eq_zero, kB_neq_zero, hx0]
  · intro x hx
    simp at hx
    have hx' : 0 < x := by simpa using hx
    simp [ofβ_eq, hx'.le, Real.toNNReal, NNReal.coe_mk]

/-! ### Convergence -/

open Filter Topology

/-- Eventually, `ofβ β` is positive as β → ∞`. -/
lemma eventually_pos_ofβ : ∀ᶠ b : ℝ≥0 in atTop, ((Temperature.ofβ b : Temperature) : ℝ) > 0 := by
  have hge : ∀ᶠ b : ℝ≥0 in atTop, (1 : ℝ≥0) ≤ b := Filter.eventually_ge_atTop 1
  refine hge.mono ?_
  intro b hb
  have hbpos : 0 < (b : ℝ) := (zero_lt_one.trans_le hb)
  have hden : 0 < kB * (b : ℝ) := mul_pos kB_pos hbpos
  have : 0 < (1 : ℝ) / (kB * (b : ℝ)) := one_div_pos.mpr hden
  simpa [Temperature.ofβ, one_div, Temperature.toReal] using this

/-- General helper: for any `a > 0`, we have `1 / (a * b) → 0` as `b → ∞` in `ℝ≥0`. -/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hεpos : 0 < ε := hε
  let Breal : ℝ := (1 / (a * ε)) + 1
  have hBpos : 0 < Breal := by
    have : 0 < (1 / (a * ε)) := by
      have : 0 < a * ε := mul_pos ha hεpos
      exact one_div_pos.mpr this
    linarith
  let B : ℝ≥0 := ⟨Breal, le_of_lt hBpos⟩
  have h_ev : ∀ᶠ b : ℝ≥0 in atTop, b ≥ B := Filter.eventually_ge_atTop B
  refine h_ev.mono ?_
  intro b hb
  have hBposR : 0 < (B : ℝ) := hBpos
  have hbposR : 0 < (b : ℝ) := by
    have hBB : (B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    exact lt_of_lt_of_le hBposR hBB
  have hb0 : 0 < (a * (b : ℝ)) := mul_pos ha hbposR
  have hB0 : 0 < (a * (B : ℝ)) := mul_pos ha hBposR
  have hmono : (1 : ℝ) / (a * (b : ℝ)) ≤ (1 : ℝ) / (a * (B : ℝ)) := by
    have hBB : (B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hden_le : (a * (B : ℝ)) ≤ (a * (b : ℝ)) :=
      mul_le_mul_of_nonneg_left hBB (le_of_lt ha)
    simpa [one_div] using one_div_le_one_div_of_le hB0 hden_le
  have hB_gt_base : (1 / (a * ε)) < (B : ℝ) := by
    simp [B, Breal]
  have hden_gt : (1 / ε) < (a * (B : ℝ)) := by
    have h' := mul_lt_mul_of_pos_left hB_gt_base ha
    have hane : a ≠ 0 := ne_of_gt ha
    have hx' : a * (ε⁻¹ * a⁻¹) = (1 / ε) := by
      have : a * (ε⁻¹ * a⁻¹) = ε⁻¹ := by
        simp [mul_comm, hane]
      simpa [one_div] using this
    simpa [hx'] using h'
  have hpos : 0 < (1 / ε) := by simpa [one_div] using inv_pos.mpr hεpos
  have hBbound : (1 : ℝ) / (a * (B : ℝ)) < ε := by
    have := one_div_lt_one_div_of_lt hpos hden_gt
    simpa [one_div, inv_div] using this
  set A : ℝ := (1 : ℝ) / (a * (b : ℝ)) with hA
  have hA_nonneg : 0 ≤ A := by
    have : 0 ≤ a * (b : ℝ) :=
      mul_nonneg (le_of_lt ha) (by exact_mod_cast (show 0 ≤ b from b.2))
    simpa [hA] using div_nonneg zero_le_one this
  have hxlt : A < ε := by
    have := lt_of_le_of_lt hmono hBbound
    simpa [hA] using this
  have hAbs : |A| < ε := by
    simpa [abs_of_nonneg hA_nonneg] using hxlt
  have hAbs' : |A - 0| < ε := by simpa [sub_zero] using hAbs
  have hdist : dist A 0 < ε := by simpa [Real.dist_eq] using hAbs'
  simpa [Real.dist_eq, hA, one_div, mul_comm, mul_left_comm, mul_assoc] using hdist

/-- Core convergence: as β → ∞, `toReal (ofβ β) → 0` in `ℝ`. -/
lemma tendsto_toReal_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hform :
      (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
        = (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) := by
    funext b; simp [Temperature.ofβ, Temperature.toReal]
  have hsrc :
      Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_inv_mul_atTop kB kB_pos
  simpa [hform] using hsrc

/-- As β → ∞, T = ofβ β → 0+ in ℝ (within Ioi 0). -/
lemma tendsto_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have h_to0 := tendsto_toReal_ofβ_atTop
  have h_into :
      Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_principal.2 (by simpa using Temperature.eventually_pos_ofβ)
  have : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop ((nhds (0 : ℝ)) ⊓ 𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_inf.2 ⟨h_to0, h_into⟩
  simpa [nhdsWithin] using this

end Temperature
