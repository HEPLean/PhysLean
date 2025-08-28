/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.Thermodynamics.Temperature.Basic
import Mathlib

/-!

### Canonical Ensemble: Fluctuations and Heat Capacity
This file develops the theory of fluctuations in the canonical ensemble, focusing on the
energy variance and its relation to the heat capacity, establishing the Fluctuation-Dissipation 
Theorem.
-/

namespace CanonicalEnsemble
open MeasureTheory Real Temperature Constants
open scoped Temperature Topology Filter ENNReal Constants

variable {ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)

/-! ## Energy Variance and Fluctuations -/

/-- The mean square energy ⟨E²⟩ of the canonical ensemble at temperature T. -/
noncomputable def meanSquareEnergy (T : Temperature) : ℝ :=
∫ i, (𝓒.energy i)^2 ∂𝓒.μProd T

/-- The identity relating variance to the first two moments:
Var(E) = ⟨E²⟩ - ⟨E⟩². -/
theorem energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq
    (T : Temperature) [IsProbabilityMeasure (𝓒.μProd T)]
    (hE_int : Integrable 𝓒.energy (𝓒.μProd T))
    (hE2_int : Integrable (fun i => (𝓒.energy i)^2) (𝓒.μProd T)) :
    𝓒.energyVariance T = 𝓒.meanSquareEnergy T - (𝓒.meanEnergy T)^2 := by
  unfold energyVariance meanSquareEnergy meanEnergy
  set U := ∫ i, 𝓒.energy i ∂𝓒.μProd T
  have h_expand : (fun i => (𝓒.energy i - U)^2)
      = (fun i => (𝓒.energy i)^2 - 2 * U * 𝓒.energy i + U^2) := by
    funext i; ring
  rw [h_expand]
  have h_int_E_mul_const : Integrable (fun i => 2 * U * 𝓒.energy i) (𝓒.μProd T) :=
    hE_int.const_mul (2 * U)
  have h_int_const : Integrable (fun _ => U^2) (𝓒.μProd T) := integrable_const _
  erw [integral_add (hE2_int.sub h_int_E_mul_const) h_int_const]
  erw [integral_sub hE2_int h_int_E_mul_const]
  rw [integral_const_mul]
  rw [integral_const]
  have hμProb : (𝓒.μProd T) Set.univ = 1 := by simp
  have hμReal : (𝓒.μProd T).real Set.univ = 1 := by
    simp [measureReal_def, hμProb]
  calc
    ∫ i, (𝓒.energy i)^2 ∂𝓒.μProd T
        - 2 * U * ∫ i, 𝓒.energy i ∂𝓒.μProd T
        + (𝓒.μProd T).real Set.univ * U^2
        = ∫ i, (𝓒.energy i)^2 ∂𝓒.μProd T - 2 * U * U + (𝓒.μProd T).real Set.univ * U^2 := by
          simp [U]
    _ = ∫ i, (𝓒.energy i)^2 ∂𝓒.μProd T - 2 * U^2 + (𝓒.μProd T).real Set.univ * U^2 := by ring
    _ = ∫ i, (𝓒.energy i)^2 ∂𝓒.μProd T - U^2 := by
          simp [hμReal, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
                mul_left_comm, mul_assoc]
          ring_nf

/-! ## Heat Capacity and Derivatives -/

-- We define functions from ℝ to handle derivatives smoothly, using Real.toNNReal

/-- The mean energy as a function of the real-valued temperature t. -/
noncomputable def meanEnergy_T (t : ℝ) : ℝ := 𝓒.meanEnergy (Temperature.ofNNReal (Real.toNNReal t))

/-- The mean energy as a function of the real-valued inverse temperature b. -/
noncomputable def meanEnergy_Beta (b : ℝ) : ℝ := 𝓒.meanEnergy (Temperature.ofβ (Real.toNNReal b))

/-- The heat capacity (at constant volume) C_V is defined as C_V = ∂U/∂T.
We use derivWithin on the set of positive temperatures Set.Ioi 0.
-/
noncomputable def heatCapacity (T : Temperature) : ℝ :=
  derivWithin (𝓒.meanEnergy_T) (Set.Ioi 0) (T.val : ℝ)

/-- Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)). -/
lemma heatCapacity_eq_deriv_meanEnergy_beta
    (T : Temperature) (hT_pos : 0 < T.val)
    -- We require that U(β) is differentiable at T.β.
    (hU_deriv : HasDerivWithinAt (𝓒.meanEnergy_Beta)
    (derivWithin (𝓒.meanEnergy_Beta) (Set.Ioi 0) (T.β : ℝ))
    (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.heatCapacity T = (derivWithin (𝓒.meanEnergy_Beta) (Set.Ioi 0) (T.β : ℝ)) *
    (-1 / (kB * (T.val : ℝ)^2)) := by
  unfold heatCapacity meanEnergy_T
  have h_U_eq_comp : (𝓒.meanEnergy_T) = fun t : ℝ => (𝓒.meanEnergy_Beta) (Beta_fun_T t) := by
    funext t
    dsimp [meanEnergy_T, meanEnergy_Beta, Beta_fun_T]
    simp
  let dUdβ := derivWithin (𝓒.meanEnergy_Beta) (Set.Ioi 0) (T.β : ℝ)
  have h_chain := chain_rule_T_beta (F:=𝓒.meanEnergy_Beta) (F':=dUdβ) T hT_pos hU_deriv
  have h_UD :
    UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) (T.val : ℝ) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).uniqueDiffWithinAt hT_pos
  simp only [ofNNReal]
  rw [← (h_chain.derivWithin h_UD)]
  ring_nf
  simp_rw [← h_U_eq_comp]; rfl

/-! ### Fluctuation-Dissipation Theorem (Parametric) -/

-- The proof of Var(E) = -dU/dβ requires assumptions on differentiation under the integral.
-- We state the FDT parametrically based on this relationship.

/-- The Fluctuation-Dissipation Theorem for energy in the canonical ensemble.
C_V = Var(E) / (kB T²).
This connects the microscopic energy fluctuations (variance) to the macroscopic
response function (heat capacity).

This version assumes the relationship Var(E) = -dU/dβ holds.
-/
theorem fluctuation_dissipation_energy_parametric
    (T : Temperature) (hT_pos : 0 < T.val)
    (h_Var_eq_neg_dUdβ : 𝓒.energyVariance T = - derivWithin (𝓒.meanEnergy_Beta) 
    (Set.Ioi 0) (T.β : ℝ))
    (hU_deriv : DifferentiableWithinAt ℝ (𝓒.meanEnergy_Beta) (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * (T.val : ℝ)^2) := by
  let dUdβ := derivWithin (𝓒.meanEnergy_Beta) (Set.Ioi 0) (T.β : ℝ)
  have hCV_eq_dUdβ_mul :
      𝓒.heatCapacity T = dUdβ * (-1 / (kB * (T.val : ℝ)^2)) :=
    heatCapacity_eq_deriv_meanEnergy_beta 𝓒 T hT_pos hU_deriv.hasDerivWithinAt
  rw [hCV_eq_dUdβ_mul, h_Var_eq_neg_dUdβ]
  have hkB_ne_zero := kB_neq_zero
  field_simp [hkB_ne_zero, pow_ne_zero 2]
  ring

end CanonicalEnsemble

/-!

Finite canonical ensemble: Fluctuations and FDT
This file extends the theory of finite canonical ensembles by incorporating results on
fluctuations and proving the Fluctuation-Dissipation Theorem (FDT) for these systems.
-/

namespace CanonicalEnsemble

open Real Temperature MeasureTheory Constants
open scoped Temperature CanonicalEnsemble BigOperators

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
[MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)

/-! ## Fluctuations in Finite Systems -/

section FluctuationsFinite

variable [IsFinite 𝓒]
lemma meanSquareEnergy_of_fintype (T : Temperature) :
    𝓒.meanSquareEnergy T = ∑ i, (𝓒.energy i)^2 * 𝓒.probability T i := by
  simp [meanSquareEnergy]
  rw [MeasureTheory.integral_fintype]
  simp [μProd_of_fintype, mul_comm]
  exact Integrable.of_finite

variable [Nonempty ι]

lemma energyVariance_of_fintype (T : Temperature) :
    𝓒.energyVariance T = (∑ i, (𝓒.energy i)^2 * 𝓒.probability T i) - (𝓒.meanEnergy T)^2 := by
  have hE_int := Integrable.of_finite (f := 𝓒.energy) (μ := 𝓒.μProd T)
  have hE2_int := Integrable.of_finite (f := fun i => (𝓒.energy i)^2) (μ := 𝓒.μProd T)
  rw [energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq 𝓒 T hE_int hE2_int]
  rw [meanSquareEnergy_of_fintype]

/-! ## Rigorous FDT for Finite Systems -/

-- We define analytical helper functions parameterized by β ∈ ℝ.

/-- Mathematical partition function as a function of real inverse temperature b. -/
noncomputable def mathematicalPartitionFunctionBetaReal (b : ℝ) : ℝ :=
  ∑ i, exp (-b * 𝓒.energy i)

omit [MeasurableSingletonClass ι] [𝓒.IsFinite] in
lemma mathematicalPartitionFunctionBetaReal_pos (b : ℝ) :
    0 < 𝓒.mathematicalPartitionFunctionBetaReal b := by
  apply Finset.sum_pos
  · intro i _; exact exp_pos _
  · exact Finset.univ_nonempty

/-- Probability as a function of real inverse temperature b. -/
noncomputable def probabilityBetaReal (b : ℝ) (i : ι) : ℝ :=
  exp (-b * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal b

/-- Mean energy as a function of real inverse temperature b for finite systems.
This definition is differentiable everywhere on ℝ. -/
noncomputable def meanEnergyBetaReal' (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i

omit [Nonempty ι] in
/-- The robust definition meanEnergy_Beta coincides with the differentiable definition
meanEnergyBetaReal' on the physical domain b > 0. -/
lemma meanEnergy_Beta_eq_finite (b : ℝ) (hb : 0 < b) :
    𝓒.meanEnergy_Beta b = 𝓒.meanEnergyBetaReal' b := by
  let T := ofβ (Real.toNNReal b)
  have hT_beta_nn : T.β = Real.toNNReal b := by
    simp [T]
  have hT_beta : (T.β : ℝ) = b := by
    simp [hT_beta_nn, Real.toNNReal_of_nonneg hb.le]
  rw [meanEnergy_Beta, meanEnergy_of_fintype 𝓒 T, meanEnergyBetaReal']
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [probability, probabilityBetaReal,
        mathematicalPartitionFunction_of_fintype,
        mathematicalPartitionFunctionBetaReal, hT_beta]

omit [MeasurableSingletonClass ι] [𝓒.IsFinite] in
/-- Differentiability of meanEnergyBetaReal' for finite systems. -/
lemma differentiable_meanEnergyBetaReal : Differentiable ℝ 𝓒.meanEnergyBetaReal' := by
  unfold meanEnergyBetaReal' probabilityBetaReal mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum fun i _ => ?_
  refine Differentiable.const_mul ?_ _
  refine Differentiable.div ?_ ?_ ?_
  · -- Numerator is differentiable
    apply Differentiable.exp
    simp -- The argument `-b * 𝓒.energy i` is linear in b, so differentiable
  · -- Denominator is differentiable
    refine Differentiable.fun_sum fun j _ => ?_
    apply Differentiable.exp
    simp -- The argument `-b * 𝓒.energy j` is linear in b, so differentiable
  · -- Denominator is non-zero
    intro x
    exact (mathematicalPartitionFunctionBetaReal_pos 𝓒 x).ne'

section FiniteSystemDerivatives

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
[MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)

omit [MeasurableSingletonClass ι] in
/-- The mathematical partition function is differentiable on ℝ. -/
lemma differentiable_mathematicalPartitionFunctionBetaReal :
    Differentiable ℝ 𝓒.mathematicalPartitionFunctionBetaReal := by
  unfold mathematicalPartitionFunctionBetaReal
  refine Differentiable.fun_sum ?_; intro i _; simp

/-- The numerator of the mean energy expression is also differentiable on ℝ. -/
noncomputable def meanEnergyNumerator (b : ℝ) : ℝ :=
  ∑ i, 𝓒.energy i * exp (-b * 𝓒.energy i)

omit [MeasurableSingletonClass ι] in
lemma differentiable_meanEnergyNumerator :
    Differentiable ℝ 𝓒.meanEnergyNumerator := by
  unfold meanEnergyNumerator
  refine Differentiable.fun_sum ?_; intro i _; apply Differentiable.const_mul; simp

omit [MeasurableSingletonClass ι] in
/-- Derivative of the mathematical partition function: `dZ/dβ = -Num`. -/
lemma deriv_mathematicalPartitionFunctionBetaReal (b : ℝ) :
    deriv 𝓒.mathematicalPartitionFunctionBetaReal b = -𝓒.meanEnergyNumerator b := by
  unfold mathematicalPartitionFunctionBetaReal meanEnergyNumerator
  field_simp [deriv_sum, mul_comm, Finset.sum_neg_distrib]

omit [MeasurableSingletonClass ι] in
/-- Derivative of the numerator of the mean energy. -/
lemma deriv_meanEnergyNumerator (b : ℝ) :
    deriv 𝓒.meanEnergyNumerator b = -∑ i, (𝓒.energy i)^2 * exp (-b * 𝓒.energy i) := by
  unfold meanEnergyNumerator
  field_simp [deriv_sum, mul_comm, pow_two]
  simp [mul_comm, mul_left_comm, mul_assoc]

end FiniteSystemDerivatives

variable {ι : Type} [Fintype ι] [MeasurableSpace ι]
[MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι) [Nonempty ι]

omit [MeasurableSingletonClass ι] in
/-- Differentiability of meanEnergyBetaReal' for finite systems. -/
lemma differentiable_meanEnergyBetaReal' : Differentiable ℝ 𝓒.meanEnergyBetaReal' := by
  -- U = Num/Z, which is a quotient of differentiable functions.
  let Z := 𝓒.mathematicalPartitionFunctionBetaReal
  let Num := 𝓒.meanEnergyNumerator
  have h_eq : 𝓒.meanEnergyBetaReal' = fun b => Num b / Z b := by
    funext b
    unfold meanEnergyBetaReal' probabilityBetaReal Num Z mathematicalPartitionFunctionBetaReal
    classical
    simp [mul_div_assoc, Finset.sum_div, Finset.sum_mul, Finset.mul_sum,
          meanEnergyNumerator, mathematicalPartitionFunctionBetaReal,
          mul_comm, mul_left_comm, mul_assoc]
  rw [h_eq]
  exact Differentiable.div (differentiable_meanEnergyNumerator 𝓒)
    (differentiable_mathematicalPartitionFunctionBetaReal 𝓒)
    (fun x => (mathematicalPartitionFunctionBetaReal_pos 𝓒 x).ne')

omit [MeasurableSingletonClass ι] in
/-- Calculation of the derivative of the mean energy with respect to β for finite systems.
dU/dβ = ⟨E⟩² - ⟨E²⟩. -/
lemma deriv_meanEnergyBetaReal' (b : ℝ) :
    deriv 𝓒.meanEnergyBetaReal' b =
    (𝓒.meanEnergyBetaReal' b)^2 - ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i := by
  let Z := 𝓒.mathematicalPartitionFunctionBetaReal
  let Num := 𝓒.meanEnergyNumerator
  have hZ_diff := (differentiable_mathematicalPartitionFunctionBetaReal 𝓒) b
  have hN_diff := (differentiable_meanEnergyNumerator 𝓒) b
  have hZ_ne_zero : Z b ≠ 0 := (mathematicalPartitionFunctionBetaReal_pos 𝓒 b).ne'
  have hU_eq_div : 𝓒.meanEnergyBetaReal' = fun x => Num x / Z x := by
    funext x
    classical
    unfold meanEnergyBetaReal' probabilityBetaReal Num Z mathematicalPartitionFunctionBetaReal
    simp [meanEnergyNumerator, Finset.sum_div, mul_div_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  have hquot' : deriv (fun x => Num x / Z x) b =
      (deriv Num b * Z b - Num b * deriv Z b) / (Z b)^2 := by
    simpa using deriv_div hN_diff hZ_diff hZ_ne_zero
  have hquot'' := hquot'
  have hnum := deriv_meanEnergyNumerator (𝓒 := 𝓒) b
  have hz   := deriv_mathematicalPartitionFunctionBetaReal (𝓒 := 𝓒) b
  simp [Num, Z, hnum, hz, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] at hquot''
  have h₁ :
      deriv (fun x => Num x / Z x) b =
        (-(Z b * ∑ i, (𝓒.energy i)^2 * exp (-b * 𝓒.energy i)) + Num b * Num b) / (Z b)^2 := by
    simpa [Num, Z] using hquot''
  have hprob :
      ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i
        = (∑ i, (𝓒.energy i)^2 * exp (-b * 𝓒.energy i)) / Z b := by
    classical
    unfold probabilityBetaReal Z
    calc
      ∑ i, (𝓒.energy i)^2 * (exp (-b * 𝓒.energy i) / Z b)
          = ∑ i, ((𝓒.energy i)^2 * exp (-b * 𝓒.energy i)) / Z b := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_assoc ((𝓒.energy i)^2) (Real.exp (-(b * 𝓒.energy i))) (Z b)).symm
      _ = (∑ i, (𝓒.energy i)^2 * exp (-b * 𝓒.energy i)) / Z b := by
            simp [Finset.sum_div]
  have h2 :
      deriv (fun x => Num x / Z x) b =
        (Num b / Z b)^2 - (∑ i, (𝓒.energy i)^2 * exp (-b * 𝓒.energy i)) / Z b := by
    rw [h₁]
    field_simp [hZ_ne_zero]
    ring
  have htarget :
      deriv (fun x => Num x / Z x) b =
        (Num b / Z b)^2 - ∑ i, (𝓒.energy i)^2 * 𝓒.probabilityBetaReal b i := by
    simpa [hprob] using h2
  simpa [hU_eq_div] using htarget

/-- The derivative of the mean energy with respect to β equals the negative of the energy variance
for finite systems: (∂U/∂β) = -Var(E). This rigorously proves the analytical condition required
for the Fluctuation-Dissipation Theorem in the finite case. -/
lemma derivWithin_meanEnergy_Beta_eq_neg_variance [IsFinite 𝓒] 
    (T : Temperature) (hT_pos : 0 < T.val) :
    derivWithin 𝓒.meanEnergy_Beta (Set.Ioi 0) (T.β : ℝ) = - 𝓒.energyVariance T := by
  let β₀ := (T.β : ℝ)
  have hβ₀_pos : 0 < β₀ := by
    unfold β₀
    exact div_pos one_pos (mul_pos kB_pos hT_pos)
  have h_eq_on : Set.EqOn 𝓒.meanEnergy_Beta 𝓒.meanEnergyBetaReal' (Set.Ioi 0) := by
    intro b hb; exact meanEnergy_Beta_eq_finite 𝓒 b hb
  rw [derivWithin_congr h_eq_on (h_eq_on hβ₀_pos)]
  have h_diff : DifferentiableAt ℝ 𝓒.meanEnergyBetaReal' β₀ :=
    (differentiable_meanEnergyBetaReal' 𝓒) β₀
  rw [h_diff.derivWithin (uniqueDiffOn_Ioi 0 β₀ hβ₀_pos)]
  rw [deriv_meanEnergyBetaReal' 𝓒 β₀]
  have h_U_eq : 𝓒.meanEnergyBetaReal' β₀ = 𝓒.meanEnergy T := by
    rw [← meanEnergy_Beta_eq_finite 𝓒 β₀ hβ₀_pos]
    simp [meanEnergy_Beta, ofβ_β]; aesop
  have h_prob_eq (i : ι) : 𝓒.probabilityBetaReal β₀ i = 𝓒.probability T i := by
    unfold probabilityBetaReal probability
    congr 1
    · unfold mathematicalPartitionFunctionBetaReal
      rw [mathematicalPartitionFunction_of_fintype]
  rw [h_U_eq]
  simp_rw [h_prob_eq]
  rw [energyVariance_of_fintype 𝓒 T]
  ring

open scoped Temperature Constants

/-- **The Fluctuation-Dissipation Theorem** for finite canonical ensembles:
C_V = Var(E) / (k_B T²).
The analytical condition (dU/dβ = -Var(E)) holds for finite systems.
-/
theorem fluctuation_dissipation_theorem_finite [IsFinite 𝓒] (T : Temperature) (hT_pos : 0 < T.val) :
    𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * (T.val : ℝ)^2) := by
  have hβ₀_pos : 0 < (T.β : ℝ) := beta_pos T hT_pos
  let β₀ := (T.β : ℝ)
  have h_diff_U_beta : DifferentiableWithinAt ℝ 𝓒.meanEnergy_Beta (Set.Ioi 0) β₀ := by
    have h_eq_on : Set.EqOn 𝓒.meanEnergy_Beta 𝓒.meanEnergyBetaReal' (Set.Ioi 0) := by
      intro b hb; exact meanEnergy_Beta_eq_finite 𝓒 b hb
    have h_diff' := (differentiable_meanEnergyBetaReal' 𝓒) (T.β : ℝ)
    apply DifferentiableWithinAt.congr_of_eventuallyEq h_diff'.differentiableWithinAt
    · exact eventuallyEq_nhdsWithin_of_eqOn h_eq_on
    · exact h_eq_on hβ₀_pos
  have h_Var_eq_neg_dUdβ := derivWithin_meanEnergy_Beta_eq_neg_variance 𝓒 T hT_pos
  apply fluctuation_dissipation_energy_parametric 𝓒 T hT_pos (by aesop) h_diff_U_beta

end FluctuationsFinite

end CanonicalEnsemble
