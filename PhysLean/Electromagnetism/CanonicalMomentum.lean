/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.KineticTerm
import PhysLean.ClassicalMechanics.VectorFields
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct


namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor ContDiff

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
open Lorentz.Vector
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

noncomputable local instance {d} : InnerProductSpace ℝ (SpaceTime d) :=
  SpaceTime.innerProductSpace d


abbrev LorentzCurrentDensity (d : ℕ := 3) := SpaceTime d → Lorentz.Vector d

namespace LorentzCurrentDensity

noncomputable def chargeDensity (J : LorentzCurrentDensity d) : Time → Space d → ℝ :=
  fun t x => J (toTimeAndSpace.symm (t, x)) (Sum.inl 0)

noncomputable def currentDensity (J : LorentzCurrentDensity d) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x i => J (toTimeAndSpace.symm (t, x)) (Sum.inr i)

end LorentzCurrentDensity

noncomputable def lagrangian (A : ElectromagneticPotential d) (J : LorentzCurrentDensity d)
    (x : SpaceTime d) : ℝ :=
    A.kineticTerm x - ⟪A x, J x⟫ₘ

lemma lagrangian_add_const {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (c : Lorentz.Vector d) (x : SpaceTime d):
    lagrangian (fun x => A x + c) J x = lagrangian A J x - ⟪c, J x⟫ₘ := by
  rw [lagrangian, lagrangian, kineticTerm_add_const]
  simp
  ring

noncomputable def gradLagrangian {d} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : SpaceTime d → Lorentz.Vector d :=
  (δ (q':=A), ∫ x, lagrangian q' J x)

lemma lagrangian_hasVarGradientAt_eq_add_gradKineticTerm (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
     HasVarGradientAt (fun A => lagrangian A J)
     (A.gradKineticTerm - ((∑ μ, fun x =>  (η μ μ * J x μ) • Lorentz.Vector.basis μ))) A := by
  conv =>
    enter [1, q', x]
    rw [lagrangian]
  apply HasVarGradientAt.add
  · exact A.kineticTerm_hasVarGradientAt hA
  apply HasVarGradientAt.neg
  conv =>
    enter [1, q', x]
    rw [minkowskiProduct_toCoord_minkowskiMatrix]
  apply HasVarGradientAt.sum _ hA
  intro μ
  have h1 := hasVarAdjDerivAt_component μ A hA
  have h2' : ContDiff ℝ ∞ fun x => η μ μ * J x μ :=
    ContDiff.mul (by fun_prop) (contDiff_euclidean.mp hJ μ )
  have h2 := HasVarAdjDerivAt.fun_mul h2' _ _ A h1
  have h3' : (fun (φ : SpaceTime d → Lorentz.Vector d) x => η μ μ * J x μ * φ x μ) =
    (fun (φ : SpaceTime d → Lorentz.Vector d)  x => η μ μ * φ x μ * J x μ) := by
    funext φ x
    ring
  rw [h3'] at h2
  apply HasVarGradientAt.intro _ h2
  simp


lemma gradLagrangian_eq_kineticTerm_sub (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian J = A.gradKineticTerm -
      ((∑ μ, fun x =>  (η μ μ * J x μ) • Lorentz.Vector.basis μ)) := by
  apply HasVarGradientAt.varGradient
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ


lemma lagrangian_hasVarGradientAt_gradLagrangian (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
     HasVarGradientAt (fun A => lagrangian A J) (A.gradLagrangian J) A := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  apply lagrangian_hasVarGradientAt_eq_add_gradKineticTerm A hA J hJ

lemma gradLagrangian_eq_sum_fieldStrengthMatrix (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    A.gradLagrangian J = fun x => ∑ ν,
      (η ν ν • (∑ μ, ∂_ μ (fun x => (A.fieldStrengthMatrix x) (μ, ν)) x - J x ν)
      • Lorentz.Vector.basis ν) := by
  rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
  funext x
  simp
  rw [gradKineticTerm_eq_fieldStrength]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [smul_smul, ← sub_smul, ← mul_sub, ← smul_smul]
  exact hA
open Time

lemma gradLagrangian_eq_electricField_magneticField (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity 3)
    (hJ : ContDiff ℝ ∞ J) (x : SpaceTime) :
    A.gradLagrangian J x = ((∇ ⬝ A.electricField x.time) x.space - J.chargeDensity x.time x.space) •
       Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time  - (∇ × (A.magneticField x.time)) x.space
          +  J.currentDensity x.time x.space) i • Lorentz.Vector.basis (Sum.inr i))  := by
  calc A.gradLagrangian J x
    _ = A.gradKineticTerm x - ((∑ μ, (η μ μ * J x μ) • Lorentz.Vector.basis μ))  := by
      rw [gradLagrangian_eq_kineticTerm_sub A hA J hJ]
      simp
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0) +
        ∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i) -
        ((∑ μ, (η μ μ * J x μ) • Lorentz.Vector.basis μ)) := by
      rw [gradKineticTerm_eq_electric_magnetic _ _ hA]
      rfl
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0) +
        ∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i) -
        (( J x (Sum.inl 0) • Lorentz.Vector.basis (Sum.inl 0))
        - (∑ i,  J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
      rw [Fintype.sum_sum_type]
      simp
      rfl
    _ = (∇ ⬝ (A.electricField x.time)) x.space • Lorentz.Vector.basis (Sum.inl 0)
        - (J x (Sum.inl 0) • Lorentz.Vector.basis (Sum.inl 0)) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i)
        + (∑ i,  J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
        module
    _ = ((∇ ⬝ (A.electricField x.time)) x.space - J x (Sum.inl 0)) •
        Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i)
          • Lorentz.Vector.basis (Sum.inr i)
        + (∑ i,  J x (Sum.inr i) • Lorentz.Vector.basis (Sum.inr i))) := by
        module
    _ = ((∇ ⬝ (A.electricField x.time)) x.space - J.chargeDensity x.time x.space) •
       Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time i - (∇ × (A.magneticField x.time)) x.space i
          +  J x (Sum.inr i)) • Lorentz.Vector.basis (Sum.inr i)) := by
        conv_rhs =>
          enter [2, 2, i]
          rw [add_smul]
        rw [Finset.sum_add_distrib]
        congr
        simp
    _ = ((∇ ⬝ A.electricField x.time) x.space - J.chargeDensity x.time x.space) •
       Lorentz.Vector.basis (Sum.inl 0) +
        (∑ i, (∂ₜ (A.electricField · x.space) x.time  - (∇ × (A.magneticField x.time)) x.space
          +  J.currentDensity x.time x.space) i • Lorentz.Vector.basis (Sum.inr i)) := by
      congr
      funext i
      simp [LorentzCurrentDensity.currentDensity]

noncomputable def canonicalMomentum (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    SpaceTime d → Lorentz.Vector d := fun x =>
  gradient (fun (v : Lorentz.Vector d) =>
    lagrangian (fun x => A x + x (Sum.inl 0) • v) J x) 0
  - x (Sum.inl 0) • gradient (fun (v : Lorentz.Vector d) =>
    lagrangian (fun x => A x + v) J x) 0

lemma kineticTerm_add_time_mul_const {d} (A : ElectromagneticPotential d)
    (ha : Differentiable ℝ A)
    (c : Lorentz.Vector d) (x : SpaceTime d) :
    kineticTerm (fun x => A x + x (Sum.inl 0) • c) x = A.kineticTerm x +
       (-1 / 2 * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
         2 * c ν * (∂_ ν A x (Sum.inl 0)))) + 1/2 * c (Sum.inl 0) ^2)  := by
  have diff_a  : ∂_ (Sum.inl 0) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inl 0) A + (fun x => c) := by
    funext x ν
    rw [SpaceTime.deriv_eq]
    rw [fderiv_fun_add _ (by fun_prop)]
    simp
    congr
    rw [fderiv_smul_const (by fun_prop)]
    simp [Lorentz.Vector.coordCLM]
    exact ha.differentiableAt
  have diff_b (i : Fin d) : ∂_ (Sum.inr i) (fun x => A x + x (Sum.inl 0) • c) =
      ∂_ (Sum.inr i) A := by
    funext x ν
    rw [SpaceTime.deriv_eq]
    rw [fderiv_fun_add _ (by fun_prop)]
    simp
    rw [fderiv_smul_const (by fun_prop)]
    simp
    rw [← SpaceTime.deriv_eq]
    simp [Lorentz.Vector.coordCLM]
    exact ha.differentiableAt
  have hdiff (μ : Fin 1 ⊕ Fin d)  :
     ∂_ μ (fun x => A x + x (Sum.inl 0) • c) x =
      ∂_ μ A x + if μ = Sum.inl 0 then c else 0 := by
    match μ with
    | Sum.inl 0 => simp [diff_a]
    | Sum.inr i => simp [diff_b i]

  rw [kineticTerm_eq_sum_potential]

  calc _
    _ = -1 / 2 *
    ∑ μ, ∑ ν, (η μ μ * η ν ν * (∂_ μ A x + if μ = Sum.inl 0 then c else 0 ) ν ^ 2 -
          (∂_ μ A x + if μ = Sum.inl 0 then c else 0) ν *
          (∂_ ν A x + if ν = Sum.inl 0 then c else 0 ) μ) := by
      congr
      funext μ
      congr
      funext ν
      rw [hdiff μ, hdiff ν]
    _ = -1 / 2 *
    ∑ μ, ∑ ν, (η μ μ * η ν ν * (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0 ) ^ 2 -
          (∂_ μ A x ν + if μ = Sum.inl 0 then c ν else 0) *
          (∂_ ν A x μ + if ν = Sum.inl 0 then c μ else 0 ) ) := by
      congr
      funext μ
      congr
      funext ν
      congr
      all_goals
      · simp
        split_ifs
        simp
        rfl
     _ = -1 / 2 *
    ∑ μ, ∑ ν, ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) +
          (if μ = Sum.inl 0 then c ν else 0)  * (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0 )  -
         (∂_ ν A x μ ) - (if ν = Sum.inl 0 then c μ else 0 ))
          - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      congr
      funext μ
      congr
      funext ν
      ring
     _ = -1 / 2 *
       ∑ μ, ∑ ν, ((η μ μ * η ν ν * (∂_ μ A x ν) ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ)) +
       -1 / 2 * ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0)  * (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0 )  -
         (∂_ ν A x μ ) - (if ν = Sum.inl 0 then c μ else 0 ))
          - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      rw [← mul_add]
      rw [← Finset.sum_add_distrib]
      congr
      funext μ
      rw [← Finset.sum_add_distrib]
      congr
      ring_nf
    _ = A.kineticTerm x +
       -1 / 2 * ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0)  * (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0 )  -
         (∂_ ν A x μ ) - (if ν = Sum.inl 0 then c μ else 0 ))
          - (∂_ μ A x ν) * (if ν = Sum.inl 0 then c μ else 0)) := by
      rw [kineticTerm_eq_sum_potential]
    _ = A.kineticTerm x +
       -1 / 2 * ∑ μ, ∑ ν, ((if μ = Sum.inl 0 then c ν else 0)  * (2 * η μ μ * η ν ν * ∂_ μ A x ν +
          η μ μ * η ν ν * (if μ = Sum.inl 0 then c ν else 0 )  -
         (∂_ ν A x μ ) - (if ν = Sum.inl 0 then c μ else 0 ))
          - (∂_ ν A x μ) * (if μ = Sum.inl 0 then c ν else 0)) := by
      congr 1
      conv_rhs =>
        enter [2, 2, μ]
        rw [Finset.sum_sub_distrib]
      conv_rhs =>
        rw [Finset.sum_sub_distrib]
        enter [2, 2]
        rw [Finset.sum_comm]
      rw [← Finset.sum_sub_distrib]
      conv_rhs =>
        enter [2, 2, μ]
        rw [← Finset.sum_sub_distrib]
    _ = A.kineticTerm x +
       -1 / 2 * ∑ ν, (c ν * (2 * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν -
         (∂_ ν A x (Sum.inl 0) ) - (if ν = Sum.inl 0 then c (Sum.inl 0) else 0))
          - (∂_ ν A x (Sum.inl 0)) * c ν) := by
      congr 1
      simp
    _ = A.kineticTerm x +
       -1 / 2 * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
         2 * c ν * (∂_ ν A x (Sum.inl 0))) - c ν * (if ν = Sum.inl 0 then c (Sum.inl 0) else 0))
         := by
      congr
      funext ν
      ring
    _ = A.kineticTerm x +
       (-1 / 2 * ∑ ν, ((2 * c ν * η ν ν * ∂_ (Sum.inl 0) A x ν + η ν ν * c ν ^ 2 -
         2 * c ν * (∂_ ν A x (Sum.inl 0)))) + 1/2 * c (Sum.inl 0) ^2)  := by
        simp
        ring


lemma canonicalMomentum_eq_gradient_kineticTerm {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum J  = fun x =>
    gradient (fun (v : Lorentz.Vector d) =>
    kineticTerm (fun x => A x + x (Sum.inl 0) • v) x) 0:= by
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  rw [gradient, canonicalMomentum]
  simp
  rw [inner_sub_left, inner_smul_left]
  simp [gradient]
  conv_lhs =>
    enter [2]
    simp [lagrangian_add_const]
  have hx : DifferentiableAt ℝ (fun v => kineticTerm (fun x => A x + x (Sum.inl 0) • v) x) 0 := by
    apply Differentiable.differentiableAt _
    conv =>
      enter [2, v]
      rw [kineticTerm_add_time_mul_const _  (hA.differentiable (by simp))]
    fun_prop

  conv_lhs =>
    enter [1]
    simp only [lagrangian, Fin.isValue, map_add, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_fun_sub hx (by fun_prop)]
    simp
    rw [fderiv_const_mul (by fun_prop)]
  simp
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp


lemma canonicalMomentum_eq {d} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity d) :
    A.canonicalMomentum J  = fun x => fun μ => η μ μ • A.fieldStrengthMatrix x (μ, Sum.inl 0) := by
  rw [canonicalMomentum_eq_gradient_kineticTerm A hA J]
  funext x
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  simp [gradient]
  conv_lhs =>
    enter [1, 2, v]
    rw [kineticTerm_add_time_mul_const _ (hA.differentiable (by simp))]
  simp
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  conv_lhs =>
    enter [1, 1, 2, 1, 2, i]
    rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    rw [fderiv_pow _ (by fun_prop)]
    simp
  conv_lhs =>
    enter [1, 1, 2, 2, 2, i]
    rw [fderiv_mul_const (by fun_prop)]
    rw [fderiv_const_mul (by fun_prop)]
    simp
  rw [fderiv_pow _ (by fun_prop)]
  simp [Lorentz.Vector.coordCLM]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr
  funext μ
  simp
  rw [fieldStrengthMatrix, toFieldStrength_basis_repr_apply_eq_single]
  simp
  ring_nf
  simp

noncomputable def hamiltonian (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (x : SpaceTime d) : ℝ :=
    ∑ μ, A.canonicalMomentum J x μ * ∂_ (Sum.inl 0) A x μ - lagrangian A J x

lemma hamiltonian_eq_electricField_magneticField (A : ElectromagneticPotential 3)
    (hA : ContDiff ℝ 2 A) (J : LorentzCurrentDensity 3) (x : SpaceTime) :
    A.hamiltonian J x = 1/2 * (‖A.electricField x.time x.space‖ ^ 2
      + ‖A.magneticField x.time x.space‖ ^ 2)
      + ∑ i, (A.electricField x.time x.space i * ∂_ (Sum.inr i) A x (Sum.inl 0)) +
      ⟪A x, J x⟫ₘ := by
  conv_lhs =>
    rw [hamiltonian, lagrangian, canonicalMomentum_eq A hA J]

    rw [kineticTerm_eq_electric_magnetic' (hA.differentiable (by simp))]
    simp [Fintype.sum_sum_type, Fin.sum_univ_three]
  repeat rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
  simp
  have h1 (i : Fin 3): ∂_ (Sum.inl 0) A x (Sum.inr i) = -
    (A.fieldStrengthMatrix x (Sum.inr i, Sum.inl 0) + ∂_ (Sum.inr i) A x (Sum.inl 0)) := by
    rw [fieldStrengthMatrix, toFieldStrength_basis_repr_apply_eq_single]
    simp
  rw [h1, h1, h1]
  repeat rw [fieldStrengthMatrix_eq_electric_magnetic_of_spaceTime]
  simp
  calc _
    _ = ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i)^2
      + ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      ring
     _ = ‖A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2‖ ^ 2
      + ∑ i, (A.electricField (toTimeAndSpace x).1 (toTimeAndSpace x).2 i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by
      congr
      rw [PiLp.norm_sq_eq_of_L2]
      simp
     _ = ‖A.electricField x.time x.space‖ ^ 2
      + ∑ i, (A.electricField x.time x.space i *
          (∂_ (Sum.inr i) A x (Sum.inl 0))) -
        2⁻¹ * (‖A.electricField (time x) fun i => x (Sum.inr i)‖ ^ 2 -
          ‖A.magneticField (time x) fun i => x (Sum.inr i)‖ ^ 2) +
      (minkowskiProduct (A x)) (J x) := by rfl
    _ = 1/2 * (‖A.electricField x.time x.space‖ ^ 2 +  ‖A.magneticField x.time x.space‖ ^ 2)
      + ∑ i, (A.electricField x.time x.space i * ∂_ (Sum.inr i) A x (Sum.inl 0)) +
      ⟪A x, J x⟫ₘ := by simp; ring
  simp
  repeat exact hA.differentiable (by simp)


end ElectromagneticPotential

end Electromagnetism
