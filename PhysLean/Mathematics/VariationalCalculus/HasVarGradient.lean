/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
import Mathlib.Tactic.FunProp.Differentiable
/-!

# Variational gradient

Definition of variational gradient that allows for formal treatement of variational calculus
as used in physics textbooks.
-/

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {U} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Function `grad` is variational gradient of functional `S` at point `u`.

This formalizes the notion of variational gradient `δS/δu` of a functional `S` at a point `u`.

However, it is not defined for a functional `S : (X → U) → ℝ` but rather for the function
`S' : (X → U) → (X → ℝ)` which is related to the usual functional as `S u = ∫ x, S' (u x) x ∂μ`.
For example for action integral, `S u = ∫ t, L (u t) (deriv u t)` we have
`S' u t = L (u t) (deriv u t)`. Working with `S'` rather than with `S` allows us to ignore certain
technicalities with integrability.

Examples:

Euler-Lagrange equations:
```
δ/δx ∫ L(x,ẋ) dt = ∂L/∂ x - d/dt (∂L/∂ẋ)
```
can be expressed as
```
HasVarGradientAt
  (fun u t => L (u t) (deriv u t))
  (fun t =>
    deriv (L · (deriv u t)) ((u t))
    -
    deriv (fun t' => deriv (L (u t') ·) (deriv u t')) t)
  u
```

Laplace equation is variational gradient of Dirichlet energy:
```
δ/δu ∫ 1/2*‖∇u‖² = - Δu
```
can be expressed as
```
HasVarGradientAt
  (fun u t => 1/2 * deriv u t^2)
  (fun t => - deriv (deriv u) t)
  u
```
-/
inductive HasVarGradientAt (S' : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U) : Prop
  | intro (F')
      (diff : ∀ δu x, IsTestFunction δu →
        Differentiable ℝ (fun s : ℝ => S' (fun x' => u x' + s • δu x') x))
      (adjoint : HasVarAdjoint (fun δu x => deriv (fun s : ℝ => S' (u + s • δu) x) 0) F')
      /- This condition is effectivelly saying that `F' (fun _ => 1) = grad` but `F'` is not
      guaranteed to produce meaningful result for `fun _ => 1` as it is not test function.
      Therefore we require that it is possible to glue `grad` together by -/
      (eq : ∀ (x : X), ∃ D : Set X,
        x ∈ D ∧ IsCompact D
        ∧
        ∀ (φ : X → ℝ), IsTestFunction φ → (∀ x ∈ D, φ x = 1) → F' φ x = grad x)

lemma HasVarGradientAt.unique
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasureSpace X]
    [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (@volume X _)]
    {S' : (X → U) → (X → ℝ)} {grad grad' : X → U} {u : X → U}
    (h : HasVarGradientAt S' grad u) (h' : HasVarGradientAt S' grad' u) :
    grad = grad' := by

  obtain ⟨F,_,hF,eq⟩ := h
  obtain ⟨G,_,hG,eq'⟩ := h'
  funext x
  obtain ⟨D,hm,hD,hgrad⟩ := eq x
  obtain ⟨D',_,hD',hgrad'⟩ := eq' x

  -- prepare test function that is one on `D ∪ D'`
  let r := sSup ((fun x => ‖x‖) '' (D ∪ D'))
  have : 0 ≤ r := by
    obtain ⟨x, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := D ∪ D')
      (IsCompact.union hD hD') (Set.Nonempty.inl (Set.nonempty_of_mem hm))
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
  let f := fun x => φ.toFun x
  have hφ : IsTestFunction (fun x : X => φ x) := by
    constructor
    apply ContDiffBump.contDiff
    apply ContDiffBump.hasCompactSupport
  have hφ' : ∀ x, x ∈ D ∪ D' → x ∈ Metric.closedBall 0 φ.rIn := by
    intro x hx
    simp [φ, r]
    obtain ⟨y, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := D ∪ D')
      (IsCompact.union hD hD') (Set.Nonempty.inl (Set.nonempty_of_mem hm))
      (f := fun x => ‖x‖) (by fun_prop)
    rw [h2]
    have h3' := h3 x hx
    apply le_trans h3'
    simp
  have h := hgrad φ hφ
    (by intros _ hx; unfold φ; rw[φ.one_of_mem_closedBall]; apply hφ'; simp[hx])
  have h' := hgrad' φ hφ
    (by intros _ hx; unfold φ; rw[φ.one_of_mem_closedBall]; apply hφ'; simp[hx])
  rw[← h, ← h',hF.unique hG φ (ContDiffBump.contDiff φ)]

/-- Variation of `S(x) = ∫ 1/2*m*‖ẋ‖² - V(x)` gives Newton's law of motion `δS(x) = - m*ẍ - V'(x)`-/
lemma euler_lagrange_particle_1d (m : ℝ) (u V : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hV : ContDiff ℝ ∞ V) :
    HasVarGradientAt
      (fun (u : ℝ → ℝ) (t : ℝ) => 1/2 * m * deriv u t ^ 2 - V (u t))
      (fun t => - m * deriv (deriv u) t - deriv V (u t))
      u := by
  apply HasVarGradientAt.intro
  case diff =>
    intro _ _ hδu
    have := hδu.1
    have : (2:WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
    fun_prop (config:={maxTransitionDepth:=2}) (disch:=aesop) [deriv]
  case adjoint =>
    eta_expand
    have := hu.differentiable ENat.LEInfty.out
    have := hV.differentiable ENat.LEInfty.out
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro δu hδu; funext t
      have := hδu.differentiable
      have hd : deriv (fun y => V (u t + y * δu t)) 0
                =
                deriv V (u t) * δu t := by
        have h := deriv_comp (h₂:=V) (h:=fun y => u t + y * δu t) 0 (by fun_prop) (by fun_prop)
        simp +unfoldPartialApp [Function.comp] at h
        exact h
      conv =>
        lhs
        simp (disch:=fun_prop (config:={maxTransitionDepth:=2}) (disch:=simp)) [deriv_add,hd]
        ring_nf
    case h =>
      apply HasVarAdjoint.sub
      · apply HasVarAdjoint.mul_left (ψ := fun x => m * deriv u x) (hψ := by fun_prop)
        apply HasVarAdjoint.deriv
      · apply HasVarAdjoint.mul_left (hψ := by fun_prop)
        apply HasVarAdjoint.id
  case eq =>
    intro x
    use (Metric.closedBall x 1)
    constructor
    · simp
    · constructor
      · exact isCompact_closedBall x 1
      · intro φ hφ hφ'
        simp[hφ',hφ]
        have h : (fun x => m * deriv u x * φ x) =ᶠ[nhds x] (fun x => m * deriv u x) :=
          Filter.eventuallyEq_of_mem (Metric.closedBall_mem_nhds x Real.zero_lt_one)
            (by intro x' hx'; simp[hφ' x' hx'])
        simp[h.deriv_eq]
