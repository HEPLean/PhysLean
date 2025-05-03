/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
/-!
# Time

In this file we define the time worldvolume as a real line.

## Note on implementation

The definition of `Time` currently inherits all instances of
`ℝ`.

This, in particular, automatically equips `Time` with a
norm. This norm induces a metric on `Time` which is the standard
flat metric. Thus `Time` automatically corresponds to
flat time.

The definition of `deriv` through `fderiv` explicitly uses this metric.

`Time` also inherits instances of `ℝ` such as
a zero vector, the ability to add two time positions etc, which
are not really allowed operations on `Time`.

-/

/-- The type `Time` represents the time manifold. -/
abbrev Time := ℝ

namespace Time

/-- Given a function `f : Time → M` the derivative of `f`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) : Time → M :=
  (fun t => fderiv ℝ f t 1)

@[inherit_doc deriv]
scoped notation "∂ₜ" => deriv

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv]
  rw [fderiv_const_smul]
  rfl
  fun_prop

end Time
