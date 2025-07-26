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

In this module we define the type `Time`, corresponding to time in a given
(but arbitary) set of units, with a given (but arbitary) choice of origin (time zero).
We note that this is the version of time most often used in undergraduate and
non-mathematical physics.

The choice of units or origin can be made on a case-by-case basis, as
long as they are done consistently. However, since the choice of units and origin is
left implicit, Lean will not catch inconsistencies in the choice of units or origin when
working with `Time`.

For example, for the classical mechanics system corresponding to the harmonic oscillator,
one can take the origin of time to be the time at which the initial conditions are specified,
and the units can be taken as anything as long as the units chosen for time `t` and
the angular frequency `ω` are consistent.

With this notion of `Time`, it becomes equivalent to the type `ℝ`, and inherits all the
instances of `ℝ`.

Within other modules e.g. `TopTime.Basic`, we define versions of time with less choices made.

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

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv, fderiv_fun_const_smul]
  rfl
  fun_prop

end Time
