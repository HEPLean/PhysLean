/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
import PhysLean.Meta.Informal.SemiFormal
/-!

## Complex Lorentz tensors from Real Lorentz tensors

In this module we define the equivariant semi-linear map from real Lorentz tensors to
complex Lorentz tensors.

-/

namespace realLorentzTensor

open TensorSpecies
open Tensor
open complexLorentzTensor

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.C) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

/-- The semilinear map from real Lorentz tensors to complex Lorentz tensors.

Semiformal implmentation note: Probably the easist way to define this
is through basis. -/
semiformal_result "7RJQJ" toComplex (c : Fin n → realLorentzTensor.C) :
    ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c)

/-- The map `toComplex` is injective. -/
informal_lemma toComplex_injective where
  deps := []
  tag := "7RKCJ"

/-- The map `toComplex` is equivariant. -/
informal_lemma toComplex_equivariant where
  deps := []
  tag := "7RKDY"

/-!

## Relation to tensor operations

-/

/-- The map `toComplex` commutes with permT. -/
informal_lemma permT_toComplex where
  deps := [``permT]
  tag := "7RKA6"

/-- The map `toComplex` commutes with prodT. -/
informal_lemma prodT_toComplex where
  deps := [``prodT]
  tag := "7RKFF"

/-- The map `toComplex` commutes with contrT. -/
informal_lemma contrT_toComplex where
  deps := [``contrT]
  tag := "7RKFR"

/-- The map `toComplex` commutes with evalT. -/
informal_lemma evalT_toComplex where
  deps := [``evalT]
  tag := "7RKGK"

end realLorentzTensor
