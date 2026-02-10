/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
/-!

# Laplace-Runge-Lenz vector

-/

namespace QuantumMechanics
noncomputable section
open SchwartzMap

/-- The Laplace-Runge-Lenz vector operator, `𝐀ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - km 𝐱ᵢ/r`,
with inverse radius regularized by `ε`. -/
def lrlOperator {km : ℝ} (i : Fin d) (ε : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (1/2 : ℝ) • ∑ j, (𝐩[j] ∘L 𝐋[i,j] + 𝐋[i,j] ∘L 𝐩[j]) - km • 𝐫[-1,ε] ∘L 𝐱[i]

@[inherit_doc lrlOperator]
macro "𝐀[" i:term "]" : term => `(lrlOperator $i)

end
