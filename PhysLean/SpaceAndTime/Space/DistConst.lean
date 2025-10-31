/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Curl
/-!

# The constant distribution on space
-/

namespace Space
open Distribution

/-- The constant distribution from `Space d` to a module `M` associated with
  `m : M`. -/
noncomputable def distConst {M } [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    (Space d) →d[ℝ] M := const ℝ (Space d) m

@[simp]
lemma distDeriv_distConst {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (m : M) :
    distDeriv μ (distConst d m) = 0 := by
  ext η
  simp [distDeriv, distConst]

@[simp]
lemma distGrad_distConst {d} (m : ℝ) :
    distGrad (distConst d m) = 0 := by
  ext η
  simp [distGrad, distConst]

@[simp]
lemma distDiv_distConst {d} (m : EuclideanSpace ℝ (Fin d)) :
    distDiv (distConst d m) = 0 := by
  ext η
  simp [distDiv, distConst]


@[simp]
lemma distCurl_distConst (m : EuclideanSpace ℝ (Fin 3)) :
    distCurl (distConst 3 m) = 0 := by
  ext η
  simp [distCurl, distConst]

end Space
