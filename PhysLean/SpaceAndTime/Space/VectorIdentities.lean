/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
/-!

# Vector identities

## i. Overview

In this module we prove properties of the gradient, divergence, and curl operators.
We show that on differentiable functions they are linear,
show their action on basic functions, and prove vector calculus identities

## ii. Key results

- `grad_inner_space_unit_vector` : The gradient in the direction of the space position.
- `curl_of_curl` : `∇ × (∇ × f) = ∇ (∇ ⬝ f) - Δ f`
- `div_of_curl_eq_zero` : `∇ ⬝ (∇ × f) = 0`

## iii. Table of contents

- A. Basic lemmas about derivatives of space
  - A.1. Derivative distributes over addition
  - A.2. Derivative distributes over scalar multiplication
  - A.3. Two spatial derivatives commute
  - A.4. Derivative of a component
  - A.5. Derivative of a component squared
  - A.6. Derivivatives of components
  - A.7. Derivative of a norm squared
    - A.7.1. Differentiability of the norm squared function
    - A.7.2. Derivative of the norm squared function
  - A.8. Derivative of the inner product
    - A.8.1. Differentiability of the inner product function
    - A.8.2. Derivative of the inner product function
  - A.9. Differentiability of derivatives
- B. Properties of the gradient operator
  - B.1. Gradient of the zero function
  - B.2. Gradient distributes over addition
  - B.3. Gradient of a constant function
  - B.4. Gradient distributes over scalar multiplication
  - B.5. Gradient distributes over negation
  - B.6. Expansion in terms of basis vectors
  - B.7. Components of the gradient
  - B.8. Inner product with a gradient
  - B.9. Gradient is equal to `gradient` from Mathlib
  - B.10. Value of gradient in the direction of the position vector
  - B.11. Gradient of the norm squared function
  - B.12. Gradient of the inner product function
- C. Properties of the curl operator
  - C.1. The curl on the zero function
  - C.2. The curl on a constant function
  - C.3. The curl distributes over addition
  - C.4. The curl distributes over scalar multiplication
  - C.5. The curl of a linear map is a linear map
  - C.6. Preliminary lemmas about second derivatives
  - C.7. The div of a curl is zero
  - C.8. The curl of a curl
- D. Properties of the divergence operator
  - D.1. The divergence on the zero function
  - D.2. The divergence on a constant function
  - D.3. The divergence distributes over addition
  - D.4. The divergence distributes over scalar multiplication
  - D.5. The divergence of a linear map is a linear map
- E. Properties of the Laplacian operator
- F. Properites of derivatives of time

## iv. References

-/

namespace Space

/-!

## A. Basic lemmas about derivatives of space

-/


/-!

## B. Properties of the gradient operator

-/


/-!

## C. Properties of the curl operator

-/

/-!

## D. Properties of the divergence operator

-/

/-!

## E. Properties of the Laplacian operator

-/



open InnerProductSpace

end Space

/-!

## F. Properites of derivatives of time

-/

namespace Time


  end Time
