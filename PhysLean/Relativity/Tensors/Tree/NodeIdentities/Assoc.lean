/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Elab
/-!

## Specific associativity results for tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open PhysLean.Fin
open TensorProduct

namespace TensorTree

variable {k : Type} [CommRing k] {S : TensorSpecies k}

open TensorSpecies Tensor

/-- The associativity lemma for `t1 | μ ⊗ t2 | μ ν ⊗ t3 | ν σ`. -/
lemma assoc_one_two_two {c1 c2 c3 : S.C} (t1 : S.Tensor ![c1])
    (t2 : S.Tensor ![S.τ c1, c2]) (t3 : S.Tensor ![S.τ c2, c3]) :
    {t1 | μ ⊗ t2 | μ ν ⊗ t3 | ν σ}ᵀ = ({t1 | μ ⊗ (t2 | μ ν ⊗ t3 | ν σ)}ᵀ
    |> permT id (And.intro (Function.bijective_id) (fun i => by
      fin_cases i; rfl))) := by
  rw [prodT_swap, contrT_permT, prodT_contrT_snd, contrT_permT, permT_permT]
  rw [prodT_swap, prodT_assoc t1 t2 t3, permT_permT]
  rw [contrT_permT, contrT_permT, permT_permT]
  conv_rhs =>
    rw [prodT_contrT_snd, contrT_permT, permT_permT, contrT_comm, permT_permT]
  apply permT_congr
  · simp
    ext i
    fin_cases i
    · simp
  · rfl

end TensorTree
