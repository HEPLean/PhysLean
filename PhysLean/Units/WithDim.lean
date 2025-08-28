/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Units.Basic

/-!

## WithDim

WithDim is the type `M` which carrying the dimension `d`.

-/

open NNReal

structure WithDim (d : Dimension) (M : Type) [MulAction ℝ≥0 M] where
  val : M

namespace WithDim

@[ext]
lemma ext {d M}  [MulAction ℝ≥0 M] (x1 x2 : WithDim d M) (h : x1.val = x2.val) : x1 = x2 := by
  cases x1
  cases x2
  simp_all

instance (d : Dimension) (M : Type) [MulAction ℝ≥0 M] : MulAction ℝ≥0 (WithDim d M) where
  smul a m := ⟨a • m.val⟩
  one_smul m := ext _ _ (one_smul ℝ≥0 m.val)
  mul_smul a b m := by
    ext
    exact mul_smul a b m.val

@[simp]
lemma smul_val {d : Dimension} {M : Type} [MulAction ℝ≥0 M] (a : ℝ≥0) (m : WithDim d M) :
    (a • m).val = a • m.val := rfl

instance (d : Dimension) (M : Type) [inst : MulAction ℝ≥0 M] :
    CarriesDimension (WithDim d M) where
  d := d

@[simp]
lemma carriesDimension_d (d : Dimension) (M : Type) [MulAction ℝ≥0 M] :
    CarriesDimension.d (WithDim d M) = d := rfl

instance {d1 d2 : Dimension} :
    HMul (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2) ℝ) where
  hMul m1 m2 := ⟨m1.val * m2.val⟩

@[simp]
lemma withDim_hMul_val {d1 d2 : Dimension} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    (m1 * m2).val = m1.val * m2.val := rfl

instance {d1 d2 : Dimension} :
    DMul (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2)  ℝ) where
  mul_dim m1 m2 := by
    intro u1 u2
    ext
    simp
    rw [m1.2 u1, m2.2 u1]
    simp
    rw [smul_smul]
    congr 1
    rw [mul_comm]

end WithDim
