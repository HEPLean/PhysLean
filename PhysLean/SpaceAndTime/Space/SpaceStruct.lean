/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hou Run Feng, Joseph Tooby-Smith
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!

  # `SpaceStruct d`

  This is a work in progress reimplmentation of `Space d`
  that abstracts over the underlying `EuclideanSpace`

  `Space d` is planned to be deprecated in favor of `SpaceStruct d`.
  Once the necessary components are migrated to be compatible with `SpaceStruct`,
  it will become the default implementation of `Space`
-/

/--
  The type `SpaceStruct d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `SpaceStuct = Spacestruct 3`.
-/
structure SpaceStruct (d : ℕ := 3) where
    /-- The underlying EuclideanSpace associated `SpaceStruct d` -/
    val : EuclideanSpace ℝ (Fin d)

open MeasureTheory InnerProductSpace
/-!

## Basic operations on `Space`.

-/
noncomputable instance {d : Nat} : Add (SpaceStruct d) where
  add x y := ⟨x.val + y.val⟩

@[simp]
lemma add_val {d: ℕ} (x y : SpaceStruct d) :
    x + y = ⟨x.val + y.val⟩ := rfl

instance {d : Nat} : Neg (SpaceStruct d) where
  neg x := ⟨-x.val⟩

@[simp]
lemma neg_val {d: ℕ} (x : SpaceStruct d) :
    (-x).val = -x.val := rfl

noncomputable instance {d: ℕ} : Sub (SpaceStruct d)
  where sub x y := ⟨x.val - y.val⟩

instance {d : Nat} : SMul ℝ (SpaceStruct d) where
  smul k x := ⟨k • x.val⟩

instance {d : Nat} : Zero (SpaceStruct d) := ⟨⟨0⟩⟩

noncomputable instance : VAdd (EuclideanSpace ℝ (Fin d)) (SpaceStruct d) where
  vadd v s := ⟨v + s.val⟩

/-!

## Instances on `Space`

-/

noncomputable instance {d : ℕ} : AddGroup (SpaceStruct d) where
  add_assoc := by simp [add_assoc]
  zero_add := fun ⟨x⟩ => by
    show SpaceStruct.mk (0 + x) = SpaceStruct.mk x
    rw [zero_add]
  add_zero := fun ⟨x⟩ => by
    show SpaceStruct.mk (x + 0) = SpaceStruct.mk x
    rw [add_zero]
  neg_add_cancel := fun ⟨x⟩ => by
    show SpaceStruct.mk (-x) + SpaceStruct.mk x = SpaceStruct.mk 0
    show SpaceStruct.mk (-x + x) = SpaceStruct.mk 0
    rw [add_comm (-x) x, add_neg_cancel]
  nsmul n x := ⟨n • x.val⟩
  zsmul n x := ⟨n • x.val⟩

noncomputable instance {d: ℕ} : AddCommMonoid (SpaceStruct d) where
  add_comm := by simp [add_comm]

noncomputable instance {d : ℕ} : AddCommGroup (SpaceStruct d) where

instance {d: ℕ}: Module ℝ (SpaceStruct d) where
  one_smul t := by simp [one_smul]
  smul_add k t1 t2 := by ext; simp [mul_add]
  smul_zero k := by ext; simp [mul_zero]
  add_smul k1 k2 t := by ext; simp [add_mul]
  mul_smul k1 k2 t := by ext; simp [mul_assoc]
  zero_smul t := by ext; simp [zero_smul]

-- noncomputable instance {d: ℕ}: SeminormedAddCommGroup (SpaceStruct d) where
--   dist_self := by intros; simp [dist_eq_real_dist]
--   dist_comm := by intros; simp [dist_eq_real_dist, dist_comm]
--   dist_triangle := by intros; simp [dist_eq_real_dist, dist_triangle]

/-!

## Inner product

-/

noncomputable instance (d: ℕ) : Inner ℝ (SpaceStruct d) where
  inner x y := Inner.inner ℝ x.val y.val

@[simp]
lemma inner_def {d: ℕ} (x1 x2 : SpaceStruct d) :
    ⟪x1, x2⟫_ℝ = ⟪x1.val, x2.val⟫_ℝ := rfl

lemma inner_eq_sum {d: ℕ} (p q : SpaceStruct d) :
    inner ℝ p q = ∑ i, p.val i * q.val i := by
  simp only [inner, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm (q.val i) (p.val i)

-- noncomputable instance {d: ℕ } : InnerProductSpace ℝ (SpaceStruct d) where
--   norm_sq_eq_re_inner := by intros; simp [norm]; ring
--   conj_inner_symm := by intros; simp [inner_def]; ring
--   add_left := by intros; simp [inner_def, add_mul]
--   smul_left := by intros; simp [inner_def]; ring

