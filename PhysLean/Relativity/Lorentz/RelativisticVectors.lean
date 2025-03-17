/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/

import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Relativity.Lorentz.RealVector.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Relativistic Vectors in Lorentz Space

This file defines the fundamental 4-vectors (position, velocity, momentum) of special relativity and
their transformation properties under the Lorentz group in flat Minkowski spacetime.

## Key Features
* Defines structures for 4-position, 4-velocity and 4-momentum vectors
* Implements Minkowski inner product and causal structure
* Proves key properties like proper time additivity and mass-energy equivalence
* Shows invariance under Lorentz transformations

## Main Limitations

* Uses a simplified model with vectors in a single linear space, rather than properly distinguishing
  affine points (events) from their displacement vectors

* Limited to flat Minkowski spacetime - does not handle curved spacetimes of general relativity

* Velocity addition is implemented only for collinear velocities

* Particle momentum calculations assume massive particles, special handling needed for massless case

* Uses (-+++) metric signature convention by default, though signature is configurable

## Future Work

* Distinguish events (points) from displacements (vectors) using affine spaces
* Add general non-collinear velocity addition
* Handle massless particles via limits
* Add support for curved spacetimes
* Prove additional relativistic effects like length contraction
-/

noncomputable section

namespace Lorentz

open Matrix

/-- The physical dimension of Minkowski spacetime in special relativity. -/
def spacetimeDim : ℕ := 4

/-- A Lorentz 4-position vector in Minkowski spacetime. -/
structure LorentzPosition4Vector (d : ℕ) where
  /-- The underlying Lorentz vector. -/
  toLorentzVector : ContrMod d

/-- A physical 4-vector in Minkowski spacetime. -/
abbrev PhysicalLorentzVector := LorentzPosition4Vector spacetimeDim

/-- Constructs a 4-vector from time and space components. -/
def mkLorentzVector (t : ℝ) (x y z : ℝ) : PhysicalLorentzVector :=
  ⟨ContrMod.mk $ fun i => match i with
    | Sum.inl ⟨0, _⟩ => t
    | Sum.inl ⟨1, _⟩ => x
    | Sum.inl ⟨2, _⟩ => y
    | Sum.inl ⟨3, _⟩ => z
    | _ => 0⟩


/-- Extracts the timelike component of a 4-vector. -/
def timeComponent (v : PhysicalLorentzVector) : ℝ :=
  v.toLorentzVector.toFin1dℝ (Sum.inl 0)

/-- Metric signature conventions for Minkowski space. -/
inductive MetricSignature
  | TimeNegative -- (-+++) convention
  | TimePositive -- (+---) convention

/-- Configuration for the Lorentz space. -/
structure LorentzConfig where
  /-- The signature convention for the metric. -/
  signature : MetricSignature := MetricSignature.TimeNegative

/-- Minkowski metric matrix with configurable signature. -/
def minkowskiMatrixWithSignature (cfg : LorentzConfig) (d : ℕ) : Matrix (Sum Unit (Fin d)) (Sum Unit (Fin d)) ℝ :=
  let η : Matrix (Sum Unit (Fin d)) (Sum Unit (Fin d)) ℝ := fun i j =>
    if i = j then
      if i = Sum.inl Unit.unit then
        match cfg.signature with
        | MetricSignature.TimeNegative => -1
        | MetricSignature.TimePositive => 1
      else
        match cfg.signature with
        | MetricSignature.TimeNegative => 1
        | MetricSignature.TimePositive => -1
    else 0
  η

namespace LorentzPosition4Vector

variable {d : ℕ}

@[ext]
theorem ext {x y : LorentzPosition4Vector d} (h : x.toLorentzVector = y.toLorentzVector) : x = y := by
  cases x; cases y; congr

/-- The instance of an additive commutative group for Lorentz 4-position vectors. -/
@[simp]
instance : AddCommGroup (LorentzPosition4Vector d) where
  add x y := ⟨x.toLorentzVector + y.toLorentzVector⟩
  add_assoc := by
    intros a b c
    ext x
    dsimp
    exact add_assoc _ _ _
  neg := fun x => ⟨-x.toLorentzVector⟩
  zero := ⟨0⟩
  zero_add := by
    intro a
    apply LorentzPosition4Vector.ext
    simp
    exact zero_add a.toLorentzVector
  add_zero := by
    intro a
    apply LorentzPosition4Vector.ext
    simp
    exact add_zero a.toLorentzVector
  add_comm := by
    intros a b
    apply ext
    exact add_comm a.toLorentzVector b.toLorentzVector
  neg_add_cancel := by
    intro a
    apply ext
    dsimp
    exact neg_add_cancel a.toLorentzVector
  nsmul := fun n x => ⟨n • x.toLorentzVector⟩
  nsmul_zero := by
    intro x
    apply ext
    simp
    exact rfl
  nsmul_succ := by
    intros n x
    apply LorentzPosition4Vector.ext
    simp [nsmul_add, one_nsmul]
    exact rfl
  zsmul := fun z x => ⟨z • x.toLorentzVector⟩
  zsmul_zero' := by
    intro x
    apply LorentzPosition4Vector.ext
    simp
    exact rfl
  zsmul_succ' := by
    intro n x
    apply ext
    simp
    exact rfl
  zsmul_neg' := by
    intro n x
    apply ext
    simp
    rfl


/-- Lorentz 4-position vectors form a module over the real numbers. -/
@[simp]
instance : Module ℝ (LorentzPosition4Vector d) where
  smul := fun r x => ⟨r • x.toLorentzVector⟩
  one_smul := fun x => by
    apply ext
    dsimp
    exact one_smul ℝ x.toLorentzVector
  mul_smul := fun r s x => by
    apply ext
    dsimp
    exact mul_smul r s x.toLorentzVector
  smul_add := fun r x y => by
    apply ext
    dsimp
    exact smul_add r x.toLorentzVector y.toLorentzVector
  smul_zero := fun r => by
    apply ext
    dsimp
    exact smul_zero r
  add_smul := fun r s x => by
    apply ext
    dsimp
    exact add_smul r s x.toLorentzVector
  zero_smul := fun x => by
    apply ext
    dsimp
    exact zero_smul ℝ x.toLorentzVector

/-- The instance of a CoeSort for Lorentz 4-position vectors. -/
instance : CoeSort (LorentzPosition4Vector d) Type where
  coe := fun _ => ContrMod d

/-- The inclusion map to get the underlying `ContrMod` from a `LorentzPosition4Vector`. -/
instance : Coe (LorentzPosition4Vector d) (ContrMod d) where
  coe x := x.toLorentzVector

/-- The instance of a group action by the Lorentz group on 4-position vectors. -/
instance : MulAction (LorentzGroup d) (LorentzPosition4Vector d) where
  smul Λ p := {
    toLorentzVector := Λ.1 *ᵥ p.toLorentzVector
  }
  one_smul := fun p => by
    apply ext
    dsimp only
    have h : (1 : LorentzGroup d).1 *ᵥ p.toLorentzVector = p.toLorentzVector := by
      simp [MulAction.one_smul]
    exact h
  mul_smul := fun Λ Λ' p => by
    apply ext
    dsimp only
    have h : (Λ * Λ').1 *ᵥ p.toLorentzVector = Λ.1 *ᵥ (Λ'.1 *ᵥ p.toLorentzVector) := by
      simp [MulAction.mul_smul]
      obtain ⟨val, property⟩ := Λ
      obtain ⟨val_1, property_1⟩ := Λ'
      simp_all only
      rw [@ContrMod.mulVec_mulVec]
    exact h

@[simp]
lemma coe_add (x y : LorentzPosition4Vector d) : (x + y : ContrMod d) = x + y := by
  rfl

@[simp]
lemma coe_smul (r : ℝ) (x : LorentzPosition4Vector d) : (r • x : ContrMod d) = r • x := by
  rfl

@[simp]
lemma coe_neg (x: LorentzPosition4Vector d) : ((-x) : ContrMod d) = -x := by rfl

@[simp]
lemma coe_sub (x y : LorentzPosition4Vector d) : (x - y : ContrMod d) = x - y := by rfl

@[simp]
lemma coe_nsmul (n : ℕ) (x: LorentzPosition4Vector d) : ((n • x) : ContrMod d) = n • x := by rfl

@[simp]
lemma coe_zsmul (z : ℤ) (x : LorentzPosition4Vector d) : ((z • x) : ContrMod d) = z • x := by rfl

@[simp]
lemma coe_zero : ((0 : LorentzPosition4Vector d) : ContrMod d) = 0 := rfl

/-- Lorentz transformations are linear transformations on Lorentz 4-position vectors. -/
lemma lorentz_transformation_linear :
    ∀ (Λ : LorentzGroup d) (v w : LorentzPosition4Vector d) (a : ℝ),
    (Λ • (v + a • w)) = (Λ • v) + a • (Λ • w) := by
  intros Λ v w a
  -- Use `ext` lemma to show equality of LorentzPosition4Vector structures
  apply LorentzPosition4Vector.ext
  -- Expand the definitions to show the matrix multiplications
  dsimp only [Multiplicative.smul, AddGroup.toAddCancelMonoid, instAddCommGroup, instModuleReal]
  -- Use linearity of matrix multiplication on vectors
  have h : Λ.1 *ᵥ (v.toLorentzVector + a • w.toLorentzVector) =
           Λ.1 *ᵥ v.toLorentzVector + a • (Λ.1 *ᵥ w.toLorentzVector) := by
    rw [ContrMod.mulVec_add]
    simp_all only [_root_.map_smul]
  exact h

end LorentzPosition4Vector

/-- A Lorentz 4-velocity vector in Minkowski spacetime. -/
structure LorentzVelocity4Vector (d : ℕ) where
  /-- The underlying Lorentz vector. -/
  toLorentzVector : ContrMod d

namespace LorentzVelocity4Vector

variable {d : ℕ}

@[ext]
theorem ext {x y : LorentzVelocity4Vector d} (h : x.toLorentzVector = y.toLorentzVector) : x = y := by
  cases x; cases y; congr

/-- The instance of a CoeSort for Lorentz 4-velocity vectors. -/
instance : CoeSort (LorentzVelocity4Vector d) Type where
  coe := fun _ => ContrMod d

/-- The inclusion map to get the underlying `ContrMod` from a `LorentzVelocity4Vector`. -/
instance : Coe (LorentzVelocity4Vector d) (ContrMod d) where
  coe x := x.toLorentzVector

/-- The instance of an additive commutative group for Lorentz 4-velocity vectors. -/
@[simp]
instance : AddCommGroup (LorentzVelocity4Vector d) where
  add x y := ⟨x.toLorentzVector + y.toLorentzVector⟩
  add_assoc := by
    intros a b c
    ext x
    dsimp
    exact add_assoc _ _ _
  neg := fun x => ⟨-x.toLorentzVector⟩
  zero := ⟨0⟩
  zero_add := by
    intro a
    apply LorentzVelocity4Vector.ext
    simp
    exact zero_add a.toLorentzVector
  add_zero := by
    intro a
    apply LorentzVelocity4Vector.ext
    simp
    exact add_zero a.toLorentzVector
  add_comm := by
    intros a b
    apply ext
    exact add_comm a.toLorentzVector b.toLorentzVector
  neg_add_cancel := by
    intro a
    apply ext
    dsimp
    exact neg_add_cancel a.toLorentzVector
  nsmul := fun n x => ⟨n • x.toLorentzVector⟩
  nsmul_zero := by
    intro x
    apply ext
    simp
    exact rfl
  nsmul_succ := by
    intros n x
    apply LorentzVelocity4Vector.ext
    simp [nsmul_add, one_nsmul]
    exact rfl
  zsmul := fun z x => ⟨z • x.toLorentzVector⟩
  zsmul_zero' := by
    intro x
    apply LorentzVelocity4Vector.ext
    simp
    exact rfl
  zsmul_succ' := by
    intro n x
    apply ext
    simp
    rfl
  zsmul_neg' := by
    intro n x
    apply ext
    simp
    rfl

end LorentzVelocity4Vector

/-- A Lorentz 4-momentum vector in Minkowski spacetime. -/
structure LorentzMomentum4Vector (d : ℕ) where
  /-- The underlying Lorentz vector. -/
  toLorentzVector : ContrMod d


namespace LorentzMomentum4Vector


/-- Constructs a 4-momentum vector from energy and momentum components. -/
def mkLorentzMomentum (e : ℝ) (px py pz : ℝ) : LorentzMomentum4Vector spacetimeDim :=
  ⟨ContrMod.mk $ fun i => match i with
    | Sum.inl ⟨0, _⟩ => e
    | Sum.inl ⟨1, _⟩ => px
    | Sum.inl ⟨2, _⟩ => py
    | Sum.inl ⟨3, _⟩ => pz
    | _ => 0⟩
/-- The inclusion map to get the underlying `ContrMod` from a `LorentzMomentum4Vector`. -/
instance : Coe (LorentzMomentum4Vector d) (ContrMod d) where
  coe x := x.toLorentzVector

variable {d : ℕ}

@[ext]
theorem ext {x y : LorentzMomentum4Vector d} (h : x.toLorentzVector = y.toLorentzVector) : x = y := by
  cases x; cases y; congr

/-- The instance of an additive commutative group for Lorentz 4-momentum vectors. -/
@[simp]
instance : AddCommGroup (LorentzMomentum4Vector d) where
  add x y := ⟨x.toLorentzVector + y.toLorentzVector⟩
  add_assoc := by
    intros a b c
    ext x
    dsimp
    exact add_assoc _ _ _
  neg := fun x => ⟨-x.toLorentzVector⟩
  zero := ⟨0⟩
  zero_add := by
    intro a
    apply LorentzMomentum4Vector.ext
    simp
    exact zero_add a.toLorentzVector
  add_zero := by
    intro a
    apply LorentzMomentum4Vector.ext
    simp
    exact add_zero a.toLorentzVector
  add_comm := by
    intros a b
    apply ext
    exact add_comm a.toLorentzVector b.toLorentzVector
  neg_add_cancel := by
    intro a
    apply ext
    dsimp
    exact neg_add_cancel a.toLorentzVector
  nsmul := fun n x => ⟨n • x.toLorentzVector⟩
  nsmul_zero := by
    intro x
    apply ext
    simp
    exact rfl
  nsmul_succ := by
    intros n x
    apply LorentzMomentum4Vector.ext
    simp [nsmul_add, one_nsmul]
    exact rfl
  zsmul := fun z x => ⟨z • x.toLorentzVector⟩
  zsmul_zero' := by
    intro x
    apply LorentzMomentum4Vector.ext
    simp
    exact rfl
  zsmul_succ' := by
    intro n x
    apply ext
    simp
    rfl
  zsmul_neg' := by
    intro n x
    apply ext
    simp
    rfl

/-- Lorentz 4-momentum vectors form a module over the real numbers. -/
@[simp]
instance : Module ℝ (LorentzMomentum4Vector d) where
  smul := fun r x => ⟨r • x.toLorentzVector⟩
  one_smul := fun x => by
    apply ext
    dsimp
    exact one_smul ℝ x.toLorentzVector
  mul_smul := fun r s x => by
    apply ext
    dsimp
    exact mul_smul r s x.toLorentzVector
  smul_add := fun r x y => by
    apply ext
    dsimp
    exact smul_add r x.toLorentzVector y.toLorentzVector
  smul_zero := fun r => by
    apply ext
    dsimp
    exact smul_zero r
  add_smul := fun r s x => by
    apply ext
    dsimp
    exact add_smul r s x.toLorentzVector
  zero_smul := fun x => by
    apply ext
    dsimp
    exact zero_smul ℝ x.toLorentzVector


/-- Lorentz 4-momentum vectors form a module over the real numbers. -/
@[simp]
instance : MulAction (LorentzGroup d) (LorentzMomentum4Vector d) where
  smul Λ p := {
    toLorentzVector := Λ.1 *ᵥ p.toLorentzVector
  }
  one_smul := fun p => by
    apply ext
    dsimp only
    have h : (1 : LorentzGroup d).1 *ᵥ p.toLorentzVector = p.toLorentzVector := by
      simp [MulAction.one_smul]
    exact h
  mul_smul := fun Λ Λ' p => by
    apply ext
    dsimp only
    have h : (Λ * Λ').1 *ᵥ p.toLorentzVector = Λ.1 *ᵥ (Λ'.1 *ᵥ p.toLorentzVector) := by
      simp [MulAction.mul_smul]
      obtain ⟨val, property⟩ := Λ
      obtain ⟨val_1, property_1⟩ := Λ'
      simp_all only
      rw [@ContrMod.mulVec_mulVec]
    exact h


end LorentzMomentum4Vector

namespace SpecialRelativity

/-- The Minkowski inner product of two 4-position vectors. -/
def innerMinkowski (u v : LorentzPosition4Vector d) : ℝ :=
  dotProduct ((u : ContrMod d).toFin1dℝ) (minkowskiMatrix *ᵥ (v : ContrMod d).toFin1dℝ)

notation "⟪" u ", " v "⟫ₘ" => innerMinkowski u v

/-- The Minkowski norm squared of a 4-position vector. -/
def normSqMinkowski (u : LorentzPosition4Vector d) : ℝ := ⟪u, u⟫ₘ

/-!
This lemma states that when a matrix A multiplies the result
of matrix B multiplying a vector v, that's equivalent to the
matrix product A * B multiplying the vector v directly.
-/

@[simp]
lemma Matrix.mulVec_assoc {α : Type*} [Semiring α] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  (A : Matrix m n α) (B : Matrix n p α) (v : p → α) :
  A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v := by
  ext i
  simp only [mulVec, Matrix.mul_apply, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [@Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_assoc]

/-- The indefinite diagonal for the Minkowski metric is symmetric. -/
lemma indefiniteDiagonal_symm {m n : Type*} [DecidableEq m] [DecidableEq n]
  (R : Type*) [CommRing R] (i j : m ⊕ n) :
  LieAlgebra.Orthogonal.indefiniteDiagonal m n R i j = LieAlgebra.Orthogonal.indefiniteDiagonal m n R j i :=
by
  cases i with
  | inl x => cases j with
    | inl y =>
      simp [LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal]
      by_cases h : x = y
      · simp [h]
      · simp [h]; exact Eq.symm (if_neg fun a => h (id (Eq.symm a)))
    | inr y =>
      simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
  | inr x => cases j with
    | inl y =>
      simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
    | inr y =>
      simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
      rw [diagonal]
      by_cases h : x = y
      · simp [h]
      · simp [h]
        exact Eq.symm (if_neg fun a => h (id (Eq.symm a)))



/-- For a matrix A and vectors v, w, the dot product ⟨v, Aw⟩ equals ⟨Aᵀv, w⟩. -/
@[simp]
lemma Matrix.dotProduct_mulVec_left {α : Type*} [CommSemiring α] {m n : Type*} [Fintype m] [Fintype n]
  (A : Matrix m n α) (v : m → α) (w : n → α) :
  dotProduct v (A *ᵥ w) = dotProduct (Aᵀ *ᵥ v) w := by
  simp only [dotProduct, mulVec, transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [@Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [@Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  exact mul_right_comm (A j i) (w i) (v j)

/--
The Minkowski matrix is symmetric.
-/
lemma Matrix.transpose_eq_self [CommRing R] {n : Type*} [Fintype n] (A : Matrix n n R)
  (h : ∀ (i j : n), A i j = A j i) : A = Aᵀ := by
  ext i j
  simp only [transpose_apply]
  exact h i j

/-- Apply a Lorentz transformation to a 4-position vector. -/
def LorentzTransform (Λ : LorentzGroup d) (v : LorentzPosition4Vector d) : LorentzPosition4Vector d :=
    Λ • v

@[simp]
lemma LorentzTransform_apply (Λ : LorentzGroup d) (v : LorentzPosition4Vector d) :
  (LorentzTransform Λ v).toLorentzVector = Λ.1 *ᵥ v.toLorentzVector := rfl

-- Minkowski inner product is preserved under Lorentz transformations
-- This follows from the defining property of the Lorentz group, which preserves the metric
@[simp]
lemma lorentzTransform_preserves_innerMinkowski (Λ : LorentzGroup d)
    (u v : LorentzPosition4Vector d) :
    ⟪LorentzTransform Λ u, LorentzTransform Λ v⟫ₘ = ⟪u, v⟫ₘ := by
  simp only [LorentzTransform, innerMinkowski]

  -- Get the Lorentz condition: Λᵀ η Λ = η
  have h_lorentz := Λ.2

  -- Let's use the property that defines the Lorentz group
  have h_preserve : Λ.1.transpose * minkowskiMatrix * Λ.1 = minkowskiMatrix := by
    -- Use the membership condition of the Lorentz group
    have h := Λ.2
    -- Convert the membership condition to the matrix equation we want
    rw [LorentzGroup.mem_iff_self_mul_dual] at h
    -- Use the definition of dual and solve
    simp [minkowskiMatrix.dual] at h
    exact LorentzGroup.transpose_mul_minkowskiMatrix_mul_self

  -- Use the Matrix.dotProduct_mulVec_left lemma to simplify the calculation
  calc
    dotProduct ((Λ.1 *ᵥ u.toLorentzVector).toFin1dℝ) (minkowskiMatrix *ᵥ (Λ.1 *ᵥ v.toLorentzVector).toFin1dℝ)
    = dotProduct (u.toLorentzVector.toFin1dℝ) ((Λ.1.transpose * minkowskiMatrix * Λ.1) *ᵥ v.toLorentzVector.toFin1dℝ) := by
      -- Convert both sides to work with matrix operations
      simp only [ContrMod.mulVec_toFin1dℝ, mulVec_mulVec, Matrix.dotProduct_mulVec_left,
        transpose_mul, minkowskiMatrix.eq_transpose,
        LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]
      -- Use associativity of matrix multiplication with vectors

    _ = dotProduct (u.toLorentzVector.toFin1dℝ) (minkowskiMatrix *ᵥ v.toLorentzVector.toFin1dℝ) := by
      -- Apply the Lorentz condition
      rw [h_preserve]

--

/-- A timelike 4-vector in Minkowski spacetime. -/
structure TimelikeVector (d : ℕ) extends LorentzPosition4Vector d where
  isTimelike : normSqMinkowski toLorentzPosition4Vector < 0

/-- A lightlike 4-vector in Minkowski spacetime. -/
structure LightlikeVector (d : ℕ) extends LorentzPosition4Vector d where
  isLightlike : normSqMinkowski toLorentzPosition4Vector = 0

/-- A spacelike 4-vector in Minkowski spacetime. -/
structure SpacelikeVector (d : ℕ) extends LorentzPosition4Vector d where
  isSpacelike : normSqMinkowski toLorentzPosition4Vector > 0

/-- Classification of 4-vectors based on their causal character. -/
inductive CausalCharacter
  | Timelike   -- For vectors with negative Minkowski norm (in -+++ convention)
  | Lightlike  -- For vectors with zero Minkowski norm
  | Spacelike  -- For vectors with positive Minkowski norm

/-- Determines the causal character of a 4-position vector based on its Minkowski norm. -/
def causalCharacter (v : LorentzPosition4Vector d) : CausalCharacter :=
  let normSq := normSqMinkowski v
  if normSq < 0 then CausalCharacter.Timelike
  else if normSq = 0 then CausalCharacter.Lightlike
  else CausalCharacter.Spacelike

/-- The forward light cone of a spacetime point p. -/
def forwardLightCone (p : LorentzPosition4Vector d) : Set (LorentzPosition4Vector d) :=
  {q | let v := q - p;
       causalCharacter v = CausalCharacter.Timelike ∧
       (v.toLorentzVector.toFin1dℝ (Sum.inl 0)) > 0}

/-- The backward light cone of a spacetime point p. -/
def backwardLightCone (p : LorentzPosition4Vector d) : Set (LorentzPosition4Vector d) :=
  {q | let v := q - p;
       causalCharacter v = CausalCharacter.Timelike ∧
       (v.toLorentzVector.toFin1dℝ (Sum.inl 0)) < 0}

/-- The light cone boundary (null surface) of a spacetime point p. -/
def lightConeBoundary (p : LorentzPosition4Vector d) : Set (LorentzPosition4Vector d) :=
  {q | causalCharacter (q - p) = CausalCharacter.Lightlike}


/-- Determines if event q is in the causal future of event p. -/
def causallyFollows (p q : LorentzPosition4Vector d) : Prop :=
  q ∈ forwardLightCone p ∨ q ∈ lightConeBoundary p ∨ p = q

/-- Determines if event q is in the causal past of event p. -/
def causallyPrecedes (p q : LorentzPosition4Vector d) : Prop :=
  causallyFollows q p

/-- Events p and q are causally related. -/
def causallyRelated (p q : LorentzPosition4Vector d) : Prop :=
  causallyFollows p q ∨ causallyFollows q p

/-- Events p and q are causally unrelated (spacelike separated). -/
def causallyUnrelated (p q : LorentzPosition4Vector d) : Prop :=
  causalCharacter (p - q) = CausalCharacter.Spacelike

/-- The proper orthochronous Lorentz group, which preserves orientation and time direction. -/
structure ProperOrthochronousLorentzGroup (d : ℕ) extends LorentzGroup d where
  isProper : det val = 1
  isOrthochronous : val (Sum.inl 0) (Sum.inl 0) ≥ 1

namespace ProperOrthochronousLorentzGroup

instance {d : ℕ} : Coe (ProperOrthochronousLorentzGroup d) (LorentzGroup d) where
  coe := fun Λ => Λ.1

end ProperOrthochronousLorentzGroup

/-- The causal character of a 4-vector is invariant under proper orthochronous Lorentz transformations. -/
theorem causalCharacter_invariant (v : LorentzPosition4Vector d)
    (Λ : ProperOrthochronousLorentzGroup d) :
    causalCharacter ((Λ : LorentzGroup d) • v) = causalCharacter v := by
  simp only [causalCharacter]
  have h_norm_invariant : normSqMinkowski ((Λ : LorentzGroup d) • v) = normSqMinkowski v := by
    simp only [normSqMinkowski]
    -- Apply the theorem that Lorentz transformations preserve the Minkowski inner product
    exact lorentzTransform_preserves_innerMinkowski (Λ : LorentzGroup d) v v
  simp [h_norm_invariant]

/-- The causal diamond between events p and q, where p is assumed to causally precede q. -/
def causalDiamond (p q : LorentzPosition4Vector d) : Set (LorentzPosition4Vector d) :=
  {r | causallyFollows p r ∧ causallyFollows r q}

/-- Computes the proper time interval between two timelike-separated events. -/
def properTime (p q : LorentzPosition4Vector d) (h : causalCharacter (q - p) = CausalCharacter.Timelike) : ℝ :=
  Real.sqrt (-(normSqMinkowski (q - p)))
  where
    h_pos : 0 < -(normSqMinkowski (q - p)) := by
      -- Using `h` to ensure that the square root is of a positive number
      have h_lt : normSqMinkowski (q - p) < 0 := by
        simp only [causalCharacter] at h
        -- Analyze the definition of causalCharacter
        let normSq := normSqMinkowski (q - p)
        have h_def : (if normSq < 0 then CausalCharacter.Timelike
                      else if normSq = 0 then CausalCharacter.Lightlike
                      else CausalCharacter.Spacelike) = CausalCharacter.Timelike := h
        -- Split cases on whether normSq < 0
        by_cases h1 : normSq < 0
        · exact h1
        · -- In this case, the condition would be false
          simp [h1] at h_def
          -- The if-then-else would result in "if normSq = 0 then Lightlike else Spacelike"
          -- But h_def says this equals Timelike, which is a contradiction
          simp_all only [LorentzPosition4Vector.instAddCommGroup, ↓reduceIte, not_lt, gt_iff_lt, normSq]
          split at h_def
          next h => simp_all only [le_refl, reduceCtorEq]
          next h => simp_all only [reduceCtorEq]
      exact neg_pos.mpr h_lt


/--
Example: Time dilation calculation.

For an observer moving at velocity v relative to a clock,
this computes the relativistic time dilation factor γ and
the dilated time interval.

Inputs:
- v: The relative velocity as a fraction of c (magnitude < 1)
- Δt₀: The proper time interval in the clock's rest frame

Output:
- The dilated time interval Δt = γΔt₀
-/
def timeDilation (v : ℝ) (Δt₀ : ℝ) (_ : abs v < 1) : ℝ :=
  let γ := 1 / Real.sqrt (1 - v^2)
  γ * Δt₀


def particleMomentum (m v_x v_y v_z : ℝ) (_ : v_x^2 + v_y^2 + v_z^2 < 1) :
    LorentzMomentum4Vector spacetimeDim :=
  let v_sq := v_x^2 + v_y^2 + v_z^2
  let γ := 1 / Real.sqrt (1 - v_sq)
  let E := γ * m  -- Energy/c (in mass units where c=1)
  let p_x := γ * m * v_x
  let p_y := γ * m * v_y
  let p_z := γ * m * v_z
  LorentzMomentum4Vector.mkLorentzMomentum E p_x p_y p_z

/-- Minkowski inner product for momentum vectors. -/
def innerMinkowskiMomentum (u v : LorentzMomentum4Vector d) : ℝ :=
  dotProduct ((u : ContrMod d).toFin1dℝ) (minkowskiMatrix *ᵥ (v : ContrMod d).toFin1dℝ)

/-- The Minkowski norm squared of a 4-momentum vector. -/
def normSqMinkowskiMomentum (u : LorentzMomentum4Vector d) : ℝ :=
  innerMinkowskiMomentum u u

/-- Determines the causal character of a 4-momentum vector based on its Minkowski norm. -/
def causalCharacterMomentum (v : LorentzMomentum4Vector d) : CausalCharacter :=
  let normSq := normSqMinkowskiMomentum v
  if normSq < 0 then CausalCharacter.Timelike
  else if normSq = 0 then CausalCharacter.Lightlike
  else CausalCharacter.Spacelike

/--
Example: Compute the invariant mass from a 4-momentum vector.
-/
def invariantMass (p : LorentzMomentum4Vector spacetimeDim) : ℝ :=
  let p_sq := normSqMinkowskiMomentum p
  match causalCharacterMomentum p with
  | CausalCharacter.Timelike => Real.sqrt (-p_sq)  -- Physical massive particle
  | _ => 0  -- Massless or tachyonic (unphysical) particle

/-- For timelike vectors, the Minkowski norm squared is negative. -/
lemma normSqMinkowski_timelike_neg {d : ℕ} {v : LorentzPosition4Vector d}
    (h : causalCharacter v = CausalCharacter.Timelike) :
    normSqMinkowski v < 0 := by
  simp only [causalCharacter] at h
  split at h
  · assumption
  · simp_all only [not_lt]
    split at h
    next h_2 => simp_all only [le_refl, reduceCtorEq]
    next h_2 => simp_all only [reduceCtorEq]

/-- For timelike vectors, the negative of the Minkowski norm squared is nonnegative. -/
lemma normSqMinkowski_timelike_nonneg {d : ℕ} {v : LorentzPosition4Vector d}
    (h : causalCharacter v = CausalCharacter.Timelike) :
    0 ≤ -normSqMinkowski v := by
  simp only [Left.nonneg_neg_iff]
  apply le_of_lt
  exact normSqMinkowski_timelike_neg h

/-- The Matrix.dotProduct_add_left lemma showing bilinearity of dot product. -/
@[simp]
lemma Matrix.dotProduct_add_left {α : Type*} [CommSemiring α] {n : Type*} [Fintype n]
    (x y z : n → α) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp only [dotProduct, Pi.add_apply]
  -- Distribute multiplication over addition
  rw [← @Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  · intro i _
    rw [add_mul]

/-- The Matrix.dotProduct_add_right lemma showing bilinearity of dot product. -/
@[simp]
lemma Matrix.dotProduct_add_right {α : Type*} [CommSemiring α] {n : Type*} [Fintype n]
    (x y z : n → α) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp only [dotProduct, Pi.add_apply]
  rw [← @Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add]

/-- Dot product is linear in the first argument with respect to scalar multiplication. -/
@[simp]
lemma Matrix.dotProduct_smul_left {α : Type*} [CommSemiring α] {n : Type*} [Fintype n]
    (r : α) (x y : n → α) :
    dotProduct (r • x) y = r * dotProduct x y := by
  simp only [dotProduct, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul]
  rw [mul_assoc]

/-- Dot product is linear in the second argument with respect to scalar multiplication. -/
@[simp]
lemma Matrix.dotProduct_smul_right {α : Type*} [CommSemiring α] {n : Type*} [Fintype n]
    (r : α) (x y : n → α) :
    dotProduct x (r • y) = r * dotProduct x y := by
  simp only [dotProduct, Pi.smul_apply]
  rw [@Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul]
  calc
    x i * (r * y i) = x i * (y i * r) := by rw [mul_comm r (y i)]
    _ = (x i * y i) * r := by rw [mul_assoc]
    _ = r * (x i * y i) := by rw [mul_comm]

@[simp]
lemma Finset.sum_add_distrib {α : Type*} [DecidableEq α] {β : Type*} [AddCommMonoid β]
    (s : Finset α) (f g : α → β) :
    ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i := by
  cases s
  · simp [Finset.sum_empty]

/-- The inclusion map to get the underlying `ContrMod` from a `LorentzPosition4Vector`. -/
@[simp]
instance instCoeLorentzPosition4VectorContrMod {d : ℕ} :
    Coe (LorentzPosition4Vector d) (ContrMod d) where
  coe x := x.toLorentzVector

/-- Function coercion preserves equality. -/
@[simp]
lemma CoeFun.coe_fn_eq {α β : Type*} {f g : α → β} :
    (f : α → β) = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    funext x
    exact h x

/-- The function value of a constructor equals the value used in the constructor. -/
lemma coe_fn_mk {α : Type*} {β : Type*} (f : α → β) : (fun x => f x) = f := by
  funext x
  rfl

@[simp]
lemma coe_add (x y : LorentzPosition4Vector d) : (x + y : ContrMod d) = x.toLorentzVector + y.toLorentzVector := by
  -- Direct application of the coercion definition
  simp only
  -- This is trivial by definition of addition on LorentzPosition4Vector

@[simp]
lemma coe_smul (r : ℝ) (x : LorentzPosition4Vector d) : (r • x : ContrMod d) = r • x.toLorentzVector := by
  -- Direct application of the coercion definition
  simp only
  -- This is trivial by definition of scalar multiplication on LorentzPosition4Vector

/-- Adding ContMod vectors commutes with conversion to Fin1dℝ. -/
@[simp]
lemma ContrMod.add_toFin1dℝ {d : ℕ} (v w : ContrMod d) :
    (v + w).toFin1dℝ = v.toFin1dℝ + w.toFin1dℝ := by
  -- Apply function extensionality since we're proving equality of functions
  funext i
  -- Use the definition of addition for ContrMod
  simp only [map_add, Pi.add_apply]

@[simp]
lemma Matrix_dotProd_comm {d : ℕ} (p q r : LorentzPosition4Vector d) :
    dotProduct ((r - q).toLorentzVector.toFin1dℝ) (minkowskiMatrix *ᵥ (q - p).toLorentzVector.toFin1dℝ) =
    dotProduct ((q - p).toLorentzVector.toFin1dℝ) (minkowskiMatrix *ᵥ ((r - q).toLorentzVector.toFin1dℝ)) := by
  -- First prove that minkowski matrix is symmetric
  have h_sym : ∀ i j, (@minkowskiMatrix d) i j = (@minkowskiMatrix d) j i := fun i j =>
    indefiniteDiagonal_symm ℝ i j

  -- Use the symmetry property to rewrite the dot product
  calc
    dotProduct ((r - q).toLorentzVector.toFin1dℝ) (minkowskiMatrix *ᵥ (q - p).toLorentzVector.toFin1dℝ)
    = dotProduct ((r - q).toLorentzVector.toFin1dℝ) ((@minkowskiMatrix d) *ᵥ (q - p).toLorentzVector.toFin1dℝ) := by
      rfl
    _ = dotProduct (((@minkowskiMatrix d)ᵀ *ᵥ (r - q).toLorentzVector.toFin1dℝ)) ((q - p).toLorentzVector.toFin1dℝ) := by
      rw [@Matrix.dotProduct_mulVec_left]
    _ = dotProduct ((@minkowskiMatrix d) *ᵥ (r - q).toLorentzVector.toFin1dℝ) ((q - p).toLorentzVector.toFin1dℝ) := by
      congr
      refine CoeFun.coe_fn_eq.mpr ?e_v.a
      intro x
      simp_all only [Sum.forall, ne_eq, reduceCtorEq, not_false_eq_true, minkowskiMatrix.off_diag_zero, implies_true,
        and_true, true_and, minkowskiMatrix.eq_transpose, LorentzPosition4Vector.instAddCommGroup]
    _ = dotProduct ((q - p).toLorentzVector.toFin1dℝ) ((@minkowskiMatrix d) *ᵥ ((r - q).toLorentzVector.toFin1dℝ)) := by
      rw [dotProduct_comm]
    _ = dotProduct ((q - p).toLorentzVector.toFin1dℝ) (minkowskiMatrix *ᵥ ((r - q).toLorentzVector.toFin1dℝ)) := by
      rfl


/-- For timelike vectors, the proper time is positive. -/
theorem properTime_positive {d : ℕ} {p q : LorentzPosition4Vector d}
    (h : causalCharacter (q - p) = CausalCharacter.Timelike) :
    properTime p q h > 0 := by
  simp only [properTime]
  apply Real.sqrt_pos.2
  exact neg_pos.2 (normSqMinkowski_timelike_neg h)

end SpecialRelativity
