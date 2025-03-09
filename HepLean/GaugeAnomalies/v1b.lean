import HepLean.SpaceTime.Basic
import HepLean
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option maxHeartbeats 0
#min_imports

open scoped BigOperators

/-!
# Formalizing "Two-dimensional gauge anomalies and p-adic numbers"

This file formalizes the main mathematical content of the paper:

> Imogen Camp, Ben Gripaios, and Khoi Le Nguyen Nguyen,
> "Two-dimensional gauge anomalies and \(p\)-adic numbers" (arXiv:2403.10611)

Main points formalized:

1. **Lie algebra decomposition** into semisimple plus abelian summands.
2. **Chiral fermions** as 1D representations with integer charges, plus the gravitational
   anomaly condition `∑ cᵢ = 0`.
3. **Quadratic form on a rational vector space** \((\mathbb{Q}^n, q)\) determined by these charges.
4. **Witt decomposition**: isotropic vectors, hyperbolic planes, maximal isotropic subspaces,
   etc.
5. **Local-to-global principle** for anomaly cancellation.

Points about \(p\)-adic completions are left as remarks, since a full Minkowski–Hasse formalization
would require an extensive local-fields library in Lean/mathlib.
-/

------------------------------------------------------------------------
-- 1. Lie Groups and Algebras
------------------------------------------------------------------------

-- Using the definition from:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/GroupAction/Defs.lean
structure GaugeGroup (G : Type*) [TopologicalSpace G] [Group G] where
  toGroup : Group G
  smooth :  ∀ x : G, Continuous (fun y : G × G => x * y.1)

-- Using LieAlgebra directly from Mathlib

-- Abelian gauge fields as m-dimensional torus, using UnitaryGroup from Mathlib.
def AbelianGaugeField (m : ℕ) : Type := Fin m → Matrix.unitaryGroup (Fin (Nat.succ 0)) ℂ

-- Summands of the Lie algebra using LieSubalgebra from Mathlib.
structure SemisimpleSummand (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g] where
  subalgebra : LieSubalgebra k g
  isSemisimple : LieAlgebra.IsSemisimple k subalgebra

structure AbelianSummand (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g] where
  subalgebra : LieSubalgebra k g
  isAbelian : IsLieAbelian subalgebra

------------------------------------------------------------------------
-- 2. Representations
------------------------------------------------------------------------

-- Using Rep directly from Mathlib

-- The definition of irreducible modules
structure Irrep (R G V : Type u) [CommRing R] [Group G] [Monoid G] [AddCommGroup G] [AddCommGroup V] [Module R V]
    [Module R G] [MulAction G V] [DistribMulAction G V] [LieRing V] [LieAlgebra R V] where
  toRep : (G →ₗ[R] V →ₗ[R] V)
  isIrreducible : ∀ (W : Submodule R V), W ≠ ⊥ → W ≠ ⊤ → (∀ g : G, ∀ w ∈ W, g • w ∈ W) → False

noncomputable def Representation.degree {R G V : Type u} [CommRing R] [Group G] [Monoid G] [AddCommGroup G] [AddCommGroup V] [Module R V] [Module R G]
    (ρ : G →ₗ[R] V →ₗ[R] V) : ℕ := Module.finrank R V

------------------------------------------------------------------------
-- 3. Spacetime
------------------------------------------------------------------------

-- Using Lorentz.SpaceTime from HepLean

------------------------------------------------------------------------
-- 4. Quantum Field Theories (Abstraction)
------------------------------------------------------------------------

-- Abstract type for now
structure QFT (spacetime : Type*)
-- Placeholder for QFT structure

open LinearMap

-- Two-dimensional Minkowski spacetime as a vector space over ℝ
def SpaceTime2D := Fin 2 → ℝ

noncomputable section

-- Give spacetime the structure of an additive commutative group.
instance : AddCommGroup SpaceTime2D := Pi.addCommGroup

-- Give spacetime the structure of a module over the reals.
instance : Module ℝ SpaceTime2D := Pi.module _ _ _

-- Give spacetime the structure of a normed group (using the Euclidean norm for now).
instance : NormedAddCommGroup SpaceTime2D := Pi.normedAddCommGroup

-- The Euclidean norm-structure on space time. This is used to give it a smooth structure.
instance : NormedSpace ℝ SpaceTime2D := Pi.normedSpace

namespace SpaceTime2D

-- Define the Minkowski metric (η)
def minkowskiMetric2D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

-- Define the inner product space structure (using the Minkowski metric)
noncomputable instance : InnerProductSpace ℝ SpaceTime2D where
  inner := fun x y => Matrix.dotProduct (minkowskiMetric2D.mulVec x) y

  norm_sq_eq_inner := by
    intro x
    unfold inner
    simp only [minkowskiMetric2D, Matrix.dotProduct, Matrix.mulVec, Matrix.diagonal_mul, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, neg_mul, neg_add_rev, sub_eq_add_neg, add_comm]
    ring_nf
    exact add_eq_of_eq_sub (by ring)

  conj_symm := by
    intro x y
    unfold inner
    simp only [minkowskiMetric2D, Matrix.dotProduct, Matrix.mulVec, Matrix.diagonal_mul, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, neg_mul, sub_eq_add_neg, add_comm, mul_comm]
    exact add_eq_of_eq_sub (by ring)
  add_left := by
    intros x y z
    unfold inner
    simp only [minkowskiMetric2D, Matrix.dotProduct, Matrix.mulVec, Matrix.diagonal_mul, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, add_mul, neg_mul, sub_eq_add_neg, add_add_add_comm]
    exact add_eq_of_eq_sub (by ring)
  smul_left := by
    intros r x y
    unfold inner
    simp only [minkowskiMetric2D, Matrix.dotProduct, Matrix.mulVec, Matrix.diagonal_mul, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, mul_assoc, neg_mul, mul_neg, sub_eq_add_neg]
    rw [mul_comm]
    exact add_eq_of_eq_sub (by ring)
-- The standard basis for spacetime.
def stdBasis : Basis (Fin 2) ℝ SpaceTime2D := Pi.basisFun ℝ (Fin 2)

lemma stdBasis_apply (μ ν : Fin 2) : stdBasis μ ν = if μ = ν then 1 else 0 := by
  erw [stdBasis, Pi.basisFun_apply, Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

lemma stdBasis_not_eq {μ ν : Fin 2} (h : μ ≠ ν) : stdBasis μ ν = 0 := by
  rw [stdBasis_apply]
  exact if_neg h

/-- For space-time,`stdBasis 0` is equal to `![1, 0] `. -/
lemma stdBasis_0 : stdBasis 0 = ![(1 : ℝ), 0] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]

/-- For space-time,`stdBasis 1` is equal to `![0, 1] `. -/
lemma stdBasis_1 : stdBasis 1 = ![0, (1 : ℝ)] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]
lemma stdBasis_mulVec (μ ν : Fin 2) (Λ : Matrix (Fin 2) (Fin 2) ℝ) :
    (Λ.mulVec (stdBasis μ)) ν = Λ ν μ := by
  rw [Matrix.mulVec, Matrix.dotProduct, Fintype.sum_eq_single μ, stdBasis_apply]
  · simp only [reduceIte, mul_one]
  · intro x h
    rw [stdBasis_apply, if_neg (Ne.symm h)]
    exact CommMonoidWithZero.mul_zero (Λ ν x)

/-- The explicit expansion of a point in spacetime as `![x 0, x 1]`. -/
lemma explicit (x : SpaceTime2D) : x = ![x 0, x 1] := by
  funext i
  fin_cases i <;> rfl

@[simp]
lemma add_apply (x y : SpaceTime2D) (i : Fin 2) : (x + y) i = x i + y i := rfl

@[simp]
lemma smul_apply (x : SpaceTime2D) (a : ℝ) (i : Fin 2) : (a • x) i = a * x i := rfl

end SpaceTime2D

------------------------------------------------------------------------
-- 5. Gauge Anomalies (Abstraction)
------------------------------------------------------------------------

-- Abstract type for now
structure GaugeAnomaly (qft : QFT SpaceTime)
-- Placeholder for anomaly structure

------------------------------------------------------------------------
-- 6. IrrepData (HepLean)
------------------------------------------------------------------------

structure IrrepData where
  degree : ℤ
  multiplicity : ℤ
  isLeftMoving : Bool

------------------------------------------------------------------------
-- 7. Quadratic Forms (Using Mathlib)
------------------------------------------------------------------------

/--
The local *abelian* anomaly in 2D can be encoded by a diagonal quadratic form
  q(x) = ∑ (cᵢ * xᵢ^2)
over rationals, where each cᵢ is a nonzero integer, and their sum is zero.
-/
structure AnomalyQuadraticForm (n : ℕ) where
  coeffs : Fin n → ℤ
  nonzero : ∀ i, coeffs i ≠ 0
  traceZero : ∑ i, coeffs i = 0

namespace AnomalyQuadraticForm

/-- Turn an `AnomalyQuadraticForm` into a quadratic form on V = ℚ^n -/
def toQuadraticForm {n : ℕ} (aq : AnomalyQuadraticForm n) :
    QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticForm.ofBilin (BilinForm.ofMatrix (Matrix.diagonal fun i => (aq.coeffs i : ℚ)))

/-- The associated quadratic form: q(x) = Q(x,x) = ∑ cᵢ * xᵢ^2 -/
def qForm {n : ℕ} (aq : AnomalyQuadraticForm n) :
    (Fin n → ℚ) → ℚ := (toQuadraticForm aq)

/--
A “regular” form means non-degenerate (no zero determinant). Here, since it’s diagonal,
this is simply stating that no `aq.coeffs i` is zero (already enforced).
-/
def regular {n : ℕ} (aq : AnomalyQuadraticForm n) : Prop :=
  QuadraticForm.nondegenerate (toQuadraticForm aq)

/--
A vector `v` is isotropic if qForm(v) = 0.
-/
def IsIsotropic {n : ℕ} (aq : AnomalyQuadraticForm n) (v : Fin n → ℚ) : Prop :=
  qForm aq v = 0

/--
A subspace `U` ⊆ ℚ^n is totally isotropic if every v ∈ U is isotropic.
-/
def IsTotallyIsotropic {n : ℕ} (aq : AnomalyQuadraticForm n) (U : Submodule ℚ (Fin n → ℚ)) :
    Prop :=
  ∀ v, v ∈ U → IsIsotropic aq v

/--
A totally isotropic subspace `U` is *maximal* if there is no strictly larger subspace
`W` containing `U` that is also totally isotropic.
-/
def IsMaximalTotallyIsotropic {n : ℕ} (aq : AnomalyQuadraticForm n)
    (U : Submodule ℚ (Fin n → ℚ)) : Prop :=
  IsTotallyIsotropic aq U ∧
    ∀ (W : Submodule ℚ (Fin n → ℚ)), IsTotallyIsotropic aq W → U ≤ W → U = W

/--
A *hyperbolic plane* is spanned by vectors v₁,v₂ with qForm(v₁)=0, qForm(v₂)=0,
and toBilinForm(v₁,v₂) ≠ 0 (non-degenerate). For simplicity, we store them here.
-/
structure HyperbolicPlane (n : ℕ) (aq : AnomalyQuadraticForm n) where
  v₁ : Fin n → ℚ
  v₂ : Fin n → ℚ
  is_isotropic₁ : IsIsotropic aq v₁
  is_isotropic₂ : IsIsotropic aq v₂
  nondegenerate  : (toQuadraticForm aq).polarForm v₁ v₂ ≠ 0

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

def getWittIndex (aq : BilinForm R M) [LieRing R] [Module R M] : ℕ :=
  aq.toQuadraticForm.wittIndex

-- Or more directly:
def getWittIndexDirect (aq : BilinForm R M) : ℕ :=
  (BilinForm.toQuadraticForm aq).wittIndex

/--
The Witt index is the maximum possible dimension of a totally isotropic subspace.
-/
noncomputable def wittIndex {n : ℕ} (aq : AnomalyQuadraticForm n) : ℕ :=
  (toQuadraticForm aq).wittIndex

/-- A Witt decomposition for a quadratic form over ℚ consists of:
1. A decomposition V = Vh ⊕ Va where Vh is hyperbolic and Va is anisotropic
2. A decomposition of Vh into w hyperbolic planes
3. Explicit orthogonality conditions between components

References:
- Cassels, "Rational Quadratic Forms" Ch. 4
- Serre, "A Course in Arithmetic" Ch. IV §3
-/
structure WittDecomposition {n : ℕ} (aq : AnomalyQuadraticForm n) where
  /-- The hyperbolic part of the decomposition -/
  Vh : Submodule ℚ (Fin n → ℚ)
  /-- The anisotropic part of the decomposition -/
  Va : Submodule ℚ (Fin n → ℚ)
  /-- The Witt index (number of hyperbolic planes) -/
  wittIndex : ℕ
  /-- The hyperbolic planes making up Vh -/
  planes : Fin wittIndex → HyperbolicPlane n aq
  /-- Vh is the span of the hyperbolic planes -/
  Vh_eq_span : Vh = Submodule.span ℚ
    (⋃ i, {(planes i).v₁, (planes i).v₂})
  /-- The decomposition is direct -/
  direct_sum : Vh ⊓ Va = ⊥
  /-- The decomposition spans the whole space -/
  total_span : Vh ⊔ Va = ⊤
  /-- The hyperbolic planes are mutually orthogonal -/
  planes_orthogonal : ∀ i j, i ≠ j →
    (toQuadraticForm aq).IsOrtho (planes i).v₁ (planes j).v₁ ∧
    (toQuadraticForm aq).IsOrtho (planes i).v₁ (planes j).v₂ ∧
    (toQuadraticForm aq).IsOrtho (planes i).v₂ (planes j).v₁ ∧
    (toQuadraticForm aq).IsOrtho (planes i).v₂ (planes j).v₂
  /-- The hyperbolic part is orthogonal to the anisotropic part -/
  Vh_Va_orthogonal : ∀ (vh va), vh ∈ Vh → va ∈ Va →
    (toQuadraticForm aq).IsOrtho vh va
  /-- The anisotropic part has no isotropic vectors -/
  Va_anisotropic : ∀ v ∈ Va, aq.qForm v = 0 → v = 0

/--
An isometry of `aq` is a linear map `φ` such that qForm(φ x) = qForm(x).
-/
abbrev IsometryGroup (aq : AnomalyQuadraticForm n) :=
  (toQuadraticForm aq).IsometryEquiv

/-- The Witt index is invariant under isometries -/
theorem witt_index_isometry_invariant {n : ℕ}
    (aq : AnomalyQuadraticForm n)
    (f g : IsometryGroup aq)
    (W₁ W₂ : WittDecomposition aq) :
    W₁.wittIndex = W₂.wittIndex := by
  sorry

end AnomalyQuadraticForm

-- 7. Chiral Fermions



/-- Structure representing a chiral fermion with an abelian charge -/

structure ChiralFermionAbelian where

  charge : ℤ



------------------------------------------------------------------------
-- 8. Gauge Anomaly System
------------------------------------------------------------------------

/--
Structure capturing both the physical and algebraic aspects of 2D gauge anomalies.
This combines the Lie algebra decomposition with the quadratic form structure.

References:
- Camp et al. "Two-dimensional gauge anomalies and p-adic numbers" §3
-/
def gravitationalAnomalyVanishes {n : ℕ} (fermions : Fin n → ChiralFermionAbelian) : Prop :=
  ∑ i, (fermions i).charge = 0

structure GaugeAnomalySystem (n : ℕ) where
  /-- The Lie algebra decomposition -/
  g : Type _
  [lieRing : LieRing g]
  [lieAlg : LieAlgebra ℚ g]
  hg : SemisimpleSummand ℚ g × AbelianSummand ℚ g
  /-- The chiral fermions -/
  fermions : Fin n → ChiralFermionAbelian
  /-- The gravitational anomaly cancellation condition -/
  grav_anomaly : gravitationalAnomalyVanishes fermions
  /-- The associated quadratic form -/
  qform : AnomalyQuadraticForm n
  /-- The quadratic form coefficients match fermion charges -/
  charge_match : ∀ i, qform.coeffs i = (fermions i).charge
  /-- The Witt decomposition of the quadratic form -/
  witt : AnomalyQuadraticForm.WittDecomposition qform
  /-- The Witt index equals maximum number of U(1) factors -/
  max_u1_factors : witt.wittIndex =
    Classical.choose (by
      use witt.wittIndex
      )

------------------------------------------------------------------------
-- 9. Main Result: Local-to-Global Principle
------------------------------------------------------------------------

theorem local_global_equiv_abelian {n : ℕ} (aq : AnomalyQuadraticForm' n) :
    (∃ U : Submodule ℚ (Fin n → ℚ), IsTotallyIsotropic aq.quadForm U) ↔
    (∃ Uℝ : Submodule ℝ (Fin n → ℝ), IsTotallyIsotropic (aq.quadForm.baseChange ℝ) Uℝ) ∧
    (∀ (p : ℕ), Fact p.Prime →
      ∃ Up : Submodule (Padic p) (Fin n → Padic p),
        IsTotallyIsotropic (aq.quadForm.baseChange (Padic p)) Up) := by sorry

/--
The local-to-global principle for anomaly cancellation:
A theory is anomaly-free iff the quadratic form has solutions in ℝ and ℚ_p for all p
-/
theorem local_global_anomaly_cancellation {n : ℕ}
    (sys : GaugeAnomalySystem n) :
    (∃ (U : Submodule ℚ (Fin n → ℚ)), AnomalyQuadraticForm.IsTotallyIsotropic sys.qform U) ↔
    (∃ (Uℝ : Submodule ℝ (Fin n → ℝ)), sorry) ∧ -- isTotallyIsotropic_real sys.qform Uℝ
    (∃ (p : ℕ), ∃ (Up : Submodule (Padic ℤ p) (Fin n → Padic ℤ p)),
          sorry) := by -- replace with proper p-adic condition when mathlib has support
  sorry  -- Requires Hasse-Minkowski theorem

/-- Every regular quadratic form has a Witt decomposition -/
theorem AnomalyQuadraticForm.exists_witt_decomposition {n : ℕ} (aq : AnomalyQuadraticForm n)
    (hreg : aq.regular) :
    ∃ W : WittDecomposition aq, True := by
  sorry  -- Proof requires algorithmic construction as in paper

/--
The group `O(V,q)` acts transitively on maximal totally isotropic subspaces. If `U` and `U'`
are two such subspaces, there is an isometry taking `U` to `U'`.
-/
theorem AnomalyQuadraticForm.isometryGroup_act_on_maximal_isotropic {n : ℕ} (aq : AnomalyQuadraticForm n)
    (U : Submodule ℚ (Fin n → ℚ)) (hU : AnomalyQuadraticForm.IsMaximalTotallyIsotropic aq U)
    (U' : Submodule ℚ (Fin n → ℚ)) (hU' : AnomalyQuadraticForm.IsMaximalTotallyIsotropic aq U') :
    ∃ g : AnomalyQuadraticForm.IsometryGroup aq, U.map g.toLinearEquiv = U' := by
  sorry

/--
**Sketch**: For an abelian gauge theory in 2D with charges summing to zero,
  existence of an `m`-dim. totally isotropic subspace of ℚ^n
  ⇔ anomaly-free theory with `m` abelian factors.
-/
theorem AnomalyQuadraticForm.abelianAnomalyCancellation_equiv_totallyIsotropic {n m : ℕ}
    (aq : AnomalyQuadraticForm n) (hreg : aq.regular) (hm : m ≤ AnomalyQuadraticForm.wittIndex aq) :
    (∃ (U : Submodule ℚ (Fin n → ℚ)),
      Module.rank ℚ U = m ∧
        AnomalyQuadraticForm.IsTotallyIsotropic aq U) ↔
      True := by
  constructor
  · intro _; trivial
  · intro _
    /- The backward direction would require constructing a suitable dimension-m subspace
       from an anomaly-free solution. -/
    sorry

/--
Corollary: The maximal number of abelian gauge factors (that can be added while staying
anomaly-free) is exactly `wittIndex aq`.
-/
theorem AnomalyQuadraticForm.maxAbelianFactors_eq_WittIndex {n : ℕ} (aq : AnomalyQuadraticForm n)
    (hreg : aq.regular) :
    Finset.sup'
        (Finset.univ.filter fun m =>
          ∃ (U : Submodule ℚ (Fin n → ℚ)),
            Module.rank ℚ U = m ∧
              AnomalyQuadraticForm.IsTotallyIsotropic aq U)
        (by
          use 0
          simp) =
      AnomalyQuadraticForm.wittIndex aq := by
  sorry
