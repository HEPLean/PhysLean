/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Linters.Sorry
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
/-!

## Complex Lorentz tensors from Real Lorentz tensors

In this module we define the equivariant semi-linear map from real Lorentz tensors to
complex Lorentz tensors.

-/

namespace realLorentzTensor

open Module TensorSpecies
open Tensor
open complexLorentzTensor

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.Color) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

/-- The complexification of the component index of a real Lorentz tensor to
  a complex Lorentz tensor. -/
def _root_.TensorSpecies.Tensor.ComponentIdx.complexify {n} {c : Fin n → realLorentzTensor.Color} :
    ComponentIdx (S := realLorentzTensor) c ≃
      ComponentIdx (S := complexLorentzTensor) (colorToComplex ∘ c) where
  toFun i := fun j => Fin.cast (by
    simp only [repDim_eq_one_plus_dim, Nat.reduceAdd, Function.comp_apply]
    generalize c j = cj
    match cj with
    | .up => rfl
    | .down => rfl) (i j)
  invFun i := fun j => Fin.cast (by
    simp only [Function.comp_apply, repDim_eq_one_plus_dim, Nat.reduceAdd]
    generalize c j = cj
    match cj with
    | .up => rfl
    | .down => rfl) (i j)
  left_inv i := by
    rfl
  right_inv i := by
    rfl

/-- The semilinear map from real Lorentz tensors to complex Lorentz tensors,
  defined through basis. -/
noncomputable def toComplex {n} {c : Fin n → realLorentzTensor.Color} :
    ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c) where
  toFun v := ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v i •
    Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i.complexify
  map_smul' c v := by
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofRealHom_eq_coe,
      Complex.coe_smul]
    rw [Finset.smul_sum]
    congr
    funext i
    rw [smul_smul]
  map_add' c v := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr
    funext i
    simp [add_smul]

lemma toComplex_eq_sum_basis {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v
      (ComponentIdx.complexify.symm i) •
      Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i := by
  simp only [toComplex, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [← Equiv.sum_comp ComponentIdx.complexify]
  rfl

@[simp]
lemma toComplex_eq_zero_iff {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = 0 ↔ v = 0 := by
  rw [toComplex_eq_sum_basis]
  have h1 : LinearIndependent ℂ
      (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)) :=
    Basis.linearIndependent _
  rw [Fintype.linearIndependent_iff] at h1
  constructor
  · intro h
    apply (Tensor.basis (S := realLorentzTensor) c).repr.injective
    ext i
    have h2 := h1 (fun i => ((Tensor.basis c).repr v) (ComponentIdx.complexify.symm i)) h
      i.complexify
    simpa using h2
  · intro h
    subst h
    simp

/-- The map `toComplex` is injective. -/
lemma toComplex_injective {n} (c : Fin n → realLorentzTensor.Color) :
    Function.Injective (toComplex (c := c)) :=
  (injective_iff_map_eq_zero' toComplex).mpr (fun v => toComplex_eq_zero_iff c v)

open Matrix
open MatrixGroups
open complexLorentzTensor
open Lorentz.SL2C in
/-- The map `toComplex` is equivariant. -/
@[sorryful]
lemma toComplex_equivariant {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (Λ : SL(2, ℂ)) :
    Λ • (toComplex v) = toComplex (Lorentz.SL2C.toLorentzGroup Λ • v) := by
  sorry

/-!

## Relation to tensor operations

-/

/-- The `PermCond` condition is preserved under `colorToComplex`. -/
@[simp] lemma permCond_colorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    PermCond (colorToComplex ∘ c) (colorToComplex ∘ c1) σ := by
  refine And.intro h.1 ?_
  intro i
  simpa [Function.comp_apply] using congrArg colorToComplex (h.2 i)

/-- The map `toComplex` commutes with permT. -/
@[sorryful]
lemma permT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (t : ℝT(3, c)) :
    toComplex (permT (S := realLorentzTensor) σ h t)
      =
    permT (S := complexLorentzTensor) σ (permCond_colorToComplex (c := c) (c1 := c1) h)
      (toComplex (c := c) t) := by
  sorry

/-- `colorToComplex` commutes with `Fin.append` (as functions). -/
@[simp]
lemma colorToComplex_append {n m : ℕ}
    (c : Fin n → realLorentzTensor.Color) (c1 : Fin m → realLorentzTensor.Color) :
    (colorToComplex ∘ Fin.append c c1) = Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1) := by
  funext x
  -- breaking down x : Fin (n+m) into left/right parts
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · -- left case: x = castAdd m i
    -- here `simp` should expand `Fin.append` on castAdd
    simp [Fin.append, Function.comp_apply]
  · -- right case: x = natAdd n j
    simp [Fin.append, Function.comp_apply]

/-- `prodT` on the complex side, with colors written as `colorToComplex ∘ Fin.append ...`.
This is `prodT` followed by a cast using `colorToComplex_append`. -/
noncomputable def prodTColorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color} :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ c1) → ℂT(colorToComplex ∘ Fin.append c c1) :=
    fun x y => permT (S := complexLorentzTensor) id (by simp) <|
      prodT (S := complexLorentzTensor) x y

/-- The map `toComplex` commutes with prodT. -/
@[sorryful]
lemma prodT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    (t : ℝT(3, c)) (t1 : ℝT(3, c1)) :
    toComplex (c := Fin.append c c1) (prodT (S := realLorentzTensor) t t1)
      =
    prodTColorToComplex (c := c) (c1 := c1)
      (toComplex (c := c) t) (toComplex (c := c1) t1) := by
  sorry

/-- `τ` commutes with `colorToComplex` on the Lorentz `up/down` colors. -/
@[simp]
lemma tau_colorToComplex (x : realLorentzTensor.Color) :
    (complexLorentzTensor).τ (colorToComplex x) = colorToComplex ((realLorentzTensor).τ x) := by
  cases x <;> rfl

/-- The map `toComplex` commutes with contrT. -/
@[sorryful]
lemma contrT_toComplex {n : ℕ}
    {c : Fin (n + 1 + 1) → realLorentzTensor.Color} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ (realLorentzTensor).τ (c i) = c j) (t : ℝT(3, c)) :
    toComplex (c := c ∘ Pure.dropPairEmb i j) (contrT (S := realLorentzTensor) n i j h t)
      =
    contrT (S := complexLorentzTensor) n i j (by
        simpa [Function.comp_apply] using
          And.intro h.1 (by
            simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
      (toComplex (c := c) t) := by
  sorry

@[simp]
lemma complex_repDim_up :
    (complexLorentzTensor).repDim complexLorentzTensor.Color.up = 4 := rfl

@[simp]
lemma complex_repDim_down :
    (complexLorentzTensor).repDim complexLorentzTensor.Color.down = 4 := rfl

/-- Convert an evaluation index from the real repDim to the complex repDim. -/
def evalIdxToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin ((realLorentzTensor).repDim (c i))) :
    Fin ((complexLorentzTensor).repDim ((colorToComplex ∘ c) i)) :=
  Fin.cast (by
    cases hci : c i with
    | up =>
        simp [hci, colorToComplex, Function.comp_apply, complex_repDim_up]
    | down =>
        simp [hci, colorToComplex, Function.comp_apply, complex_repDim_down]) b

/-- `evalT` on the complex side, but with output colors as `colorToComplex ∘ (c ∘ i.succAbove)`.
Implemented via `permT (σ := id) (by simp)` as a transport. -/
noncomputable def evalTColorToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin ((realLorentzTensor).repDim (c i))) :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ (c ∘ i.succAbove)) :=
  fun t =>
    permT (S := complexLorentzTensor) (σ := (id : Fin n → Fin n))
      (by
        -- transport ((colorToComplex ∘ c) ∘ i.succAbove) and (colorToComplex ∘ (c ∘ i.succAbove))
        simp [Function.comp_apply])
      ((TensorSpecies.Tensor.evalT (S := complexLorentzTensor) (c := (colorToComplex ∘ c))
          i (evalIdxToComplex (c := c) i b)) t)

/-- The map `toComplex` commutes with `evalT`. -/
@[sorryful]
lemma evalT_toComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin ((realLorentzTensor).repDim (c i))) (t : ℝT(3, c)) :
    toComplex (c := c ∘ i.succAbove)
        ((TensorSpecies.Tensor.evalT (S := realLorentzTensor) (c := c) i b) t)
      =
    evalTColorToComplex (c := c) i b (toComplex (c := c) t) := by
  sorry

end realLorentzTensor
