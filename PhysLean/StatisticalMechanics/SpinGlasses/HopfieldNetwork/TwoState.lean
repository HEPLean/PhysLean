
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Vector.Defs
import Init.Data.Vector.Lemmas
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.aux
import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.NeuralNetwork
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.StatisticalMechanics.CanonicalEnsemble.TwoState

import Mathlib.Probability.Kernel.Invariance
import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib

/-!
# Two-state Hopfield networks: Gibbs update and zero-temperature limit

This file builds a general interface for two-state neural networks, provides
three concrete Hopfield-style instances, develops a one-site Gibbs update
kernel, and proves convergence of this kernel to a deterministic zero-temperature
limit as `β → ∞` (equivalently, `T → 0+`).

## Overview

- Abstract typeclass `TwoStateNeuralNetwork` for two-valued activations:
  it exposes distinguished states `σ_pos`, `σ_neg`, a canonical index `θ0` for the
  single threshold parameter, and order data connecting the numeric embedding `m`
  of the two states (`m σ_neg < m σ_pos`).

- Three concrete encodings of (symmetric) Hopfield parameters:
  * `SymmetricBinary R U` with σ = R and activations in {-1, 1}.
  * `SymmetricSignum R U` with σ = Signum (a type-level two-point type).
  * `ZeroOne R U` with σ = R and activations in {0, 1}.

- A scale parameter, pushed along a ring hom `f`:
  * `scale f : ℝ` and its ring-generalization `scaleS f : S`.
    These quantify the numeric gap between `σ_pos` and `σ_neg` in the image of `f`.

- Probabilistic update at positive temperature:
  * `logisticProb x := 1 / (1 + exp(-x))` with basic bounds
    `logisticProb_nonneg` and `logisticProb_le_one`.
  * `probPos f p T s u : ℝ` gives `P(σ_u = σ_pos)` for one Gibbs update, formed from
    logisticProb with argument `(scale f) * f(local field) * β(T)`.

- One-site PMF update (and sweeps):
  * `updPos`, `updNeg`: force a single site to `σ_pos`/`σ_neg`.
  * `gibbsUpdate f p T s u : PMF State` is the one-site Gibbs update.
  * `zeroTempDet p s u` is the deterministic threshold update at `T = 0`.
  * `gibbsSweepAux`, `gibbsSweep`: sequential composition over a list of sites.

- Energy specification abstraction:
  * `EnergySpec` and a simplified `EnergySpec'` bundle together a global energy
    `E` and a local-field `localField` satisfying:
      `f (E p (updPos s u) - E p (updNeg s u))
        = - (scale f) * f (localField p s u)`.
    It follows that:
      `probPos f p T s u = logisticProb (- f(ΔE) * β(T))`
    where `ΔE := E p (updPos s u) - E p (updNeg s u)`.

- Zero-temperature limit:
  * `scale_pos f` shows `scale f > 0` for an injective order-embedding `f`.
  * `zeroTempLimitPMF p s u` is the limiting one-step kernel at `T = 0+`, which:
    - moves deterministically to `updPos` if local field is positive,
    - to `updNeg` if negative,
    - and splits 1/2–1/2 between them on a tie.
  * Main theorem:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`
    states the PMF `gibbsUpdate f p (tempOfBeta b) s u` converges (as `b → ∞`)
    to `zeroTempLimitPMF p s u`, pointwise on states.

## Key definitions and lemmas

- Interfaces and instances:
  * `class TwoStateNeuralNetwork NN`:
    exposes `σ_pos`, `σ_neg`, `θ0`, and ordering data `m σ_neg < m σ_pos`.
  * Instances:
    - `instTwoStateSymmetricBinary` for `SymmetricBinary`,
    - `instTwoStateSignum` for `SymmetricSignum`,
    - `instTwoStateZeroOne` for `ZeroOne`.

- Scaling gadgets:
  * `scale f : ℝ`, `scaleS f : S`:
    gap between the numeric images of `σ_pos` and `σ_neg`.
    Specializations:
      - `scale_binary f = f 2` on `SymmetricBinary`,
      - `scale_zeroOne f = f 1` on `ZeroOne`.

- Gibbs probability and PMFs:
  * `logisticProb` with bounds:
      `logisticProb_nonneg`, `logisticProb_le_one`.
  * `probPos f p T s u`:
      `= logisticProb ((scale f) * f(localField) * β(T))`.
  * `updPos`, `updNeg`: single-site state updates.
  * `gibbsUpdate f p T s u : PMF State`: one-site Gibbs step.
  * `gibbsSweepAux`, `gibbsSweep`: sequential composition over a list of sites.

- Energy view:
  * `EnergySpec`, `EnergySpec'` and the fundamental relation
      `f (E p (updPos s u) - E p (updNeg s u))
        = - (scale f) * f (localField p s u)`.
  * `EnergySpec.probPos_eq_of_energy`:
      re-express `probPos` via the energy difference `ΔE`.

- Convergence to zero temperature:
  * `scale_pos f`: positivity of `scale f` under an injective order embedding.
  * `zeroTempLimitPMF p s u : PMF State`: the `T → 0+` limit kernel.
  * Pointwise convergence on the only two reachable states:
      - `gibbs_update_tends_to_zero_temp_limit_apply_updPos`
      - `gibbs_update_tends_to_zero_temp_limit_apply_updNeg`
    and zero limit on any other target state
      - `gibbs_update_tends_to_zero_temp_limit_apply_other`.
  * Main PMF convergence:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`.

## Typeclass and notation prerequisites

- Base field and order:
  `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`.
- Sites:
  `[DecidableEq U] [Fintype U] [Nonempty U]` for finite networks and
  decidable equality on sites.
- Embeddings for the scale and probabilities:
  - For `scale` and `probPos` we use a typeclass-driven `f` that is simultaneously
    a ring hom (`[RingHomClass F R ℝ]`) and (when needed for convergence)
    an order embedding (`[OrderHomClass F R ℝ]`) with `Function.Injective f`.

- Probability monad:
  uses `PMF` from Mathlib. The constructions are purely discrete.

## Design notes

- The class `TwoStateNeuralNetwork` abstracts the parts of a network used by a
  two-site threshold update: a canonical scalar threshold index `θ0`, the result
  of `fact` at or above threshold (`σ_pos`) and strictly below (`σ_neg`), and
  numeric ordering `m σ_neg < m σ_pos`.
- The concrete Hopfield instances share the same adjacency and `κ2 = 1` setup,
  but differ in the activation alphabet and decoding map `m`.
- The scaling `scale f` is a thin adapter that makes formulas uniform across
  different encodings, so that Gibbs updates depending on `f(local field)` and
  `β(T)` can be stated once for all `NN`.

## Usage

- To run one Gibbs update at site `u`:
  ```
  gibbsUpdate f p T s u : PMF _
  ```
- To sweep a list of sites in order:
  ```
  gibbsSweep order p T f s0 : PMF _
  ```
- If you can provide an `EnergySpec`, then:
  ```
  probPos f p T s u = logisticProb (- f(ΔE) * β(T))
  ```
  where `ΔE = E p (updPos s u) - E p (updNeg s u)`.

- The zero-temperature limit theorem applies once you supply an `f` that is both
  a ring hom and an injective order embedding (via the corresponding typeclasses).

## TODO

- Finish the (commented) section proving reversibility and invariance of the
  random-scan Gibbs kernel w.r.t. the Boltzmann distribution, after adding a
  finite enumeration of states and the necessary summation lemmas.
- Provide convenience embeddings `f : R →+* ℝ` for common `R` (e.g. `R = ℝ`).

-/

open Finset Matrix NeuralNetwork State Constants Temperature Filter Topology
open scoped ENNReal NNReal BigOperators
open NeuralNetwork

--variable {R U σ : Type}
--variable {R U σ : Type*}
universe uR uU uσ

-- We can also parametrize earlier variables with these universes if desired:
variable {R : Type uR} {U : Type uU} {σ : Type uσ}

--variable {R U σ : Type}

/-- A minimal two-point activation alphabet.

This class specifies:
- `σ_pos`: the distinguished “positive” activation,
- `σ_neg`: the distinguished “negative” activation,
- `embed`: a numeric embedding `σ → R` used to interpret activations in the ambient ring `R`.
-/
class TwoPointActivation (R : Type) (σ : Type) where
  /-- Distinguished “positive” activation state. -/
  σ_pos : σ
  /-- Distinguished “negative” activation state. -/
  σ_neg : σ
  /-- Numeric embedding of activation states into the ambient ring `R`. -/
  embed : σ → R

/-- Scale between the two distinguished activations in `σ`, computed in `R` via the embedding.
It is defined as `embed σ_pos - embed σ_neg`. -/
@[simp] def twoPointScale {R σ} [Sub R] [TwoPointActivation R σ] : R :=
  TwoPointActivation.embed (R:=R) (σ:=σ) (TwoPointActivation.σ_pos (R:=R) (σ:=σ)) -
    TwoPointActivation.embed (R:=R) (σ:=σ) (TwoPointActivation.σ_neg (R:=R) (σ:=σ))

/-- Two–state neural networks (abstract interface).

This exposes:
- `σ_pos`, `σ_neg`: the two distinguished activation states,
- `θ0`: a canonical index into the `κ2`-vector of thresholds extracting the scalar threshold,
- facts that `fact` returns `σ_pos` at or above `θ0`, and `σ_neg` strictly below,
- that both `σ_pos` and `σ_neg` satisfy `pact`,
- and an order gap on the numeric embedding `m` (`m σ_neg < m σ_pos`). -/
class TwoStateNeuralNetwork {R U σ}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (NN : NeuralNetwork R U σ) where
  /-- Distinguished “positive” activation state. -/
  σ_pos : σ
  /-- Distinguished “negative” activation state. -/
  σ_neg : σ
  /-- Proof that the two distinguished activation states are distinct. -/
  h_pos_ne_neg : σ_pos ≠ σ_neg
  /-- Canonical index in `κ2 u` selecting the scalar threshold used by `fact`. -/
  θ0 : ∀ u : U, Fin (NN.κ2 u)
  /-- At or above threshold `θ0 u`, `fact` returns `σ_pos`. -/
  h_fact_pos :
    ∀ u (σcur : σ) (net : R) (θ : Vector R (NN.κ2 u)),
      (θ.get (θ0 u)) ≤ net → NN.fact u σcur net θ = σ_pos
  /-- Strictly below threshold `θ0 u`, `fact` returns `σ_neg`. -/
  h_fact_neg :
    ∀ u (σcur : σ) (net : R) (θ : Vector R (NN.κ2 u)),
      net < (θ.get (θ0 u)) → NN.fact u σcur net θ = σ_neg
  /-- `σ_pos` satisfies the activation predicate `pact`. -/
  h_pact_pos : NN.pact σ_pos
  /-- `σ_neg` satisfies the activation predicate `pact`. -/
  h_pact_neg : NN.pact σ_neg
  /-- Numeric embedding separates the two states: `m σ_neg < m σ_pos`. -/
  m_order : NN.m σ_neg < NN.m σ_pos

namespace TwoState
variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
--variable [DecidableEq U] [Fintype U] [Nonempty U]

/-! Concrete network families (three encodings). -/

/-- Helper canonical index for all concrete networks with κ2 = 1. -/
@[inline] def fin0 : Fin 1 := ⟨0, by decide⟩

/-- Standard symmetric Hopfield parameters with activations in {-1,1} (σ = R). -/
def SymmetricBinary (R U : Type) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U R :=
{ Adj := fun u v => u ≠ v
  Ui := Set.univ
  Uo := Set.univ
  Uh := ∅
  hUi := by simp
  hUo := by simp
  hU := by simp
  hhio := by simp
  κ1 := fun _ => 1
  κ2 := fun _ => 1
  pw := fun W => W.IsSymm ∧ ∀ u, W u u = 0
  pact := fun a => a = 1 ∨ a = -1
  fnet := fun u row pred _ => ∑ v, if v ≠ u then row v * pred v else 0
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then 1 else -1
  fout := fun _ a => a
  m := id
  hpact := by
    classical
    intro W _ _ _ θ cur hcur u
    by_cases hth :
        (θ u).get fin0 ≤ ∑ v, if v ≠ u then W u v * cur v else 0
    · simp [pact, fact, fnet, hth]; aesop
    · simp [pact, fact, fnet, hth]; aesop }

/-- Type level two-value signum variant. -/
inductive Signum | pos | neg deriving DecidableEq

instance : Fintype Signum where
  elems := {Signum.pos, Signum.neg}
  complete := by intro x; cases x <;> simp

/-- Symmetric Hopfield parameters with σ = Signum. -/
def SymmetricSignum (R U : Type) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U Signum :=
{ Adj := fun u v => u ≠ v
  Ui := Set.univ
  Uo := Set.univ
  Uh := ∅
  hUi := by simp
  hUo := by simp
  hU := by simp
  hhio := by simp
  κ1 := fun _ => 1
  κ2 := fun _ => 1
  pw := fun W => W.IsSymm ∧ ∀ u, W u u = 0
  fnet := fun u row pred _ => ∑ v, if v ≠ u then row v * pred v else 0
  pact := fun _ => True
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then Signum.pos else Signum.neg
  fout := fun _ s => match s with | .pos => (1 : R) | .neg => (-1 : R)
  m := fun s => match s with | .pos => (1 : R) | .neg => (-1 : R)
  hpact := by intro; simp }

/-- Zero / one network (σ ∈ {0,1}). -/
def ZeroOne (R U : Type) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U R :=
{ (SymmetricBinary R U) with
  pact := fun a => a = 0 ∨ a = 1
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then 1 else 0
  hpact := by
    classical
    intro W _ _ σ θ cur hcur u
    by_cases hth :
        (θ u).get fin0 ≤ ∑ v, if v ≠ u then W u v * cur v else 0
    · simp [SymmetricBinary, pact, fact, hth]; aesop
    · simp [SymmetricBinary, pact, fact, hth]; aesop }

variable [DecidableEq U] [Fintype U] [Nonempty U]

instance instTwoStateSymmetricBinary :
  TwoStateNeuralNetwork (SymmetricBinary R U) where
  σ_pos := (1 : R); σ_neg := (-1 : R)
  h_pos_ne_neg := by
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    have hlt : (-1 : R) < 1 := hneg.trans h0
    exact (ne_of_lt hlt).symm
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hle; simp [SymmetricBinary, hle]
  h_fact_neg := by
    intro u σcur net θ hlt
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [SymmetricBinary, this]
  h_pact_pos := by left; rfl
  h_pact_neg := by right; rfl
  m_order := by
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    exact hneg.trans h0

instance instTwoStateSignum :
  TwoStateNeuralNetwork (SymmetricSignum R U) where
  σ_pos := Signum.pos; σ_neg := Signum.neg
  h_pos_ne_neg := by intro h; cases h
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hn
    change (if θ.get fin0 ≤ net then Signum.pos else Signum.neg) = Signum.pos
    simp [hn]
  h_fact_neg := by
    intro u σcur net θ hlt
    change (if θ.get fin0 ≤ net then Signum.pos else Signum.neg) = Signum.neg
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [this]
  h_pact_pos := by trivial
  h_pact_neg := by trivial
  m_order := by
    -- `m` maps pos ↦ 1, neg ↦ -1
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    simp [SymmetricSignum]

instance instTwoStateZeroOne :
  TwoStateNeuralNetwork (ZeroOne R U) where
  σ_pos := (1 : R); σ_neg := (0 : R)
  h_pos_ne_neg := one_ne_zero
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hn
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 1
    simp [hn]
  h_fact_neg := by
    intro u σcur net θ hlt
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 0
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [this]
  h_pact_pos := by right; rfl
  h_pact_neg := by left; rfl
  m_order := by
    -- m = id, so goal is 0 < 1
    simp [ZeroOne, SymmetricBinary]

/-- Scale between numeric embeddings of the two states (pushed along f). -/
noncomputable def scale
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) : ℝ :=
  f (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))) -
    f (NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN)))

/-- Generalized scale in an arbitrary target ring S. -/
noncomputable def scaleS
    {S} [Ring S] {F} [FunLike F R S]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] (f : F) : S :=
  f (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))) -
    f (NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN)))

omit [DecidableEq U] [Fintype U] [Nonempty U] in
@[simp] lemma scaleS_apply_ℝ
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] (f : F) :
    scaleS (NN:=NN) (f:=f) = scale (NN:=NN) (f:=f) := rfl

@[simp] lemma scale_binary (f : R →+* ℝ) :
    scale (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) (f:=f) = f 2 := by
  -- σ_pos = 1, σ_neg = -1, m = id
  unfold scale
  simp [instTwoStateSymmetricBinary, SymmetricBinary, sub_neg_eq_add, one_add_one_eq_two]
  rw [@map_ofNat]

@[simp] lemma scale_zeroOne (f : R →+* ℝ) :
    scale (R:=R) (U:=U) (σ:=R) (NN:=ZeroOne R U) (f:=f) = f 1 := by
  -- σ_pos = 1, σ_neg = 0, m = id
  unfold scale
  simp [instTwoStateZeroOne, ZeroOne, SymmetricBinary]

/-- Logistic function used for Gibbs probabilities. -/
noncomputable def logisticProb (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

lemma logisticProb_nonneg (x : ℝ) : 0 ≤ logisticProb x := by
  unfold logisticProb
  have hx : 0 < Real.exp (-x) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-x) := by linarith
  exact div_nonneg zero_le_one hden.le

lemma logisticProb_le_one (x : ℝ) : logisticProb x ≤ 1 := by
  unfold logisticProb
  have hx : 0 < Real.exp (-x) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-x) := by linarith
  have : 1 ≤ 1 + Real.exp (-x) := by
    linarith
  simpa using (div_le_one hden).mpr this

/-- Probability P(σ_u = σ_pos) for one Gibbs update. -/
noncomputable def probPos
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) : ℝ :=
  let L := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  let κ := scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)
  logisticProb (κ * (f L) * (β T))

omit [DecidableEq U] [Fintype U] [Nonempty U] in
lemma probPos_nonneg
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    0 ≤ probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u := by
  unfold probPos; apply logisticProb_nonneg

omit [DecidableEq U] [Fintype U] [Nonempty U] in
lemma probPos_le_one
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u ≤ 1 := by
  unfold probPos; apply logisticProb_le_one

/-- Force neuron u to σ_pos. -/
def updPos {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U) : NN.State :=
{ act := Function.update s.act u (TwoStateNeuralNetwork.σ_pos (NN:=NN))
, hp := by
    intro v
    by_cases h : v = u
    · subst h; simpa using TwoStateNeuralNetwork.h_pact_pos (NN:=NN)
    · simpa [Function.update, h] using s.hp v }

/-- Force neuron u to σ_neg. -/
def updNeg {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U) : NN.State :=
{ act := Function.update s.act u (TwoStateNeuralNetwork.σ_neg (NN:=NN))
, hp := by
    intro v
    by_cases h : v = u
    · subst h; simpa using TwoStateNeuralNetwork.h_pact_neg (NN:=NN)
    · simpa [Function.update, h] using s.hp v }

/-- One–site Gibbs update kernel (PMF). -/
noncomputable def gibbsUpdate
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    PMF (NN.State) := by
  classical
  let pPos := probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u
  let pPosE := ENNReal.ofReal pPos
  have h_le : pPosE ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact probPos_le_one (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u
  exact
    PMF.bernoulli pPosE h_le >>= fun b =>
      if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u))

/-- Zero–temperature deterministic (threshold) update at site u.
    (Adjusted to avoid unused variable warning in the Prop-based `if`.) -/
def zeroTempDet
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (s : NN.State) (u : U) : NN.State :=
  let net := s.net p u
  let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  if h : θ ≤ net then
    (have _ := h; updPos (s:=s) (u:=u))
  else
    (have _ := h; updNeg (s:=s) (u:=u))

/-- Gibbs sweep auxiliary function. -/
noncomputable def gibbsSweepAux
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) :
    List U → NN.State → PMF NN.State
  | [],       s => PMF.pure s
  | u :: us, s =>
      gibbsUpdate (NN:=NN) f p T s u >>= fun s' =>
        gibbsSweepAux f p T us s'

omit [Fintype U] [Nonempty U] in
@[simp] lemma gibbsSweepAux_nil
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) :
    gibbsSweepAux (NN:=NN) f p T [] s = PMF.pure s := rfl

omit [Fintype U] [Nonempty U] in
@[simp] lemma gibbsSweepAux_cons
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (u : U) (us : List U) (s : NN.State) :
    gibbsSweepAux (NN:=NN) f p T (u :: us) s =
      gibbsUpdate (NN:=NN) f p T s u >>= fun s' =>
        gibbsSweepAux (NN:=NN) f p T us s' := rfl

/-- Sequential Gibbs sweep over a list of sites, head applied first. -/
noncomputable def gibbsSweep
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (order : List U) (p : Params NN) (T : Temperature) (f : F)
    (s0 : NN.State) : PMF NN.State :=
  gibbsSweepAux (NN:=NN) f p T order s0

omit [Fintype U] [Nonempty U] in
@[simp] lemma gibbsSweep_nil
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (T : Temperature) (f : F) (s0 : NN.State) :
    gibbsSweep (NN:=NN) ([] : List U) p T f s0 = PMF.pure s0 := rfl

omit [Fintype U] [Nonempty U] in
lemma gibbsSweep_cons
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (u : U) (us : List U) (p : Params NN) (T : Temperature) (f : F) (s0 : NN.State) :
    gibbsSweep (NN:=NN) (u :: us) p T f s0 =
      (gibbsUpdate (NN:=NN) f p T s0 u) >>= fun s =>
        gibbsSweep (NN:=NN) us p T f s := rfl

@[simp] lemma probPos_nonneg_apply_binary
    (f : R →+* ℝ) (p : Params (SymmetricBinary R U)) (T : Temperature)
    (s : (SymmetricBinary R U).State) (u : U) :
    0 ≤ probPos (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u :=
  probPos_nonneg (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u

@[simp] lemma probPos_le_one_apply_binary
    (f : R →+* ℝ) (p : Params (SymmetricBinary R U)) (T : Temperature)
    (s : (SymmetricBinary R U).State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u ≤ 1 :=
  probPos_le_one (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u

/-- **Energy specification bundling a global energy and a local field**.

This abstracts the thermodynamic view:
- `E p s` is the global energy of state `s` under parameters `p`;
- `localField p s u` is the local field at site `u` in state `s`.
-  The specification `localField_spec` connects the local field to the
  network primitives, and `flip_energy_relation` states the fundamental
  relation between energy differences and local fields.
Together these properties connect energy differences
to local fields and underpin the Gibbs/zero–temperature analysis. -/
structure EnergySpec
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] where
  /-- Global energy function `E p s`. -/
  E : Params NN → NN.State → R
  /-- Local field `L = localField p s u` at site `u`. -/
  localField : Params NN → NN.State → U → R
  /-- Specification tying the abstract `localField` to the network primitives:
      `localField p s u = s.net p u - (p.θ u).get (θ0 u)`. -/
  localField_spec :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      localField p s u =
        (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  /-- Fundamental flip–energy relation: the energy difference between the
      `updPos` and `updNeg` flips at `u` equals `- scale f * f(localField p s u)`,
      when pushed along a ring hom `f : R →+* ℝ`. -/
  flip_energy_relation :
    ∀ (f : R →+* ℝ)
      (p : Params NN) (s : NN.State) (u : U),
      let sPos := updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let sNeg := updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      f (E p sPos - E p sNeg) =
        - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
          f (localField p s u)

/-- A simplified energy specification carrying the same data as `EnergySpec`,
with the flip relation stated using inlined `updPos`/`updNeg`. -/
structure EnergySpec'
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] where
  /-- Global energy function `E p s`. -/
  E : Params NN → NN.State → R
  /-- Local field `L = localField p s u` at site `u`. -/
  localField : Params NN → NN.State → U → R
  /-- Specification tying `localField` to the network primitives:
      `localField p s u = s.net p u - (p.θ u).get (θ0 u)`. -/
  localField_spec :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      localField p s u =
        (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  /-- Fundamental flip–energy relation pushed along a ring hom `f : R →+* ℝ`:
      `f (E p (updPos s u) - E p (updNeg s u))
        = - scale f * f (localField p s u)`. -/
  flip_energy_relation :
    ∀ (f : R →+* ℝ) (p : Params NN) (s : NN.State) (u : U),
      f (E p (updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u))
           - E p (updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u))) =
        - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) * f (localField p s u)

namespace EnergySpec
variable {NN : NeuralNetwork R U σ}
variable [TwoStateNeuralNetwork NN]

omit [Fintype U] [Nonempty U] in
lemma flip_energy_rel'
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : TwoState.EnergySpec (NN:=NN)) (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  -- we build a bundled ring hom from f; its coercion is definitionally f
  let f_hom : R →+* ℝ :=
  { toMonoidHom :=
    { toFun := f
      map_one' := map_one f
      map_mul' := map_mul f }
    map_zero' := map_zero f
    map_add' := map_add f }
  have h := ES.flip_energy_relation f_hom p s u
  simpa [ES.localField_spec] using h

omit [Fintype U] [Nonempty U] in
lemma probPos_eq_of_energy
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : EnergySpec (NN:=NN)) (f : F) (p : Params NN) (T : Temperature)
    (s : NN.State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u =
      let sPos := updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let sNeg := updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let Δ := f (ES.E p sPos - ES.E p sNeg)
      logisticProb (- Δ * (β T)) := by
  classical
  unfold probPos
  have hΔ :=
    ES.flip_energy_rel' (f:=f) p s u
  simp [ES.localField_spec, hΔ, logisticProb,
        mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc]

end EnergySpec

namespace EnergySpec'
variable {NN : NeuralNetwork R U σ}
variable [TwoStateNeuralNetwork NN]

/-- Convert an `EnergySpec` to an `EnergySpec'`. -/
def ofOld
    (ES : TwoState.EnergySpec (NN:=NN)) : EnergySpec' (NN:=NN) :=
{ E := ES.E
, localField := ES.localField
, localField_spec := ES.localField_spec
, flip_energy_relation := by
    intro f p s u
    simpa using (ES.flip_energy_relation f p s u) }

omit [Fintype U] [Nonempty U] in
lemma flip_energy_rel'
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : EnergySpec' (NN:=NN)) (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  -- Build a bundled ring hom from f; its coercion is definitionally f
  let f_hom : R →+* ℝ :=
  { toMonoidHom :=
    { toFun := f
      map_one' := map_one f
      map_mul' := map_mul f }
    map_zero' := map_zero f
    map_add' := map_add f }
  have h := ES.flip_energy_relation f_hom p s u
  simpa [ES.localField_spec] using h

end EnergySpec'

omit [Fintype U] [Nonempty U] in
lemma EnergySpec.flip_energy_rel''
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (ES : TwoState.EnergySpec (NN:=NN))
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  classical
  refine (EnergySpec'.flip_energy_rel'
            (EnergySpec'.ofOld (NN:=NN) ES) (f:=f) p s u)

/-! ### Convergence
As β → ∞ (i.e., T → 0+), the one–site Gibbs update PMF converges pointwise to the
zero–temperature limit kernel, for any TwoState NN and any order-embedding f. -/

open scoped Topology Filter
open PMF Filter

section Convergence
variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U] [Fintype U] [Nonempty U]

variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]

omit [Field R] [IsStrictOrderedRing R] in
-- strict monotonicity from order-hom + injective
lemma strictMono_of_injective_orderHom
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) : StrictMono f :=
  (OrderHomClass.mono f).strictMono_of_injective hf

/-- If `a > 0`, the piecewise {1, 0, 1/2} based on the sign of `a*v` matches that of `v`. -/
lemma piecewise01half_sign_mul_left_pos {a v : ℝ} (ha : 0 < a) :
    (if 0 < a * v then 1 else if a * v < 0 then 0 else (1/2 : ℝ))
    =
    (if 0 < v then 1 else if v < 0 then 0 else (1/2 : ℝ)) := by
  by_cases hvpos : 0 < v
  · have : 0 < a * v := Left.mul_pos ha hvpos
    simp [hvpos, this, not_lt.mpr this.le]
  · by_cases hvneg : v < 0
    · have : a * v < 0 := mul_neg_of_pos_of_neg ha hvneg
      simp [hvpos, hvneg, this, not_lt.mpr this.le]
    · have hv0 : v = 0 := le_antisymm (le_of_not_gt hvpos) (le_of_not_gt hvneg)
      simp [hvpos, hvneg, hv0]

/-- If `x < 0` then the {1,0,1/2} piecewise is ≤ 0 (it equals 0). -/
private lemma piecewise01half_le_zero_of_neg {x : ℝ} (hx : x < 0) :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) ≤ 0 := by
  have hnotpos : ¬ 0 < x := not_lt.mpr hx.le
  simp [hnotpos, hx]

omit [Fintype U] [Nonempty U] [DecidableEq U] in
/-- Rewrite the 1/0/1/2 piecewise expression by dropping the positive `1/kB` factor
in front of its argument. This aligns the “zero-temperature target” with the
real-limit expression using `c0 := κ * f L`. -/
lemma sign_piecewise_rewrite_with_c0
    {F} [FunLike F R ℝ]
    (f : F)
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (L : R) :
    let κ := scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)
    (if 0 < ((κ / kB) * (f L)) then 1
     else if ((κ / kB) * (f L)) < 0 then 0 else (1/2 : ℝ))
    =
    (if 0 < (κ * (f L)) then 1
     else if (κ * (f L)) < 0 then 0 else (1/2 : ℝ)) := by
  intro κ
  have ha : 0 < (kB : ℝ)⁻¹ := inv_pos.mpr kB_pos
  have hrewrite :
      ((κ / kB) * (f L)) = (kB : ℝ)⁻¹ * (κ * (f L)) := by
    simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
  have h := piecewise01half_sign_mul_left_pos
              (a := (kB : ℝ)⁻¹) (v := κ * (f L)) ha
  simpa [hrewrite] using h

omit [IsStrictOrderedRing R] in
/-- Map of a positive (resp. negative) argument remains positive (resp. negative)
under a strictly monotone embedding sending `0 ↦ 0`. -/
lemma map_pos_of_pos
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ] [RingHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) {x : R} (hx : 0 < x) : 0 < f x := by
  have hsm := strictMono_of_injective_orderHom (R:=R) (f:=f) hf
  simpa [map_zero f] using (hsm hx)

omit [IsStrictOrderedRing R] in
lemma map_neg_of_neg
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ] [RingHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) {x : R} (hx : x < 0) : f x < 0 := by
  have hsm := strictMono_of_injective_orderHom (R:=R) (f:=f) hf
  simpa [map_zero f] using (hsm hx)

omit [DecidableEq U] [Fintype U] [Nonempty U] in
/-- κ := scale between the two numeric states (pushed along f) is positive
    under a strictly monotone embedding and the class `m_order`. -/
lemma scale_pos
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] :
    0 < scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) := by
  -- TwoStateNeuralNetwork.m_order : m σ_neg < m σ_pos
  have h := (strictMono_of_injective_orderHom (R:=R) (f:=f) hf)
  have himg :
      f (NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN))) <
        f (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))) :=
    h (TwoStateNeuralNetwork.m_order (NN:=NN))
  exact sub_pos.mpr himg

/-- One-step zero-temperature limit kernel (tie -> 1/2 mixture of updPos/updNeg). -/
noncomputable def zeroTempLimitPMF
    (p : Params NN) (s : NN.State) (u : U) : PMF NN.State :=
  let net := s.net p u
  let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  if h : θ < net then
    PMF.pure (updPos (s:=s) (u:=u))
  else if h' : net < θ then
    PMF.pure (updNeg (s:=s) (u:=u))
  else
    let pHalf : ℝ≥0∞ := ENNReal.ofReal (1/2)
    have hp : pHalf ≤ 1 := by
      simpa [pHalf] using
        (ENNReal.ofReal_le_one.mpr (by norm_num : (1/2 : ℝ) ≤ 1))
    PMF.bernoulli pHalf hp >>= fun b =>
      if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u))

omit [Fintype U] [Nonempty U] in
/-- Helper: the two updated states differ. -/
private lemma updPos_ne_updNeg (s : NN.State) (u : U) :
    updPos (s:=s) (u:=u) ≠ updNeg (s:=s) (u:=u) := by
  intro h
  have := congrArg (fun st => st.act u) h
  simp [updPos, updNeg, Function.update, TwoStateNeuralNetwork.h_pos_ne_neg] at this

/-
  General limit lemmas for reals, used to analyze the zero-temperature limit.
  These are independent of the neural-network context (mathlib-ready).
-/
open Real Filter Topology Monotone

/-- Multiplication by a positive constant maps `atTop` to `atTop`. -/
lemma tendsto_mul_const_atTop_atTop_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => c * x) atTop atTop := by
  refine (Filter.tendsto_atTop_atTop).2 ?_
  intro M
  refine ⟨M / c, ?_⟩
  intro x hx
  exact (div_le_iff₀' hc).mp hx

/-- Multiplication by a negative constant maps `atTop` to `atBot`. -/
lemma tendsto_mul_const_atTop_atBot_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun x : ℝ => c * x) atTop atBot := by
  refine (Filter.tendsto_atTop_atBot).2 ?_
  intro M
  refine ⟨M / c, ?_⟩
  intro x hx
  exact (div_le_iff_of_neg' hc).mp hx

/-- As `x → +∞`, `logisticProb x → 1`. -/
lemma logisticProb_tendsto_atTop :
    Tendsto logisticProb atTop (𝓝 (1 : ℝ)) := by
  -- logisticProb x = 1/(1 + exp(-x)); as x→+∞, -x→-∞, so exp(-x)→0, then 1/(1+r)→1
  have hx_neg : Tendsto (fun x : ℝ => -x) atTop atBot :=
    (tendsto_neg_atBot_iff).mpr tendsto_id
  have h_exp : Tendsto (fun x => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hx_neg
  have h_cont : ContinuousAt (fun r : ℝ => (1 : ℝ) / (1 + r)) 0 :=
    (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num))
  have h_comp :
      Tendsto (fun x => (1 : ℝ) / (1 + Real.exp (-x))) atTop (𝓝 ((1 : ℝ) / (1 + 0))) :=
    h_cont.tendsto.comp h_exp
  unfold logisticProb
  simpa [Real.exp_zero] using h_comp

/-- As `x → -∞`, `logisticProb x → 0`. -/
lemma logisticProb_tendsto_atBot :
    Tendsto logisticProb atBot (𝓝 (0 : ℝ)) := by
  -- 0 ≤ logistic ≤ exp, and exp x → 0 as x→-∞
  have h_le_exp : ∀ x : ℝ, logisticProb x ≤ Real.exp x := by
    intro x
    unfold logisticProb
    have hxpos : 0 < Real.exp (-x) := Real.exp_pos _
    have hz_le : Real.exp (-x) ≤ 1 + Real.exp (-x) := by linarith
    have : (1 : ℝ) / (1 + Real.exp (-x)) ≤ (1 : ℝ) / Real.exp (-x) :=
      one_div_le_one_div_of_le hxpos hz_le
    simpa [one_div, Real.exp_neg] using this
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds) (Real.tendsto_exp_atBot)
      (fun x => logisticProb_nonneg x)
      (fun x => h_le_exp x)

/-- As `T → 0+`, if `c > 0` then `c/T → +∞`. -/
lemma tendsto_c_div_atTop_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => c / T) (𝓝[>] (0 : ℝ)) atTop := by
  have h_inv : Tendsto (fun T : ℝ => T⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_mul := tendsto_mul_const_atTop_atTop_of_pos hc
  simpa [div_eq_mul_inv] using (h_mul.comp h_inv)

/-- As `T → 0+`, if `c < 0` then `c/T → -∞`. -/
lemma tendsto_c_div_atBot_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun T : ℝ => c / T) (𝓝[>] (0 : ℝ)) atBot := by
  have h_inv : Tendsto (fun T : ℝ => T⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_mul := tendsto_mul_const_atTop_atBot_of_neg hc
  simpa [div_eq_mul_inv] using (h_mul.comp h_inv)

/-- As `T → 0+`, if `c > 0` then `logisticProb (c/T) → 1`. -/
lemma tendsto_logistic_scaled_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
  logisticProb_tendsto_atTop.comp (tendsto_c_div_atTop_of_pos hc)

/-- As `T → 0+`, if `c < 0` then `logisticProb (c/T) → 0`. -/
lemma tendsto_logistic_scaled_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  logisticProb_tendsto_atBot.comp (tendsto_c_div_atBot_of_neg hc)

/-- As `T → 0+`, if `c = 0` then `logisticProb (c/T)` is constantly `1/2`. -/
lemma tendsto_logistic_scaled_of_eq_zero {c : ℝ} (hc : c = 0) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) / 2)) := by
  have : (fun T : ℝ => logisticProb (c / T)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin] with T _
    simp [logisticProb, hc, Real.exp_zero, one_add_one_eq_two]
  exact (tendsto_congr' this).mpr tendsto_const_nhds

/-- As `T → 0+`, `logisticProb (c / T)` tends to `1` if `c > 0`, to `0` if `c < 0`,
and to `1/2` if `c = 0`. -/
lemma tendsto_logistic_scaled
    (c : ℝ) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  by_cases hcpos : 0 < c
  · simpa [hcpos] using (tendsto_logistic_scaled_of_pos (c:=c) hcpos)
  · by_cases hcneg : c < 0
    · have := tendsto_logistic_scaled_of_neg (c:=c) hcneg
      simpa [hcpos, hcneg] using this
    · have hc0 : c = 0 := le_antisymm (le_of_not_gt hcpos) (le_of_not_gt hcneg)
      simpa [hcpos, hcneg, hc0] using (tendsto_logistic_scaled_of_eq_zero (c:=c) hc0)

/-- On ℝ≥0: as `b → ∞`, `logisticProb (c * b) → 1/0/1/2` depending on the sign of `c`. -/
lemma tendsto_logistic_const_mul_coeNNReal
    (c : ℝ) :
    Tendsto (fun b : ℝ≥0 => logisticProb (c * (b : ℝ))) atTop
      (𝓝 (if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  have h_coe : Tendsto (fun b : ℝ≥0 => (b : ℝ)) atTop atTop := by
    refine (Filter.tendsto_atTop_atTop).2 ?_
    intro M
    refine ⟨⟨max 0 (M + 1), by have : 0 ≤ max 0 (M + 1) := le_max_left _ _; exact this⟩, ?_⟩
    intro b hb
    have hBR : (max 0 (M + 1) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hM1 : (M + 1 : ℝ) ≤ (b : ℝ) := le_trans (le_max_right _ _) hBR
    have : (M : ℝ) ≤ (b : ℝ) := by linarith
    exact this
  by_cases hcpos : 0 < c
  ·
    have hmul := tendsto_mul_const_atTop_atTop_of_pos (c:=c) hcpos
    simpa [hcpos, Function.comp] using
      logisticProb_tendsto_atTop.comp (hmul.comp h_coe)
  · by_cases hcneg : c < 0
    ·
      have hmul := tendsto_mul_const_atTop_atBot_of_neg (c:=c) hcneg
      simpa [hcpos, hcneg, Function.comp] using
        logisticProb_tendsto_atBot.comp (hmul.comp h_coe)
    ·
      have hc0 : c = 0 := le_antisymm (le_of_not_gt hcpos) (le_of_not_gt hcneg)
      have hconst :
          (fun b : ℝ≥0 => logisticProb (c * (b : ℝ))) = fun _ => (1/2 : ℝ) := by
        funext b; simp [hc0, logisticProb, Real.exp_zero, one_add_one_eq_two]
      aesop

omit [DecidableEq U] [Fintype U] [Nonempty U] in
/-- Real-valued probability limit P(T) for our model as T → 0+. -/
private lemma tendsto_probPos_at_zero
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (_ : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let L : R := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    Tendsto (fun T : ℝ => probPos (NN:=NN) f p ⟨Real.toNNReal T⟩ s u)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (let κ := scale (NN:=NN) (f:=f); let c := (κ / kB) * (f L);
          if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  intro L
  have h_event :
      (fun T : ℝ => probPos (NN:=NN) f p ⟨Real.toNNReal T⟩ s u)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun T : ℝ =>
        logisticProb (((scale (NN:=NN) (f:=f)) / kB) * (f L) / T)) := by
    filter_upwards [self_mem_nhdsWithin] with T hTpos
    have hT0 : 0 ≤ T := le_of_lt hTpos
    have : (β ⟨Real.toNNReal T⟩ : ℝ) = 1 / (kB * T) := by
      simp [Temperature.β, Temperature.toReal, Real.toNNReal_of_nonneg hT0, one_div]
    unfold probPos
    simp [this, logisticProb, one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
    aesop
  have hlim :
      Tendsto (fun T : ℝ =>
        logisticProb (((scale (NN:=NN) (f:=f)) / kB) * (f L) / T))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (let κ := scale (NN:=NN) (f:=f); let c := (κ / kB) * (f L);
             if 0 < c then 1 else if c < 0 then 0 else 1/2)) :=
    tendsto_logistic_scaled _
  exact (tendsto_congr' h_event).mpr hlim

/- Simple ENNReal evaluation lemmas for the Gibbs one-step with Bernoulli bind. -/
namespace PMF

variable {α : Type}

@[simp]
lemma bernoulli_bind_pure_apply_left_of_ne
    {p : ℝ≥0∞} (hp : p ≤ 1) {x y : α} (hxy : x ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) x = p := by
  classical
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) x = p
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, PMF.pure_apply, tsum_fintype]
  have : Finset.univ = ({false, true} : Finset Bool) := by
    ext b; simp
  rw [this, Finset.sum_pair (by simp : false ≠ true)]
  simp only [Bool.cond_false, Bool.cond_true]
  simp [hxy, if_neg hxy.symm]

@[simp]
lemma bernoulli_bind_pure_apply_other
    {p : ℝ≥0∞} (hp : p ≤ 1) {x y z : α} (hx : z ≠ x) (hy : z ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) z = 0 := by
  classical
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) z = 0
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, PMF.pure_apply, tsum_fintype]
  have : Finset.univ = ({false, true} : Finset Bool) := by
    ext b; simp
  rw [this, Finset.sum_pair (by simp : false ≠ true)]
  simp only [Bool.cond_false, Bool.cond_true]
  simp [hx, hy, if_neg hx.symm, if_neg hy.symm]

variable {α : Type} [DecidableEq α]

@[simp]
lemma bernoulli_bind_pure_apply_right_of_ne
    {p : ℝ≥0∞} (hp : p ≤ 1) {x y : α} (hxy : x ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) y = (1 - p) := by
  classical
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) y = (1 - p)
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, PMF.pure_apply, tsum_fintype]
  have : Finset.univ = ({false, true} : Finset Bool) := by
    ext b; simp
  rw [this, Finset.sum_pair (by simp : false ≠ true)]
  simp only [Bool.cond_false, Bool.cond_true]
  simp [hxy, if_neg hxy]
  aesop

end PMF
open PMF
omit [Fintype U] [Nonempty U] in
/-- Pointwise evaluation at `updPos`: exact (not just eventual) equality. -/
private lemma gibbsUpdate_apply_updPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN:=NN) f p T s u) (updPos (s:=s) (u:=u))
      = ENNReal.ofReal (probPos (NN:=NN) f p T s u) := by
  classical
  unfold gibbsUpdate
  set pPos := probPos (NN:=NN) f p T s u
  set pPosE := ENNReal.ofReal pPos
  have h_le : pPosE ≤ 1 := by
    simpa [pPosE] using probPos_le_one (NN:=NN) f p T s u
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  simp [PMF.bernoulli_bind_pure_apply_left_of_ne (α:=NN.State) h_le hne, pPosE, pPos]

omit [Fintype U] [Nonempty U] in
/-- Pointwise evaluation at `updNeg`: exact (not just eventual) equality. -/
private lemma gibbsUpdate_apply_updNeg
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN:=NN) f p T s u) (updNeg (s:=s) (u:=u))
      = ENNReal.ofReal (1 - probPos (NN:=NN) f p T s u) := by
  classical
  unfold gibbsUpdate
  set pPos := probPos (NN:=NN) f p T s u
  set pPosE := ENNReal.ofReal pPos
  have h_le : pPosE ≤ 1 := by
    simpa [pPosE] using probPos_le_one (NN:=NN) f p T s u
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  have : ((PMF.bernoulli pPosE h_le) >>= fun b => if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u))) (updNeg (s:=s) (u:=u))
      = (1 - pPosE) := PMF.bernoulli_bind_pure_apply_right_of_ne (α:=NN.State) h_le hne
  rw [this]
  have hpos_nonneg : 0 ≤ pPos := probPos_nonneg (NN:=NN) f p T s u
  have hpos_le_one : pPos ≤ 1 := probPos_le_one (NN:=NN) f p T s u
  have h_eq : (1 : ℝ≥0∞) - pPosE = ENNReal.ofReal (1 - pPos) := by
    simp_rw [pPosE]
    rw [← ENNReal.ofReal_one]
    rw [ENNReal.ofReal_sub 1 hpos_nonneg]
  rw [h_eq]

omit [Fintype U] [Nonempty U] in
/-- Eventual equality rewriting Gibbs mass at updPos along β → ∞ to ENNReal.ofReal (probPos at T). -/
private lemma eventually_eval_updPos_eq_ofReal_probPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    (fun b : ℝ≥0 => (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      =ᶠ[atTop]
    (fun b : ℝ≥0 => ENNReal.ofReal (probPos (NN:=NN) f p (Temperature.ofβ b) s u)) := by
  refine Filter.Eventually.of_forall ?_
  intro b; simp [gibbsUpdate_apply_updPos]

omit [Fintype U] [Nonempty U] in
/-- Eventual equality rewriting Gibbs mass at updNeg along β → ∞ to ENNReal.ofReal (1 - probPos). -/
private lemma eventually_eval_updNeg_eq_ofReal_one_sub_probPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    (fun b : ℝ≥0 => (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
      =ᶠ[atTop]
    (fun b : ℝ≥0 => ENNReal.ofReal (1 - probPos (NN:=NN) f p (Temperature.ofβ b) s u)) := by
  refine Filter.Eventually.of_forall ?_
  intro b; simp [gibbsUpdate_apply_updNeg]

omit [Fintype U] [Nonempty U] in
/-- Target evaluation: the zero-temperature PMF mass at `updPos` as an ENNReal.ofReal
    piecewise {1,0,1/2} driven by the sign of `((scale f)/kB) * f L`. -/
private lemma zeroTemp_target_updPos_as_ofReal_sign
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    (zeroTempLimitPMF (NN:=NN) p s u) (updPos (s:=s) (u:=u)) =
      ENNReal.ofReal
        (if 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ))
         then 1 else if ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) < 0 then 0 else (1/2 : ℝ)) := by
  classical
  intro net θ
  by_cases hpos : θ < net
  · -- positive local field: pure updPos, RHS selects 1 branch
    have hLpos : 0 < (net - θ) := sub_pos.mpr hpos
    have hfpos : 0 < f (net - θ) := map_pos_of_pos (R:=R) (f:=f) hf hLpos
    have hκpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) :=
      div_pos (scale_pos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) hf) kB_pos
    have hprodpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) :=
      mul_pos hκpos hfpos
    have hne := updPos_ne_updNeg (s:=s) (u:=u)
    simp only [zeroTempLimitPMF, net, θ, hpos, not_lt.mpr hpos.le, PMF.pure_apply,
      hne, dite_eq_ite, if_true, ENNReal.ofReal_one]
    simp [hprodpos]
    aesop
  · by_cases hneg : net < θ
    · -- negative local field: pure updNeg at updPos gives 0, RHS selects 0 branch
      have hLneg : (net - θ) < 0 := sub_lt_zero.mpr hneg
      have hfneg : f (net - θ) < 0 := map_neg_of_neg (R:=R) (f:=f) hf hLneg
      have hκpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) :=
        div_pos (scale_pos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) hf) kB_pos
      have hprodneg : ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) < 0 :=
        mul_neg_of_pos_of_neg hκpos hfneg
      have hne := updPos_ne_updNeg (s:=s) (u:=u)
      simp only [zeroTempLimitPMF, net, θ, hneg, not_lt.mpr hneg.le, PMF.pure_apply,
        hne, dite_eq_ite, if_false, if_true, ENNReal.ofReal_zero]
      rw [@ENNReal.zero_eq_ofReal]
      have hprodneg' :
          ((scale (NN:=NN) (f:=f)) / kB) * ((f net) - (f θ)) < 0 := by
        simpa [map_sub f] using hprodneg
      simpa using
        (piecewise01half_le_zero_of_neg
          (x := ((scale (NN:=NN) (f:=f)) / kB) * ((f net) - (f θ)))) hprodneg'
    · -- tie: 1/2 mixture, RHS selects 1/2 branch
      have h_eq : net = θ := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hf0 : f (net - θ) = 0 := by simp [h_eq, map_zero f]
      have hne := updPos_ne_updNeg (s:=s) (u:=u)
      simp [zeroTempLimitPMF, net, θ, hpos, hneg, hf0, hne]

omit [Fintype U] [Nonempty U] in
/-- Target evaluation: the zero-temperature PMF mass at `updNeg` as ENNReal.ofReal
    of one minus the same 1/0/1/2 piecewise expression. -/
private lemma zeroTemp_target_updNeg_as_ofReal_one_sub_sign
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    (zeroTempLimitPMF (NN:=NN) p s u) (updNeg (s:=s) (u:=u)) =
      ENNReal.ofReal
        (1 - (if 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ))
              then 1 else if ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) < 0 then 0 else (1/2 : ℝ))) := by
  classical
  intro net θ
  by_cases hpos : θ < net
  · have hLpos : 0 < (net - θ) := sub_pos.mpr hpos
    have hfpos : 0 < f (net - θ) := map_pos_of_pos (R:=R) (f:=f) hf hLpos
    have hκpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) :=
      div_pos (scale_pos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) hf) kB_pos
    have hprodpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) :=
      mul_pos hκpos hfpos
    have hne := updPos_ne_updNeg (s:=s) (u:=u)
    simp [zeroTempLimitPMF, net, θ, hpos, not_lt.mpr hpos.le, hprodpos, PMF.pure_apply, hne]
    aesop
  · by_cases hneg : net < θ
    · have hLneg : (net - θ) < 0 := sub_lt_zero.mpr hneg
      have hfneg : f (net - θ) < 0 := map_neg_of_neg (R:=R) (f:=f) hf hLneg
      have hκpos : 0 < ((scale (NN:=NN) (f:=f)) / kB) :=
        div_pos (scale_pos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) hf) kB_pos
      have hprodneg : ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) < 0 :=
        mul_neg_of_pos_of_neg hκpos hfneg
      have hne := updPos_ne_updNeg (s:=s) (u:=u)
      have hprodneg' :
          ((scale (NN:=NN) (f:=f)) / kB) * ((f net) - (f θ)) < 0 := by
        simpa [map_sub f] using hprodneg
      have hnotpos' :
          ¬ 0 < ((scale (NN:=NN) (f:=f)) / kB) * ((f net) - (f θ)) :=
        not_lt.mpr hprodneg'.le
      simp [zeroTempLimitPMF, net, θ, hneg, not_lt.mpr hneg.le, PMF.pure_apply,
            hprodneg', hnotpos', one_div]
    · -- tie branch: 1 - ofReal(1/2) = ofReal (1 - 1/2)
      have h_eq : net = θ := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hf0 : f (net - θ) = 0 := by simp [h_eq, map_zero f]
      have hne := updPos_ne_updNeg (s:=s) (u:=u)
      let pHalf : ℝ≥0∞ := ENNReal.ofReal (1 / 2 : ℝ)
      have hp : pHalf ≤ 1 := by
        simpa [pHalf] using
          (ENNReal.ofReal_le_one.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hbind :
        ((PMF.bernoulli pHalf hp) >>= fun b =>
            if b then PMF.pure (updPos (s:=s) (u:=u))
                 else PMF.pure (updNeg (s:=s) (u:=u)))
          (updNeg (s:=s) (u:=u)) = 1 - pHalf :=
        PMF.bernoulli_bind_pure_apply_right_of_ne (α:=NN.State) hp hne
      have hle₁ : (1 / 2 : ℝ) ≤ 1 := by norm_num
      have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
      have hsub :
          (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2 : ℝ) =
            ENNReal.ofReal (1 - (1 / 2 : ℝ)) := by
        have h := ENNReal.ofReal_sub
          (p := (1 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        simpa [ENNReal.ofReal_one, one_div] using h.symm
      have hbind' :
          ((PMF.bernoulli pHalf hp) >>= fun b =>
              if b then PMF.pure (updPos (s:=s) (u:=u))
                   else PMF.pure (updNeg (s:=s) (u:=u)))
            (updNeg (s:=s) (u:=u))
          = (1 - ENNReal.ofReal (1 / 2 : ℝ)) := by
        simpa [pHalf] using hbind
      simp [zeroTempLimitPMF, net, θ, hpos, hneg, hf0, hne]
      aesop

omit [DecidableEq U] [Fintype U] [Nonempty U] in
/-- Real-valued limit along `β (ofβ b) = b`: `probPos` tends to 1/0/1/2 by the sign of `c0`. -/
private lemma tendsto_probPos_along_ofβ_to_piecewise
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    let L := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    let c0 : ℝ := (scale (NN:=NN) (f:=f)) * (f L)
    Tendsto (fun b : ℝ≥0 => probPos (NN:=NN) f p (Temperature.ofβ b) s u)
      atTop
      (𝓝 (if 0 < c0 then 1 else if c0 < 0 then 0 else 1/2)) := by
  intro L c0
  have hβ : ∀ b, (β (Temperature.ofβ b) : ℝ) = b := by intro b; simp
  have h_form :
      ∀ b, probPos (NN:=NN) f p (Temperature.ofβ b) s u
            = logisticProb (c0 * (b : ℝ)) := by
    intro b; unfold probPos; simp [hβ b, L, c0, mul_comm, mul_left_comm, mul_assoc, logisticProb]
  simpa [h_form] using tendsto_logistic_const_mul_coeNNReal c0

omit [Fintype U] [Nonempty U] in
/-- Convergence on `updPos`: short proof using the split helpers. -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_updPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      atTop (𝓝 ((zeroTempLimitPMF (NN:=NN) p s u) (updPos (s:=s) (u:=u)))) := by
  classical
  have h_target := zeroTemp_target_updPos_as_ofReal_sign (NN:=NN) f hf p s u
  have hev := eventually_eval_updPos_eq_ofReal_probPos (NN:=NN) f p s u
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : R := net - θ
  set c0 : ℝ := (scale (NN:=NN) (f:=f)) * (f L)
  have h_real := tendsto_probPos_along_ofβ_to_piecewise (NN:=NN) f p s u
  have h_rewrite := sign_piecewise_rewrite_with_c0 (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) L
  have hlim := ENNReal.tendsto_ofReal (by simpa [L, c0, h_rewrite] using h_real)
  have h := (tendsto_congr' hev).mpr hlim
  have h' : Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      atTop (𝓝 (ENNReal.ofReal
        (if 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ))
         then 1 else if ((scale (NN:=NN) (f:=f)) / kB) * (f (net - θ)) < 0 then 0 else (1/2 : ℝ)))) := by
    aesop
  simpa [h_target, net, θ] using h'

omit [Fintype U] [Nonempty U] in
/-- Convergence on `updNeg`: short proof using the split helpers. -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_updNeg
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
      atTop (𝓝 ((zeroTempLimitPMF (NN:=NN) p s u) (updNeg (s:=s) (u:=u)))) := by
  classical
  have h_target := zeroTemp_target_updNeg_as_ofReal_one_sub_sign (NN:=NN) f hf p s u
  have hev := eventually_eval_updNeg_eq_ofReal_one_sub_probPos (NN:=NN) f p s u
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : R := net - θ
  set c0 : ℝ := (scale (NN:=NN) (f:=f)) * (f L)
  have h_real :=
    tendsto_probPos_along_ofβ_to_piecewise (NN:=NN) f p s u
  have h_sub :
      Tendsto (fun b : ℝ≥0 =>
        (1 : ℝ) - probPos (NN:=NN) f p (Temperature.ofβ b) s u)
        atTop
        (𝓝 (1 - (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2)))) :=
    tendsto_const_nhds.sub h_real
  have h_lift :
      Tendsto (fun b : ℝ≥0 =>
        ENNReal.ofReal (1 - probPos (NN:=NN) f p (Temperature.ofβ b) s u))
        atTop
        (𝓝 (ENNReal.ofReal (1 - (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2))))) :=
    ENNReal.tendsto_ofReal h_sub
  have h_rewrite :
      (if 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f L) then 1
       else if ((scale (NN:=NN) (f:=f)) / kB) * (f L) < 0 then 0 else (1/2 : ℝ))
        =
      (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2 : ℝ)) := by
    simpa [c0, one_div] using
      sign_piecewise_rewrite_with_c0
        (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f) L
  have h_conv :
      Tendsto (fun b : ℝ≥0 =>
        (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
        atTop
        (𝓝 (ENNReal.ofReal
              (1 - (if 0 < ((scale (NN:=NN) (f:=f)) / kB) * (f L)
                     then 1 else if ((scale (NN:=NN) (f:=f)) / kB) * (f L) < 0
                                   then 0 else (1/2 : ℝ))))) := by
    have := (tendsto_congr' hev).mpr h_lift
    aesop
  aesop

omit [Fintype U] [Nonempty U] in
/-- Convergence on any “other” state (neither updPos nor updNeg). -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_other
    {F} [FunLike F R ℝ]
    (f : F)
    (p : Params NN) (s : NN.State) (u : U)
    {state : NN.State}
    (hpos : state ≠ updPos (s:=s) (u:=u))
    (hneg : state ≠ updNeg (s:=s) (u:=u)) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) state)
      atTop (𝓝 ((zeroTempLimitPMF (NN:=NN) p s u) state)) := by
  classical
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  have htarget0 :
      (zeroTempLimitPMF (NN:=NN) p s u) state = 0 := by
    by_cases hθnet : θ < net
    · simp [zeroTempLimitPMF, net, θ, hθnet, PMF.pure_apply, hpos]
    · by_cases hnetθ : net < θ
      · simp [zeroTempLimitPMF, net, θ, hθnet, hnetθ, PMF.pure_apply, hneg]
      ·
        have hp : ENNReal.ofReal (1/2) ≤ (1 : ℝ≥0∞) := by
          simpa using (ENNReal.ofReal_le_one.2 (by norm_num : (1/2 : ℝ) ≤ 1))
        have hbind_zero :
          ((PMF.bernoulli (ENNReal.ofReal (1/2)) hp) >>= fun b =>
            if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u))) state = 0 :=
          PMF.bernoulli_bind_pure_apply_other (α:=NN.State) hp hpos hneg
        simpa [zeroTempLimitPMF, net, θ, hθnet, hnetθ] using hbind_zero
  have hev :
      (fun b : ℝ≥0 =>
        (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) state)
      =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    simp [gibbsUpdate, PMF.bind_apply, tsum_fintype, PMF.pure_apply, hpos, hneg]
  have : Tendsto (fun b : ℝ≥0 =>
    (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) state) atTop (𝓝 0) :=
    (tendsto_congr' hev).mpr tendsto_const_nhds
  simpa [htarget0] using this

omit [Fintype U] [Nonempty U] in
/-- **Theorem** Pointwise convergence of the one–site Gibbs PMF to the zero-temperature limit PMF,
for every state. This wraps the three evaluation lemmas into a single statement. -/
theorem gibbs_update_tends_to_zero_temp_limit
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    ∀ state : NN.State,
      Tendsto (fun b : ℝ≥0 =>
        (gibbsUpdate (NN:=NN) f p (Temperature.ofβ b) s u) state)
        atTop (𝓝 ((zeroTempLimitPMF (NN:=NN) p s u) state)) := by
  classical
  intro state
  by_cases hpos : state = updPos (s:=s) (u:=u)
  · subst hpos
    exact gibbs_update_tends_to_zero_temp_limit_apply_updPos
            (NN:=NN) f hf p s u
  · by_cases hneg : state = updNeg (s:=s) (u:=u)
    · subst hneg
      exact gibbs_update_tends_to_zero_temp_limit_apply_updNeg
              (NN:=NN) f hf p s u
    · exact gibbs_update_tends_to_zero_temp_limit_apply_other
              (NN:=NN) f p s u (by simpa using hpos) (by simpa using hneg)

end Convergence
end TwoState

open Finset Matrix NeuralNetwork State Constants Temperature Filter Topology
open scoped ENNReal NNReal BigOperators
open NeuralNetwork
namespace TwoState

--variable {R U σ : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
/-!
Fix: strengthen the typeclass assumptions in the final section (they were only `[Zero R]`)
and specialize to `R = ℝ` so that `EnergySpec` (which requires ordered field structure)
is usable. Then provide a complete implementation of
`EnergySpec.energy_order_from_flip_id` (previous version failed due to missing instances).
-/


lemma updPos_eq_self_of_act_pos
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U)
    (h : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN)) :
    updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u = s := by
  classical
  ext v
  by_cases hv : v = u
  · subst hv; simp [updPos, Function.update, h]
  · simp [updPos, Function.update, hv]

/-- Helper: if the current activation at `u` is already `σ_neg`, `updNeg` is identity. -/
lemma updNeg_eq_self_of_act_neg
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U)
    (h : s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u = s := by
  classical
  ext v
  by_cases hv : v = u
  · subst hv; simp [updNeg, Function.update, h]
  · simp [updNeg, Function.update, hv]

/-- Classification of a single asynchronous update at site `u`:
`Up` equals `updPos` if `θ ≤ net`, else `updNeg`. (Explicit parameters to
stabilize elaboration.) -/
lemma Up_eq_updPos_or_updNeg
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ   := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    s.Up p u =
      (if θ ≤ net then updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u
       else updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u) := by
  classical
  intro net θ
  ext v
  by_cases hv : v = u
  · subst hv
    unfold NeuralNetwork.State.Up
    simp only
    by_cases hθle : θ ≤ net
    ·
      have hpos :=
        TwoStateNeuralNetwork.h_fact_pos (NN:=NN) v (s.act v) net (p.θ v) hθle
      have : NN.fact v (s.act v)
          (NN.fnet v (p.w v) (fun w => s.out w) (p.σ v))
          (p.θ v) = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
        simpa [NeuralNetwork.State.net] using hpos
      simp [updPos, Function.update, this, hθle]
      aesop
    · have hlt : net < θ := lt_of_not_ge hθle
      have hneg :=
        TwoStateNeuralNetwork.h_fact_neg (NN:=NN) v (s.act v) net (p.θ v) hlt
      have : NN.fact v (s.act v)
          (NN.fnet v (p.w v) (fun w => s.out w) (p.σ v))
          (p.θ v) = TwoStateNeuralNetwork.σ_neg (NN:=NN) := by
        simpa [NeuralNetwork.State.net] using hneg
      simp [updNeg, Function.update, this, hθle]
      aesop
  · unfold NeuralNetwork.State.Up
    simp_rw [hv, updPos, updNeg]; simp [Function.update]
    aesop
end TwoState
namespace TwoState.EnergySpec'

/-- Given an energy difference identity
  E sPos - E sNeg = - κ * L   with κ ≥ 0,
we deduce the two directional inequalities depending on the sign of L. -/
lemma energy_order_from_flip_id
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (NN:=NN))
    {p : Params NN}
    {κ L : ℝ} {sPos sNeg : NN.State}
    (hdiff : spec.E p sPos - spec.E p sNeg = - κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → spec.E p sPos ≤ spec.E p sNeg) ∧
    (L ≤ 0 → spec.E p sNeg ≤ spec.E p sPos) := by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hDiffLe : spec.E p sPos - spec.E p sNeg ≤ 0 := by
      rw [hdiff]; simp only [neg_mul, Left.neg_nonpos_iff]; exact hκL
    exact sub_nonpos.mp hDiffLe
  · intro hL
    have hrev : spec.E p sNeg - spec.E p sPos = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have : spec.E p sNeg - spec.E p sPos ≤ 0 := by simpa [hrev] using hκL
    exact sub_nonpos.mp this

end EnergySpec'
end TwoState
namespace TwoState

section ConcreteLyapunov
variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

-- Note: The following lemmas are specialized for `SymmetricBinary ℝ U`
-- to simplify the proof development by avoiding universe polymorphism issues.

lemma updPos_eq_self_of_act_pos_binary
    (s : (SymmetricBinary ℝ U).State) (u : U)
    (h : s.act u = 1) :
    updPos (NN:=SymmetricBinary ℝ U) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updPos, Function.update, h, instTwoStateSymmetricBinary]
  · simp [updPos, Function.update, hv]

lemma updNeg_eq_self_of_act_neg_binary
    (s : (SymmetricBinary ℝ U).State) (u : U)
    (h : s.act u = -1) :
    updNeg (NN:=SymmetricBinary ℝ U) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updNeg, Function.update, h, instTwoStateSymmetricBinary]
  · simp [updNeg, Function.update, hv]

lemma Up_eq_updPos_or_updNeg_binary
    (p : Params (SymmetricBinary ℝ U)) (s : (SymmetricBinary ℝ U).State) (u : U) :
    let net := s.net p u
    let θ   := (p.θ u).get fin0
    s.Up p u =
      (if θ ≤ net
       then updPos (NN:=SymmetricBinary ℝ U) s u
       else updNeg (NN:=SymmetricBinary ℝ U) s u) := by
  intro net θ
  classical
  -- Reuse the general classification lemma and unfold the lets.
  simpa [net, θ] using
    (TwoState.Up_eq_updPos_or_updNeg
        (R:=ℝ) (U:=U) (σ:=ℝ)
        (NN:=SymmetricBinary ℝ U) p s u)

lemma energy_order_from_flip_id_binary
    (spec : EnergySpec' (NN:=SymmetricBinary ℝ U))
    {p : Params (SymmetricBinary ℝ U)}
    {κ L : ℝ} {sPos sNeg : (SymmetricBinary ℝ U).State}
    (hdiff : spec.E p sPos - spec.E p sNeg = - κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → spec.E p sPos ≤ spec.E p sNeg) ∧
    (L ≤ 0 → spec.E p sNeg ≤ spec.E p sPos) := by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hsub : spec.E p sPos - spec.E p sNeg ≤ 0 := by
      rw [hdiff]; aesop
    exact sub_nonpos.mp hsub
  · intro hL
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have hrev : spec.E p sNeg - spec.E p sPos = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hsub : spec.E p sNeg - spec.E p sPos ≤ 0 := by
      rw [hrev]; exact hκL
    exact sub_nonpos.mp hsub

/-- Lyapunov (energy non‑increase) at a single site for `SymmetricBinary` networks. -/
lemma energy_is_lyapunov_at_site_binary
    (spec : EnergySpec' (NN:=SymmetricBinary ℝ U))
    (p : Params (SymmetricBinary ℝ U)) (s : (SymmetricBinary ℝ U).State) (u : U)
    (hcur : s.act u = 1 ∨ s.act u = -1) :
    spec.E p (s.Up p u) ≤ spec.E p s := by
  set sPos := updPos (NN:=SymmetricBinary ℝ U) s u
  set sNeg := updNeg (NN:=SymmetricBinary ℝ U) s u
  set net := s.net p u
  set θ   := (p.θ u).get fin0
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  -- Get the energy difference relation from the spec
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by simp [L, net, θ, spec.localField_spec]; aesop
  have hdiff : spec.E p sPos - spec.E p sNeg = - (scale (NN:=SymmetricBinary ℝ U) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  -- Define κ and prove it's non-negative
  set κ := scale (NN:=SymmetricBinary ℝ U) (f:=fid)
  have hκ_pos : 0 < κ := by aesop--simp [scale_binary, map_ofNat]
  have hκ_nonneg : 0 ≤ κ := hκ_pos.le
  -- Get the ordering implications from the energy difference
  have hOrder := energy_order_from_flip_id_binary spec hdiff hκ_nonneg
  -- Relate the abstract update `Up` to concrete `updPos`/`updNeg`
  have hUp_cases := Up_eq_updPos_or_updNeg_binary p s u
  -- Case split on the threshold condition
  by_cases hθle : θ ≤ net
  · -- Case 1: net ≥ θ, so update goes to sPos
    have hUp_cases_eval := hUp_cases
    simp [net, θ, hθle, sPos, sNeg] at hUp_cases_eval
    rw [hUp_cases_eval]
    cases hcur with
    | inl h_is_pos =>
      rw [updPos_eq_self_of_act_pos_binary s u h_is_pos]
    | inr h_is_neg =>
      have hL_nonneg : 0 ≤ L := by simpa [L] using sub_nonneg.mpr hθle
      have hs : s = sNeg := (updNeg_eq_self_of_act_neg_binary s u h_is_neg).symm
      have hLE : spec.E p sPos ≤ spec.E p sNeg := hOrder.left hL_nonneg
      simp_rw [hs]
      exact
        le_of_eq_of_le (congrArg (spec.E p) (congrFun (congrArg updPos (id (Eq.symm hs))) u)) hLE
  · -- Case 2: net < θ, so update goes to sNeg
    have hUp_cases_eval := hUp_cases
    simp [net, θ, hθle, sPos, sNeg] at hUp_cases_eval
    rw [hUp_cases_eval]
    cases hcur with
    | inl h_is_pos =>
      have hL_nonpos : L ≤ 0 := by simpa [L] using (lt_of_not_ge hθle).le
      have hs : s = sPos := (updPos_eq_self_of_act_pos_binary s u h_is_pos).symm
      have hLE : spec.E p sNeg ≤ spec.E p sPos := hOrder.2 hL_nonpos
      simp_rw [hs]
      exact
        le_of_eq_of_le (congrArg (spec.E p) (congrFun (congrArg updNeg (id (Eq.symm hs))) u)) hLE
    | inr h_is_neg =>
      rw [updNeg_eq_self_of_act_neg_binary s u h_is_neg]

end ConcreteLyapunov
namespace EnergySpec'
open TwoState

/-- General (non-binary–specialized) Lyapunov single–site energy descent lemma. -/
lemma energy_is_lyapunov_at_site
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R:=ℝ) (NN:=NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    spec.E p (s.Up p u) ≤ spec.E p s := by
  classical
  set sPos := updPos (NN:=NN) s u
  set sNeg := updNeg (NN:=NN) s u
  set net  := s.net p u
  set θ    := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by
    simp [L, net, θ, spec.localField_spec]
  have hdiff :
      spec.E p sPos - spec.E p sNeg
        = - (scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  set κ := scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)
  have hm := TwoStateNeuralNetwork.m_order (NN:=NN)
  have hκpos : 0 < κ := by
    simp [κ, scale]
    aesop
  have hκ : 0 ≤ κ := hκpos.le
  have hOrder :=
    TwoState.EnergySpec'.energy_order_from_flip_id
      (NN:=NN) (spec:=spec) (p:=p) (κ:=κ) (L:=L)
      (sPos:=sPos) (sNeg:=sNeg) hdiff hκ
  have hup := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
  by_cases hθle : θ ≤ net
  · have hUpPos : s.Up p u = sPos := by
      simpa [net, θ, hθle] using hup
    cases hcur with
    | inl hpos =>
        have hFixed : sPos = s := by
          have h := TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hpos
          simpa [sPos] using h
        simp [hUpPos, hFixed]
    | inr hneg =>
        have hEqNeg : sNeg = s := by
          have h := TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hneg
          simpa [sNeg] using h
        have hL : 0 ≤ L := by
          have : θ ≤ net := hθle
          simpa [L] using sub_nonneg.mpr this
        have hLE := hOrder.left hL
        simp [hUpPos, hEqNeg]
        aesop
  · have hnetlt : net < θ := lt_of_not_ge hθle
    have hLle : L ≤ 0 := by
      have : net - θ < 0 := sub_lt_zero.mpr hnetlt
      exact this.le
    have hUpNeg : s.Up p u = sNeg := by
      have hnot : ¬ θ ≤ net := hθle
      simpa [net, θ, hnot] using hup
    cases hcur with
    | inl hpos =>
        have hEqPos : sPos = s := by
          have h := TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hpos
          simpa [sPos] using h
        have hLE := hOrder.right hLle
        simp [hUpNeg, hEqPos]
        aesop
    | inr hneg =>
        have hFixed : sNeg = s := by
          have h := TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hneg
          simpa [sNeg] using h
        simp [hUpNeg, hFixed]

/-- Wrapper (argument order variant). -/
lemma energy_is_lyapunov_at_site'
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R:=ℝ) (NN:=NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    spec.E p (s.Up p u) ≤ spec.E p s :=
  energy_is_lyapunov_at_site (NN:=NN) (spec:=spec) p s u hcur

/-- Lyapunov (energy non‑increase) at a single site (completed proof).
Uses `energy_order_from_flip_id` and the flip relation with the identity hom. -/
lemma energy_is_lyapunov_at_site''
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R:=ℝ) (NN:=NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    spec.E p (NeuralNetwork.State.Up s p u) ≤ spec.E p s := by
  classical
  set sPos := updPos (NN:=NN) s u
  set sNeg := updNeg (NN:=NN) s u
  set net  := s.net p u
  set θ    := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by
    simp [L, net, θ, spec.localField_spec]
  have hdiff :
      spec.E p sPos - spec.E p sNeg =
        - (scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  set κ := scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)
  have hκpos : 0 < κ := by
    have hmo := TwoStateNeuralNetwork.m_order (NN:=NN)
    have : 0 < (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))
              - NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN))) := sub_pos.mpr hmo
    simpa [κ, scale, fid, RingHom.id_apply]
  have hκ : 0 ≤ κ := hκpos.le
  have hOrder :=
    energy_order_from_flip_id
      (NN:=NN) (spec:=spec) (p:=p) (κ:=κ) (L:=L)
      (sPos:=sPos) (sNeg:=sNeg) hdiff hκ
  have hup := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
  by_cases hθle : θ ≤ net
  · have hUpPos : s.Up p u = sPos := by
      simpa [net, θ, hθle] using hup
    cases hcur with
    | inl hPos =>
        have hs : sPos = s :=
          TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hPos
        have htriv : spec.E p sPos ≤ spec.E p sPos := le_rfl
        simp [hUpPos, hs]
    | inr hNeg =>
        have hs : sNeg = s :=
          TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hNeg
        have hL : 0 ≤ L := by
          have : θ ≤ net := hθle
          simpa [L] using sub_nonneg.mpr this
        have hLE : spec.E p sPos ≤ spec.E p sNeg := hOrder.left hL
        simp [hUpPos, hs]
        aesop
  · have hLt : net < θ := lt_of_not_ge hθle
    have hLle : L ≤ 0 := (sub_lt_zero.mpr hLt).le
    have hUpNeg : s.Up p u = sNeg := by
      have hnot : ¬ θ ≤ net := hθle
      simpa [net, θ, hnot] using hup
    cases hcur with
    | inl hPos =>
        have hs : sPos = s :=
          TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hPos
        have hLE : spec.E p sNeg ≤ spec.E p sPos := hOrder.right hLle
        simp [hUpNeg, hs]
        aesop
    | inr hNeg =>
        have hs : sNeg = s :=
          TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hNeg
        have htriv : spec.E p sNeg ≤ spec.E p sNeg := le_rfl
        simp [hUpNeg, hs]

/-- Restated helper with identical conclusion (wrapper). -/
lemma energy_is_lyapunov_at_site'''
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R:=ℝ) (NN:=NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    spec.E p (NeuralNetwork.State.Up s p u) ≤ spec.E p s :=
  energy_is_lyapunov_at_site (NN:=NN) (spec:=spec) p s u hcur

end EnergySpec'
end TwoState
