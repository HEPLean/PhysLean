/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

open Mathlib Finset

/-
A `NeuralNetwork` models a neural network with:

- `R`: Type for weights and numeric computations.
- `U`: Type for neurons.
- `σ`: Type for neuron activation values.
- `[Zero R]`: `R` has a zero element.

It extends `Digraph U` and includes the network's architecture, activation functions, and constraints.
-/
structure NeuralNetwork (R U : Type) (σ : Type) [Zero R] extends Digraph U where
  /-- Input neurons. -/
  (Ui Uo Uh : Set U)
  /-- There is at least one input neuron. -/
  (hUi : Ui ≠ ∅)
  /-- There is at least one output neuron. -/
  (hUo : Uo ≠ ∅)
  /-- All neurons are either input, output, or hidden. -/
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  /-- Hidden neurons are not input or output neurons. -/
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  /-- Dimensions of input vectors for each neuron. -/
  (κ1 κ2 : U → ℕ)
  /-- Computes the net input to a neuron. -/
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  /-- Computes the activation of a neuron (polymorphic σ). -/
  (fact : ∀ u : U, σ → R → Vector R (κ2 u) → σ) -- current σ, net input, params → σ
  /-- Converts an activation value to a numeric output for computation. -/
  (fout : ∀ _ : U, σ → R)
  /-- Optional helper map σ → R (can be same as fout u if independent of u). -/
  (m : σ → R)
  /-- Predicate on activations (in σ). -/
  (pact : σ → Prop)
  /-- Predicate on weight matrices. -/
  (pw : Matrix U U R → Prop)
  /-- If all activations satisfy `pact`, then the next activations computed by `fact` also satisfy `pact`. -/
  (hpact :
    ∀ (w : Matrix U U R) (_ : ∀ u v, ¬ Adj u v → w u v = 0) (_ : pw w)
      (σv : (u : U) → Vector R (κ1 u)) (θ : (u : U) → Vector R (κ2 u))
      (current : U → σ),
      (∀ u_idx : U, pact (current u_idx)) →
      ∀ u_target : U,
        pact (fact u_target (current u_target)
                (fnet u_target (w u_target) (fun v => fout v (current v)) (σv u_target))
                (θ u_target)))

variable {R U σ : Type} [Zero R]

/-- `Params` is a structure that holds the parameters for a neural network `NN`. -/
structure Params (NN : NeuralNetwork R U σ) where
  (w : Matrix U U R)
  (hw : ∀ u v, ¬ NN.Adj u v → w u v = 0)
  (hw' : NN.pw w)
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  (θ : ∀ u : U, Vector R (NN.κ2 u))

namespace NeuralNetwork

structure State (NN : NeuralNetwork R U σ) where
  act : U → σ
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U σ : Type} [Zero R] {NN : NeuralNetwork R U σ}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U σ} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)
def onlyUi : Prop :=  ∃ σ0 : σ, ∀ u : U, u ∉ NN.Ui → s.act u = σ0
variable [DecidableEq U]

def Up {NN_local : NeuralNetwork R U σ} (s : NN_local.State) (wσθ : Params NN_local) (u_upd : U) : NN_local.State :=
  { act := fun v => if v = u_upd then
                      NN_local.fact u_upd (s.act u_upd)
                        (NN_local.fnet u_upd (wσθ.w u_upd) (fun n => s.out n) (wσθ.σ u_upd))
                        (wσθ.θ u_upd)
                    else
                      s.act v,
    hp := by
      intro v_target
      rw [ite_eq_dite]
      split_ifs with h_eq_upd_neuron
      · exact NN_local.hpact wσθ.w wσθ.hw wσθ.hw' wσθ.σ wσθ.θ s.act s.hp u_upd
      · exact s.hp v_target
  }

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => .Up (seqStates useq n) wσθ (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork
