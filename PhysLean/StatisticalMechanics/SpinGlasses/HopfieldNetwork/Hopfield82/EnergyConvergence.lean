import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.Hopfield82.PhaseSpaceFlow
namespace Hopfield82

open NeuralNetwork State Matrix Finset Real

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U] [Nonempty U]

/-! ### Connection to Physical Systems -/

/--
The `spin_glass_analogy` formalizes the connection between Hopfield networks and
physical spin glass systems, as discussed in the paper.

From the paper (p.2555): "This case is isomorphic with an Ising model."
-/
def spin_glass_analogy (wθ : Params (HopfieldNetwork R U)) : Prop :=
  wθ.w.IsSymm ∧ ∀ i, wθ.w i i = 0

/--
The `energy_convergence` theorem formalizes the connection between energy minimization
and the convergence to fixed points.

From the paper (p.2555): "State changes will continue until a least (local) E is reached."
-/
theorem energy_convergence (wθ : Params (HopfieldNetwork R U)) (s : PhaseSpacePoint R U)
    (useq : ℕ → U) (hf : fair useq) :
  ∃ (p : PhaseSpacePoint R U), FixedPoint wθ p ∧
    (∀ q : PhaseSpacePoint R U, q ∈ BasinOfAttraction wθ p useq hf → p.E wθ ≤ q.E wθ) := by
  obtain ⟨N, hN⟩ := HopfieldNet_convergence_fair s useq hf
  let p := seqStates wθ s useq N
  have p_fixed : FixedPoint wθ p := hN
  use p, p_fixed
  intro q hq
  obtain ⟨n, hn, _⟩ := hq
  have energy_decreases_along_sequence :
    ∀ (q : PhaseSpacePoint R U) (m : ℕ),
      (seqStates wθ q useq m).E wθ ≤ q.E wθ := by
    intro q' m
    induction' m with m ih
    · simp only [seqStates, energy_decomposition, le_refl]
    · have : seqStates wθ q' useq (m+1) =
            (seqStates wθ q' useq m).Up wθ (useq m) := by
        simp only [seqStates]
      rw [this]
      have energy_step : ((seqStates wθ q' useq m).Up wθ (useq m)).E wθ ≤
                        (seqStates wθ q' useq m).E wθ :=
        energy_decrease wθ (seqStates wθ q' useq m) (useq m)
      exact le_trans energy_step ih
  have p_energy_leq_q : p.E wθ ≤ q.E wθ := by
    rw [← hn]
    exact energy_decreases_along_sequence q n

  exact p_energy_leq_q
