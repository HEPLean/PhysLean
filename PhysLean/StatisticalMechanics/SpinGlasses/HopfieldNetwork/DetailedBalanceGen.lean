import Mathlib.Probability.Kernel.Invariance

open MeasureTheory Filter Set

open scoped ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

namespace ProbabilityTheory.Kernel

/--
Reversibility (detailed balance) of a Markov kernel `κ` w.r.t. a (σ-finite) measure `π`:
for all measurable sets `A B`, the mass flowing from `A` to `B` equals that from `B` to `A`.
-/
def IsReversible (κ : Kernel α α) (π : Measure α) : Prop :=
  ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

/--
A reversible Markov kernel leaves the measure `π` invariant.
Proof uses detailed balance with `B = univ` and `κ x univ = 1`.
-/
theorem Invariant.of_IsReversible
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  have h' := (h_rev hs MeasurableSet.univ).symm
  have h'' : ∫⁻ x, κ x s ∂π = ∫⁻ x in s, κ x Set.univ ∂π := by
    simpa [Measure.restrict_univ] using h'
  have hConst : ∫⁻ x in s, κ x Set.univ ∂π = π s := by
    classical
    simp [measure_univ, lintegral_const, hs]
  have hπ : ∫⁻ x, κ x s ∂π = π s := h''.trans hConst
  calc
    (π.bind κ) s = ∫⁻ x, κ x s ∂π := Measure.bind_apply hs (Kernel.aemeasurable _)
    _ = π s := hπ

end ProbabilityTheory.Kernel
