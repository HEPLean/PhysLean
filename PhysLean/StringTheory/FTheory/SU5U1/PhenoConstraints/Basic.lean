/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Matter
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Meta.Informal.SemiFormal
/-!

## Phenomenological constraints on matter content

In arXiv:1507.05961, the authors give a number of phenomenological constraints on
the matter content of the SU(5) GUT model in F-theory with an additional U(1) symmetry.

Important terms coming from the superpotential are (0912.0853) :
`W ⊃ μ 5Hu 5̄Hd + 𝛽ᵢ 5̄Mⁱ5Hu + 𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ + W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
`+ W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd + W³ᵢⱼ 5̄Mⁱ 5̄Mʲ 5Hu 5Hu + W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`

Important terms coming from the Kahler potential are (0912.0853) :
`K ⊃ K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ + K²ᵢ 5̄Hu 5̄Hd 10ⁱ`

The following terms break R-parity:
- `β`, `λ`, `W²`, `W⁴`, `K¹`, `K²`
(These are the interactions with an odd number of matter fields.)

The following terms are involved in proton-decay:
- `W¹`, `W²`, `K¹`, `λ`

In what follows we constrain via `U(1)` charges
- `μ` (C1 in 1507.05961)
- `𝛽ᵢ` (C3 in 1507.05961)
- `𝜆ᵢⱼₖ` (C4 in 1507.05961)
- `W¹ᵢⱼₖₗ` (C2 in 1507.05961)
- `W²ᵢⱼₖ` (C2 (?) in 1507.05961)
- `K¹ᵢⱼₖ` (C5 in 1507.05961)
- `W⁴ᵢ` (C6 in 1507.05961)
- `K²ᵢ` (C7 in 1507.05961)
-/

namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

/-- The overall charge of the term `μ 5Hu 5̄Hd` -/
def chargeMuTerm (qHu qHd : I.allowedBarFiveCharges) : ℤ := - qHu.1 + qHd.1

/-- The charges of the term `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`. -/
def chargeW1Term (q5 : Multiset I.allowedBarFiveCharges) (q10 : Multiset I.allowedTenCharges) :
    Multiset ℤ :=
  (Multiset.product q10 (Multiset.product q10 (Multiset.product q10 q5))).map
  (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)

lemma chargeW1Term_subset_of_subset_ten (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 q10' : Multiset I.allowedTenCharges)
    (h : q10 ⊆ q10') :
    chargeW1Term q5bar q10 ⊆ chargeW1Term q5bar q10' := by
  rw [chargeW1Term, chargeW1Term]
  refine Multiset.map_subset_map ?_
  rw [@Multiset.subset_iff]
  intro x
  simp only [Multiset.mem_product, and_imp]
  aesop

lemma chargeW1Term_single_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeW1Term q5 q10)
    (a : I.allowedTenCharges) (ha : a ∈ q10) :
    0 ∉ chargeW1Term q5 {a} := by
  have h1 : chargeW1Term q5 {a} ⊆ chargeW1Term q5 q10 := by
    apply chargeW1Term_subset_of_subset_ten
    exact Multiset.singleton_subset.mpr ha
  exact fun a => h (h1 a)

lemma chargeW1Term_subset_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeW1Term q5 q10)
    (S : Multiset I.allowedTenCharges) (hS : S ⊆ q10) :
    0 ∉ chargeW1Term q5 S := by
  have h1 : chargeW1Term q5 S ⊆ chargeW1Term q5 q10 := by
    apply chargeW1Term_subset_of_subset_ten
    exact hS
  exact fun a => h (h1 a)
/-- The charges of the term `𝛽ᵢ 5̄Mⁱ5Hu`. -/
def chargeBetaTerm (q5bar : Multiset I.allowedBarFiveCharges) (qHu : I.allowedBarFiveCharges) :
    Multiset ℤ := q5bar.map (fun x => x.1 + (- qHu.1))

/-- The charges of the term `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`. -/
def chargeLambdaTerm (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) : Multiset ℤ :=
  (Multiset.product q5bar (Multiset.product q5bar q10)).map
  (fun x => x.1 + x.2.1 + x.2.2.1)

lemma chargeLambdaTerm_subset_of_subset_ten (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 q10' : Multiset I.allowedTenCharges)
    (h : q10 ⊆ q10') :
    chargeLambdaTerm q5bar q10 ⊆ chargeLambdaTerm q5bar q10' := by
  rw [chargeLambdaTerm, chargeLambdaTerm]
  refine Multiset.map_subset_map ?_
  rw [@Multiset.subset_iff]
  intro x
  simp only [Multiset.mem_product, and_imp]
  aesop

lemma chargeLambdaTerm_single_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeLambdaTerm q5 q10)
    (a : I.allowedTenCharges) (ha : a ∈ q10) :
    0 ∉ chargeLambdaTerm q5 {a} := by
  have h1 : chargeLambdaTerm q5 {a} ⊆ chargeLambdaTerm q5 q10 := by
    apply chargeLambdaTerm_subset_of_subset_ten
    exact Multiset.singleton_subset.mpr ha
  exact fun a => h (h1 a)

lemma chargeLambdaTerm_subset_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeLambdaTerm q5 q10)
    (S : Multiset I.allowedTenCharges) (hS : S ⊆ q10) :
    0 ∉ chargeLambdaTerm q5 S := by
  have h1 : chargeLambdaTerm q5 S ⊆ chargeLambdaTerm q5 q10 := by
    apply chargeLambdaTerm_subset_of_subset_ten
    exact hS
  exact fun a => h (h1 a)

/-- The charges of the term `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`. -/
def chargeK1Term (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) : Multiset ℤ :=
  (Multiset.product q10 (Multiset.product q10 q5bar)).map
  (fun x => x.1 + x.2.1 + (- x.2.2.1))

lemma chargeK1Term_subset_of_subset_ten (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 q10' : Multiset I.allowedTenCharges)
    (h : q10 ⊆ q10') :
    chargeK1Term q5bar q10 ⊆ chargeK1Term q5bar q10' := by
  rw [chargeK1Term, chargeK1Term]
  refine Multiset.map_subset_map ?_
  rw [@Multiset.subset_iff]
  intro x
  simp only [Multiset.mem_product, and_imp]
  aesop

lemma chargeK1Term_single_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeK1Term q5 q10)
    (a : I.allowedTenCharges) (ha : a ∈ q10) :
    0 ∉ chargeK1Term q5 {a} := by
  have h1 : chargeK1Term q5 {a} ⊆ chargeK1Term q5 q10 := by
    apply chargeK1Term_subset_of_subset_ten
    exact Multiset.singleton_subset.mpr ha
  exact fun a => h (h1 a)

lemma chargeK1Term_subset_q10 (q5 : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (h : 0 ∉ chargeK1Term q5 q10)
    (S : Multiset I.allowedTenCharges) (hS : S ⊆ q10) :
    0 ∉ chargeK1Term q5 S := by
  have h1 : chargeK1Term q5 S ⊆ chargeK1Term q5 q10 := by
    apply chargeK1Term_subset_of_subset_ten
    exact hS
  exact fun a => h (h1 a)

/-- The charges of the term `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`. -/
def chargeW4Term (q5bar : Multiset I.allowedBarFiveCharges)
    (qHd : I.allowedBarFiveCharges) (qHu : I.allowedBarFiveCharges) : Multiset ℤ :=
  q5bar.map (fun x => x.1 + qHd.1 + (- qHu.1) + (- qHu.1))

/-- The charges of the term `K²ᵢ 5̄Hu 5̄Hd 10ⁱ` -/
def chargeK2Term (q10 : Multiset I.allowedTenCharges)
    (qHu : I.allowedBarFiveCharges) (qHd : I.allowedBarFiveCharges) :
    Multiset ℤ :=
  q10.map (fun x => qHu.1 + qHd.1 + x.1)

/-- The charges of the term `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`. -/
def chargeW2Term (q10 : Multiset I.allowedTenCharges)
    (qHd : I.allowedBarFiveCharges) : Multiset ℤ :=
  (Multiset.product q10 (Multiset.product q10 q10)).map
  (fun x => x.1 + x.2.1 + x.2.2.1 + qHd.1)

/-- The charges associated with the term `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`-/
def chargeYukawaTop (q10 : Multiset I.allowedTenCharges)
    (qHu : I.allowedBarFiveCharges) : Multiset ℤ :=
  ((Multiset.product q10 q10)).map (fun x => x.1 + x.2.1 + (- qHu.1))

/-- The charges associated with the term `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd``. -/
def chargeYukawaBottom (q5bar : Multiset I.allowedBarFiveCharges)
    (q10 : Multiset I.allowedTenCharges) (qHd : I.allowedBarFiveCharges) : Multiset ℤ :=
  (Multiset.product q10 q5bar).map (fun x => x.1 + x.2.1 + qHd.1)

namespace MatterContent
variable {I : CodimensionOneConfig} (𝓜 : MatterContent I)

/-- A string containing the U(1)-charges associated with interaction terms. -/
def phenoCharges : String :=
  s!"
Charges associated with terms :
μ-term (μ 5Hu 5̄Hd) : {chargeMuTerm 𝓜.qHu 𝓜.qHd}
W¹-term (W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ) : {(chargeW1Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  (𝓜.quantaTen.map QuantaTen.q)).sort (LE.le) }
𝛽-term (𝛽ᵢ 5̄Mⁱ5Hu) : {(chargeBetaTerm (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  𝓜.qHu).sort LE.le}
𝜆-term (𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ) : {(chargeLambdaTerm (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  (𝓜.quantaTen.map QuantaTen.q)).sort LE.le}
K¹-term (K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ) : {(chargeK1Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  (𝓜.quantaTen.map QuantaTen.q)).sort LE.le}
W⁴-term (W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu) : {(chargeW4Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  𝓜.qHd 𝓜.qHu).sort LE.le}
K²-term (K²ᵢ 5̄Hu 5̄Hd 10ⁱ) : {(chargeK2Term (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHu
  𝓜.qHd).sort LE.le}
...
W²-term (W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd) : {(chargeW2Term (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHd).sort LE.le}
...
Top-Yukawa (λᵗᵢⱼ 10ⁱ 10ʲ 5Hu) : {(chargeYukawaTop (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHu).sort LE.le}
Bottom-Yukawa (λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd) : {(chargeYukawaBottom
  (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
  (𝓜.quantaTen.map QuantaTen.q)
  𝓜.qHd).sort LE.le}
"

/-- A proposition which is true when the `μ`-term (`5Hu 5̄Hd`) does not obey the additional
  `U(1)` symmetry in the model, and is therefore constrained. -/
def MuTermU1Constrained : Prop := chargeMuTerm 𝓜.qHu 𝓜.qHd ≠ 0

instance : Decidable 𝓜.MuTermU1Constrained := instDecidableNot

/-- A proposition which is true
  when the R-parity violating terms all do not obey the additional
  `U(1)` symmetry in the model, and are therefore constrained.
  This corresponds to the terms:
- `𝛽ᵢ 5̄Mⁱ5Hu`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
-/
def RParityU1Constrained : Prop :=
  --`𝛽ᵢ 5̄Mⁱ5Hu`
  0 ∉ chargeBetaTerm (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) 𝓜.qHu
  -- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
  ∧ 0 ∉ chargeLambdaTerm (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q)
  -- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
  ∧ 0 ∉ chargeW2Term (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHd
  -- `W⁴ᵢ 5̄Mⁱ 5̄Hd 5Hu 5Hu`
  ∧ 0 ∉ chargeW4Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) 𝓜.qHd 𝓜.qHu
  -- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
  ∧ 0 ∉ chargeK1Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q)
  -- `K²ᵢ 5̄Hu 5̄Hd 10ⁱ`
  ∧ 0 ∉ chargeK2Term (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHu 𝓜.qHd

instance : Decidable 𝓜.RParityU1Constrained := instDecidableAnd

/-- A proposition which is true when the terms in the super-potential and the Kahler potential
  contributing to proton decay do not obey the additional `U(1)` symmetry in the model,
  and are therefore constrained.
  This corresponds to the terms
- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
-/
def ProtonDecayU1Constrained : Prop :=
  -- `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ`
  0 ∉ chargeW1Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) (𝓜.quantaTen.map QuantaTen.q)
  -- `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ`
  ∧ 0 ∉ chargeLambdaTerm (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q)
  -- `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`
  ∧ 0 ∉ chargeW2Term (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHd
  -- `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
  ∧ 0 ∉ chargeK1Term (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q)

instance : Decidable 𝓜.ProtonDecayU1Constrained := instDecidableAnd

/-- The condition on the matter content for there to exist at least one copy of the coupling
- `λᵗᵢⱼ 10ⁱ 10ʲ 5Hu`
-/
def HasATopYukawa (𝓜 : MatterContent I) : Prop :=
  0 ∈ chargeYukawaTop (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHu

instance : Decidable 𝓜.HasATopYukawa :=
  Multiset.decidableMem 0 (chargeYukawaTop (Multiset.map QuantaTen.q 𝓜.quantaTen) 𝓜.qHu)

/-- The condition on the matter content for there to exist at least one copy of the coupling
- `λᵇᵢⱼ 10ⁱ 5̄Mʲ 5̄Hd`
-/
def HasABottomYukawa (𝓜 : MatterContent I) : Prop :=
  0 ∈ chargeYukawaBottom (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) 𝓜.qHu

instance : Decidable 𝓜.HasABottomYukawa :=
  Multiset.decidableMem _ _

/-!

## More sophisticated checks
-/

lemma lambdaTerm_K1Term_W1Term_subset_check {I : CodimensionOneConfig} {n : ℕ} (𝓜 : MatterContent I)
    (hcard : 𝓜.quantaBarFiveMatter.card = n) (h : 𝓜.ProtonDecayU1Constrained)
    (S : Multiset (I.allowedTenCharges))
    (hS : ∀ (F : Finset { x // x ∈ I.allowedBarFiveCharges }), F.card = n →
      F ⊆ Finset.univ → F.card = n →
      (0 ∈ chargeW1Term F.val S ∨ 0 ∈ chargeLambdaTerm F.val S) ∨ 0 ∈ chargeK1Term F.val S:= by
      decide) :
      ¬ S ⊆ 𝓜.quantaTen.map QuantaTen.q := by
  intro hn
  have hL1 := chargeLambdaTerm_subset_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.2.1 _ hn
  have hW1 := chargeW1Term_subset_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.1 _ hn
  have hK1 := chargeK1Term_subset_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.2.2.2 _ hn
  apply not_or_intro (not_or_intro hW1 hL1) hK1
  have h5 : ((𝓜.quantaBarFiveMatter).map QuantaBarFive.q).card = n := by
    rw [Multiset.card_map]
    exact hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at h5 ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at h5 ⊢
  have hW1T : F ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = n) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ F
  revert F
  simp only [Finset.card_val, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_powerset,
    Int.reduceNeg, and_imp]
  exact hS

lemma lambdaTerm_K1Term_W1Term_singleton_check {I : CodimensionOneConfig} {n : ℕ}
    (𝓜 : MatterContent I)
    (hcard : 𝓜.quantaBarFiveMatter.card = n) (h : 𝓜.ProtonDecayU1Constrained)
    (a : (I.allowedTenCharges))
    (ha : ∀ (F : Finset { x // x ∈ I.allowedBarFiveCharges }), F.card = n →
      F ⊆ Finset.univ → F.card = n →
      (0 ∈ chargeW1Term F.val {a} ∨ 0 ∈ chargeLambdaTerm F.val {a}) ∨
      0 ∈ chargeK1Term F.val {a} := by decide) :
    a ∉ 𝓜.quantaTen.map QuantaTen.q := by
  intro hn
  have hL1 := chargeLambdaTerm_single_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.2.1 _ hn
  have hW1 := chargeW1Term_single_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.1 _ hn
  have hK1 := chargeK1Term_single_q10 (𝓜.quantaBarFiveMatter.map QuantaBarFive.q)
    (𝓜.quantaTen.map QuantaTen.q) h.2.2.2 _ hn
  apply not_or_intro (not_or_intro hW1 hL1) hK1
  have h5 : ((𝓜.quantaBarFiveMatter).map QuantaBarFive.q).card = n := by
    rw [Multiset.card_map]
    exact hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at h5 ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at h5 ⊢
  have hW1T : F ∈ (Finset.powerset (Finset.univ)).filter (fun x => x.card = n) := by
    rw [Finset.mem_filter]
    rw [Finset.mem_powerset]
    simp_all only [Finset.card_val, and_true]
    exact Finset.subset_univ F
  revert F
  simp only [Finset.card_val, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_powerset,
    Int.reduceNeg, and_imp]
  exact ha

end MatterContent
end SU5U1

end FTheory
