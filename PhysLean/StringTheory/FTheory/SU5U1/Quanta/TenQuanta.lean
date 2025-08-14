/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.ToList
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Lemmas
/-!

# Quanta of 10d representations

The 10d representations of the `SU(5)×U(1)` carry
the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## Key definitions

- `TenQuanta` is the type of quanta of 10d representations.
- `TenQuanta.toFluxesTen` is the underlying `FluxesTen` of a `TenQuanta`.
- `TenQuanta.toCharges` is the underlying Multiset charges of a `TenQuanta`.
- `TenQuanta.reduce` is the reduction of a `TenQuanta` which adds together
  all the fluxes corresponding to the same charge (i.e. representation).
- `TenQuanta.anomalyCoefficent` is the anomaly coefficent associated with a `TenQuanta`.
- `TenQuanta.ofChargesExpand` is the `TenQuanta` with fluxes
  `{(1, 0), (1, 0), (1, 0)}` or `{(1, 1), (1, -1), (1, 0)}` and finite set of charges equal to a
  given `c`.

## Key theorems

- `mem_ofChargesExpand_map_reduce_iff` states that a `TenQuanta` is in the
  image of `ofChargesExpand c` under `reduce` if and only if it is a `TenQuanta` with
  charges equal to `c` and fluxes which have no exotics or zero.
-/
namespace FTheory

namespace SU5U1
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta of w0d representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev TenQuanta : Type := Multiset (ℤ × ℤ × ℤ)

namespace TenQuanta

/-- The underlying `FluxesTen` from a `TenQuanta`. -/
def toFluxesTen (x : TenQuanta) : FluxesTen := x.map Prod.snd

/-- The underlying Multiset charges from a `TenQuanta`. -/
def toCharges (x : TenQuanta) : Multiset ℤ := x.map Prod.fst

/-!

## Reduce

-/

/-- The `reduce` of `TenQuanta` is a new `TenQuanta` with all the fluxes
  corresponding to the same charge (i.e. represenation) added together. -/
def reduce (x : TenQuanta) : TenQuanta :=
  x.toCharges.dedup.map fun q10 => (q10, ((x.filter (fun f => f.1 = q10)).map (fun y => y.2)).sum)

lemma reduce_nodup (x : TenQuanta) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : TenQuanta) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

lemma reduce_toCharges (x : TenQuanta) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

lemma reduce_eq_val (x : TenQuanta) :
    x.reduce = (x.toCharges.toFinset.image fun q10 =>
      (q10, ((x.filter (fun f => f.1 = q10)).map (fun y => y.2)).sum)).val := by
  simp only [Finset.image_val, Multiset.toFinset_val]
  rw [← reduce]
  simp

lemma mem_reduce_iff (x : TenQuanta) (p : ℤ × ℤ × ℤ) :
    p ∈ x.reduce ↔ p.1 ∈ x.toCharges ∧
      p.2 = ((x.filter (fun f => f.1 = p.1)).map (fun y => y.2)).sum := by
  simp [reduce]
  constructor
  · intro h
    obtain ⟨q, h1, rfl⟩ := h
    simp_all
  · simp only [and_imp]
    intro h1 h2
    use p.1
    simp_all
    rw [← h2]

lemma reduce_filter (x : TenQuanta) (q : ℤ) (h : q ∈ x.toCharges) :
    x.reduce.filter (fun f => f.1 = q) =
    {(q, ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum)} := by
  simp [reduce]
  rw [Multiset.filter_map]
  simp only [Function.comp_apply]
  have hx : (Multiset.filter (fun x => x = q) x.toCharges.dedup) = {q} := by
    refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · refine Multiset.Nodup.filter (fun x => x = q) ?_
      exact Multiset.nodup_dedup x.toCharges
    · exact Multiset.nodup_singleton q
    intro a
    simp only [Multiset.mem_filter, Multiset.mem_dedup, Multiset.mem_singleton,
      and_iff_right_iff_imp]
    intro h'
    subst h'
    exact h
  rw [hx]
  simp

@[simp]
lemma reduce_reduce (x : TenQuanta) :
    x.reduce.reduce = x.reduce := by
  refine Multiset.Nodup.toFinset_inj ?_ ?_ ?_
  · exact reduce_nodup x.reduce
  · exact reduce_nodup x
  ext p
  simp only [Multiset.mem_toFinset]
  rw [mem_reduce_iff, reduce_toCharges, mem_reduce_iff]
  simp only [Multiset.mem_dedup, and_congr_right_iff]
  intro hp
  have h1 (a b c : ℤ × ℤ) (h : b = c) : a = b ↔ a = c := by subst h; rfl
  apply h1
  rw [reduce_filter]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  exact hp

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : TenQuanta) (f : ℤ → ℤ × ℤ →+ M) :
    (x.reduce.map fun (q, x) => f q x).sum = (x.map fun (q, x) => f q x).sum := by
  calc _
      _ = ∑ q ∈ x.toCharges.toFinset,
          f q ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q)).map (fun y => f q y.2))).sum := by
        congr
        funext q5
        rw [AddMonoidHom.map_multiset_sum, Multiset.map_map]
        rfl
      _ = (x.toCharges.dedup.bind fun q =>
          ((x.filter (fun f => f.1 = q)).map (fun y => f q y.2))).sum := by
        rw [Multiset.sum_bind]
        simp [Finset.sum]
      _ = (((x.toCharges.dedup.bind fun q =>
          ((x.filter (fun f => f.1 = q)))).map (fun y => f y.1 y.2))).sum := by
        congr
        rw [Multiset.map_bind]
        congr
        funext q
        refine Multiset.map_congr rfl ?_
        intro y hy
        simp at hy
        rw [hy.2]
      _ = ((x.map (fun y => f y.1 y.2))).sum := by
        congr
        apply Multiset.ext.mpr
        intro p
        trans ((x.map Prod.fst).dedup.map (fun y => if p.1 = y then x.count p else 0)).sum
        · rw [@Multiset.count_bind]
          congr
          funext q5
          rw [Multiset.count_filter]
        by_cases h_mem : p.1 ∈ x.map Prod.fst
        · have h_mem_dedup : p.1 ∈ (x.map Prod.fst).dedup := by rwa [Multiset.mem_dedup]
          rw [Multiset.sum_map_eq_nsmul_single p.1]
          simp only [Multiset.nodup_dedup, ↓reduceIte, smul_eq_mul]
          have h_count_one : Multiset.count p.1 (Multiset.map Prod.fst x).dedup = 1 := by
            refine Multiset.count_eq_one_of_mem ?_ h_mem_dedup
            exact Multiset.nodup_dedup (Multiset.map Prod.fst x)
          simp [h_count_one]
          intro q5' h h2
          simp_all [eq_comm]
        · rw [Multiset.sum_eq_zero]
          refine Eq.symm (Multiset.count_eq_zero_of_notMem ?_)
          intro h
          have h_mem : p.1 ∈ Multiset.map Prod.fst x := by
            simp_all [h]
          (expose_names; exact h_mem_1 h_mem)
          intro p' hp
          simp at hp
          obtain ⟨q5', ⟨f1, f2, hf⟩, hp'⟩ := hp
          by_cases h_eq : p.1 = q5'
          · simp_all
          · simp_all


lemma reduce_eq_self_of_ofCharges_nodup (x : TenQuanta) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce]
  rw [Multiset.Nodup.dedup h]
  simp [toCharges]
  conv_rhs => rw [← Multiset.map_id x]
  apply Multiset.map_congr rfl
  intro p hp
  simp
  have x_noDup : x.Nodup := Multiset.Nodup.of_map Prod.fst h
  suffices (Multiset.filter (fun f => f.1 = p.1) x) = {p} by simp [this]
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.Nodup.filter (fun f => f.1 = p.1) x_noDup
  · exact Multiset.nodup_singleton p
  intro p'
  simp
  constructor
  · rintro ⟨h1, h2⟩
    simp [toCharges] at h
    rw [propext (Multiset.nodup_map_iff_inj_on x_noDup)] at h
    apply h
    · exact h1
    · exact hp
    · exact h2
  · rintro ⟨rfl⟩
    simp_all

/-!
## Anomaly cancellation

-/
/--
  The anomaly coefficent of a `TenQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
    see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficent (F : TenQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, 3 * (F.map fun x => x.1 * x.1 * x.2.2).sum)

lemma anomalyCoefficent_of_reduce (F : TenQuanta) :
    F.reduce.anomalyCoefficent = F.anomalyCoefficent := by
  simp [anomalyCoefficent]
  constructor
  · let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
      toFun := fun x => q5 * x.2
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul, mul_add] }
    have h1 := reduce_sum_eq_sum_toCharges F f
    simpa [f] using h1
  · let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
      toFun := fun x => q5 * q5 * x.2
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul, mul_add] }
    have h1 := reduce_sum_eq_sum_toCharges F f
    simpa [f] using h1

/-!

## toChargesExpand

-/

open SuperSymmetry.SU5.Charges

/-- Given a finite set of charges `c` the `TenQuanta`
  with fluxes `{(1, 0), (1, 0), (1, 0)}` and `{(1, 1), (1, -1), (1, 0)}`
  and finite set of charges equal to `c`. -/
def ofChargesExpand (c : Finset ℤ) : Multiset TenQuanta :=
  /- The {(1, 0), (1, 0), (1, 0)} case. -/
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S10 : Multiset (Multiset ℤ) := toMultisetsThree c
  let F1 : Multiset TenQuanta :=
    (S10.map (fun s => s.map (fun z => (z, 1, 0)))).filter (fun s => c.val ≤ s.toCharges)
  /- The {(1, 1), (1, -1), (1, 0)} case. -/
  let F2 : Multiset TenQuanta := ((c.product <| c.product <| c).val.map
    fun (x, y, z) => {(x, 1, 1), (y, 1, -1), (z, 1, 0)}).filter (fun s => c.val ≤ s.toCharges)
  /- All together-/
  F1 + F2

lemma toFluxesFive_of_mem_ofChargesExpand (c : Finset ℤ)
    {x : TenQuanta} (h : x ∈ ofChargesExpand c) :
    x.toFluxesTen = {(1, 0), (1, 0), (1, 0)}
    ∨ x.toFluxesTen = {(1, 1), (1, -1), (1, 0)}:= by
  simp [ofChargesExpand] at h
  rcases h with h | h
  · obtain ⟨⟨s, h, rfl⟩, h'⟩ := h
    left
    simp [toFluxesTen]
    rw [h.2]
    decide
  · obtain ⟨⟨q1, q2, q3, h, rfl⟩, h'⟩ := h
    simp [toFluxesTen]

lemma toCharges_of_mem_ofChargesExpand (c : Finset ℤ)
    {x : TenQuanta} (h : x ∈ ofChargesExpand c) :
    x.toCharges.toFinset = c := by
  simp [ofChargesExpand] at h
  rcases h with h | h
  · obtain ⟨⟨s, h, rfl⟩, h'⟩ := h
    simp_all [toCharges]
    ext a
    simp only [Multiset.mem_toFinset]
    constructor
    · intro hr
      apply h.1
      simpa using hr
    · intro hr
      exact Multiset.mem_of_le h' hr
  · obtain ⟨⟨q1, q2, q3, h, rfl⟩, h'⟩ := h
    simp_all [toCharges]
    refine Eq.symm ((fun {α} {s₁ s₂} => Finset.ext_iff.mpr) ?_)
    intro a
    constructor
    · intro hr
      simpa using Multiset.mem_of_le h' hr
    · intro hr
      simp at hr
      simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product] at h
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

lemma mem_ofChargesExpand_of_toCharges_toFluxesTen (c : Finset ℤ) {x : TenQuanta}
    (h : x.toCharges.toFinset = c) (h2 : x.toFluxesTen =
      {(1, 0), (1, 0), (1, 0)} ∨ x.toFluxesTen = {(1, 1), (1, -1), (1, 0)}) :
    x ∈ ofChargesExpand c := by
  simp [ofChargesExpand]
  rcases h2 with h2 | h2
  · left
    subst h
    simp only [Multiset.toFinset_subset, Multiset.toFinset_val]
    apply And.intro
    · use x.toCharges
      simp only [Multiset.Subset.refl, true_and]
      apply And.intro
      · simp [toCharges]
        trans x.toFluxesTen.card
        · simp [toFluxesTen]
        rw [h2]
        decide
      · trans Multiset.map (fun z => z) x
        swap
        · simp
        rw [toCharges, Multiset.map_map]
        apply Multiset.map_congr
        rfl
        intro p hp
        simp only [Function.comp_apply]
        have h1 : p.2 ∈ x.toFluxesTen := by
          simp [toFluxesTen]
          use p.1
        rw [h2] at h1
        simp at h1
        change _ = (p.1, p.2)
        rw [h1]
    · exact Multiset.dedup_le x.toCharges
  · right
    have h2' := h2
    simp [toFluxesTen] at h2
    rw [← Multiset.map_eq_cons] at h2
    obtain ⟨p1, hp1, hp1_2, h2⟩ := h2
    rw [← Multiset.map_eq_cons] at h2
    obtain ⟨p2, hp2, hp2_2, h2⟩ := h2
    rw [Multiset.map_eq_singleton] at h2
    obtain ⟨p3, hp3, hp3_2⟩ := h2
    apply And.intro
    · use p1.1, p2.1, p3.1
      simp only [SProd.sprod, Multiset.instSProd, Multiset.mem_product]
      subst h
      simp only [Multiset.toFinset_val, Multiset.mem_dedup, Int.reduceNeg]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simp [toCharges]
        use p1.2.1, p1.2.2
      · simp [toCharges]
        use p2.2.1, p2.2.2
        apply Multiset.erase_subset p1 x hp2
      · simp [toCharges]
        use p3.2.1, p3.2.2
        apply Multiset.erase_subset p1 x
        apply Multiset.erase_subset p2 _
        rw [hp3]
        simp
      · symm
        refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ ?_)
        · refine (Multiset.cons_le_of_notMem ?_).mpr ⟨?_, ?_⟩
          · simp
          · rw [← hp1_2]
            exact hp1
          refine (Multiset.cons_le_of_notMem ?_).mpr ⟨?_, ?_⟩
          · simp
          · rw [← hp2_2]
            apply Multiset.erase_subset p1 x
            exact hp2
          simp only [Multiset.singleton_le]
          rw [← hp3_2]
          apply Multiset.erase_subset p1 x
          apply Multiset.erase_subset p2 _
          rw [hp3]
          simp
        · trans x.toFluxesTen.card
          · simp [toFluxesTen]
          rw [h2']
          simp
    · rw [← h]
      simp only [Multiset.toFinset_val]
      exact Multiset.dedup_le x.toCharges

lemma mem_ofChargesExpand_iff (c : Finset ℤ) {x : TenQuanta} :
    x ∈ ofChargesExpand c ↔
    x.toCharges.toFinset = c ∧ (x.toFluxesTen = {(1, 0), (1, 0), (1, 0)}
    ∨ x.toFluxesTen = {(1, 1), (1, -1), (1, 0)}) := by
  constructor
  · intro h
    constructor
    exact toCharges_of_mem_ofChargesExpand c h
    exact toFluxesFive_of_mem_ofChargesExpand c h
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact mem_ofChargesExpand_of_toCharges_toFluxesTen c h1 h2

lemma mem_ofChargesExpand_of_noExotics_hasNoZero (F : TenQuanta) (c : Finset ℤ)
    (hc : F.toCharges.toFinset = c)
    (h1 : F.toFluxesTen.NoExotics) (h2 : F.toFluxesTen.HasNoZero) :
    ∃ y ∈ ofChargesExpand c, y.reduce = F.reduce := by
  have hf : F.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
    simp_all
    exact h2
  simp [FluxesTen.elemsNoExotics] at hf
  rcases hf with hf | hf | hf | hf | hf | hf
  · use F
    simp only [and_true]
    rw [mem_ofChargesExpand_iff]
    simp_all
  · use F
    simp only [and_true]
    rw [mem_ofChargesExpand_iff]
    simp_all
  · have F_card : F.card = 2 := by
      trans F.toFluxesTen.card
      · simp [toFluxesTen]
      rw [hf]
      decide
    rw [Multiset.card_eq_two] at F_card
    obtain ⟨⟨q1, a1⟩, ⟨q2, a2⟩, rfl⟩ := F_card
    simp [toFluxesTen] at hf
    rw [Multiset.cons_eq_cons] at hf
    simp at hf
    rcases hf with ⟨rfl, rfl⟩ | ⟨hf, ⟨rfl, rfl⟩⟩
    · use {(q1, 1, 0), (q2, 1, 0), (q2, 1, 0)}
      simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
      simp [reduce, toCharges]
      by_cases hq1q2 : q1 = q2
      · subst hq1q2
        simp [@Multiset.filter_singleton]
      · have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
            refine Multiset.Nodup.dedup ?_
            refine Multiset.nodup_cons.mpr ?_
            simpa using hq1q2
        have h2 : (q1 ::ₘ q2 ::ₘ {q2}).dedup = {q1, q2} := by
          refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
          · exact Multiset.nodup_dedup (q1 ::ₘ q2 ::ₘ {q2})
          · simpa using hq1q2
          intro a
          simp
        rw [h1, h2]
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.filter_cons_of_pos,
          Multiset.sum_cons, Multiset.map_singleton]
        have hq2q1 :¬ q2 = q1 := by omega
        congr 2
        · simp [@Multiset.filter_singleton, hq1q2, hq2q1]
        · simp [@Multiset.filter_singleton, hq1q2, hq2q1]
    · use {(q1, 1, 0), (q1, 1, 0), (q2, 1, 0)}
      simp [mem_ofChargesExpand_iff]
      simp [toCharges, toFluxesTen]
      apply And.intro
      · simp [← hc, toCharges]
      · simp [reduce, toCharges]
        by_cases hq1q2 : q1 = q2
        · subst hq1q2
          simp [@Multiset.filter_singleton]
        · have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
            refine Multiset.Nodup.dedup ?_
            refine Multiset.nodup_cons.mpr ?_
            simpa using hq1q2
          rw [h1]
          simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.filter_cons_of_pos,
            Multiset.sum_cons, Multiset.map_singleton]
          have hq2q1 :¬ q2 = q1 := by omega
          simp [@Multiset.filter_singleton, hq1q2, hq2q1]
  · have F_card : F.card = 2 := by
      trans F.toFluxesTen.card
      · simp [toFluxesTen]
      rw [hf]
      decide
    rw [Multiset.card_eq_two] at F_card
    obtain ⟨⟨q1, a1⟩, ⟨q2, a2⟩, rfl⟩ := F_card
    simp [toFluxesTen] at hf
    rw [Multiset.cons_eq_cons] at hf
    simp at hf
    rcases hf with ⟨rfl, rfl⟩ | ⟨hf, ⟨rfl, rfl⟩⟩
    · use {(q2, 1, 1), (q1, 1, -1), (q2, 1, 0)}
      simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
      simp [reduce, toCharges]
      by_cases hq1q2 : q1 = q2
      · subst hq1q2
        simp [@Multiset.filter_singleton]
      have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
        refine Multiset.Nodup.dedup (Multiset.nodup_cons.mpr ?_)
        simpa using hq1q2
      rw [h1]
      have hq2q1 :¬ q2 = q1 := by omega
      simp [@Multiset.filter_singleton, hq1q2, hq2q1]
    · use {(q1, 1, 1), (q2, 1, -1), (q1, 1, 0)}
      simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
      simp [reduce, toCharges]
      by_cases hq1q2 : q1 = q2
      · subst hq1q2
        simp [@Multiset.filter_singleton]
      have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
        refine Multiset.Nodup.dedup (Multiset.nodup_cons.mpr ?_)
        simpa using hq1q2
      rw [h1]
      have hq2q1 :¬ q2 = q1 := by omega
      simp [Multiset.filter_singleton, hq1q2, hq2q1, Finset.pair_comm, Multiset.cons_eq_cons]
  · have F_card : F.card = 2 := by
      trans F.toFluxesTen.card
      · simp [toFluxesTen]
      rw [hf]
      decide
    rw [Multiset.card_eq_two] at F_card
    obtain ⟨⟨q1, a1⟩, ⟨q2, a2⟩, rfl⟩ := F_card
    simp [toFluxesTen] at hf
    rw [Multiset.cons_eq_cons] at hf
    simp at hf
    rcases hf with ⟨rfl, rfl⟩ | ⟨hf, ⟨rfl, rfl⟩⟩
    · use {(q1, 1, 1), (q2, 1, -1), (q2, 1, 0)}
      simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
      simp [reduce, toCharges]
      by_cases hq1q2 : q1 = q2
      · subst hq1q2
        simp [@Multiset.filter_singleton]
      have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
        refine Multiset.Nodup.dedup (Multiset.nodup_cons.mpr ?_)
        simpa using hq1q2
      rw [h1]
      have hq2q1 :¬ q2 = q1 := by omega
      simp [@Multiset.filter_singleton, hq1q2, hq2q1]
    · use {(q2, 1, 1), (q1, 1, -1), (q1, 1, 0)}
      simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
      simp [reduce, toCharges]
      by_cases hq1q2 : q1 = q2
      · subst hq1q2
        simp [@Multiset.filter_singleton]
      have h1 : (q1 ::ₘ {q2}).dedup = {q1, q2} := by
        refine Multiset.Nodup.dedup (Multiset.nodup_cons.mpr ?_)
        simpa using hq1q2
      rw [h1]
      have hq2q1 :¬ q2 = q1 := by omega
      simp [Multiset.filter_singleton, hq1q2, hq2q1, Finset.pair_comm, Multiset.cons_eq_cons]
  · have F_card : F.card = 1 := by
      trans F.toFluxesTen.card
      · simp [toFluxesTen]
      rw [hf]
      decide
    rw [Multiset.card_eq_one] at F_card
    obtain ⟨⟨q1, a1⟩, rfl⟩ := F_card
    simp [toFluxesTen] at hf
    rcases hf with rfl
    use {(q1, 1, 0), (q1, 1, 0), (q1, 1, 0)}
    simp [mem_ofChargesExpand_iff, toCharges, toFluxesTen, ← hc, toCharges]
    simp [reduce, toCharges, Multiset.filter_singleton]

lemma reduce_hasNoZeros_of_mem_ofChargesExpand (c : Finset ℤ) (F : TenQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesTen.HasNoZero := by
  simp [reduce, toFluxesTen, FluxesTen.HasNoZero]
  intro x hx
  have hs : (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F))
      ∈ F.toFluxesTen.powerset := by
    simp [toFluxesTen]
  have h1 : Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F) ≠ 0 := by
    simp only [ne_eq, Multiset.map_eq_zero]
    rw [@Multiset.filter_eq_nil]
    simp [Prod.forall, not_forall, Classical.not_imp, Decidable.not_not, exists_and_right,
      exists_eq_right]
    simp [toCharges] at hx
    obtain ⟨a, b, h⟩ := hx
    use a, b
  generalize (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F)) = s at *
  rw [mem_ofChargesExpand_iff] at h
  rcases h with ⟨h1, h | h⟩
  all_goals
  · rw [h] at hs
    fin_cases hs
    · simp at h1
    all_goals
    · decide

lemma reduce_noExotics_of_mem_ofChargesExpand (c : Finset ℤ) (F : TenQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesTen.NoExotics := by
  simp [FluxesTen.NoExotics]
  have h1 : (Multiset.filter (fun x => x < 0)
      (Multiset.map (fun f => f.1 + f.2) F.reduce.toFluxesTen)) = ∅ := by
    simp only [Multiset.empty_eq_zero]
    rw [@Multiset.filter_eq_nil]
    intro a ha
    simp at ha
    obtain ⟨c, b, h1, h2⟩ := ha
    obtain ⟨s, h'⟩ : ∃ s ∈ F.toFluxesTen.powerset, (c, b) = s.sum := by
      simp [reduce, toFluxesTen] at h1
      obtain ⟨q, q_mem, h1⟩ := h1
      use (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = q) F))
      simp_all [toFluxesTen]
    have ha : a = s.sum.1 + s.sum.2 := by
      rw [← h2, ← h'.2]
    rw [ha]
    have h2 := h'.1
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h] at h2
      fin_cases h2
      all_goals
      · decide
  have h2 : (Multiset.filter (fun x => x < 0) (Multiset.map (fun f => f.1) F.reduce.toFluxesTen))
      = ∅ := by
    simp only [Multiset.empty_eq_zero]
    rw [@Multiset.filter_eq_nil]
    intro a ha
    simp at ha
    obtain ⟨c, h1⟩ := ha
    obtain ⟨s, h'⟩ : ∃ s ∈ F.toFluxesTen.powerset, (a, c) = s.sum := by
      simp [reduce, toFluxesTen] at h1
      obtain ⟨q, q_mem, h1⟩ := h1
      use (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = q) F))
      simp_all [toFluxesTen]
    have ha : a = s.sum.1 := by
      rw [← h'.2]
    rw [ha]
    have h2 := h'.1
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h] at h2
      fin_cases h2
      all_goals
      · decide

  have h3 : (Multiset.filter (fun x => x < 0)
    (Multiset.map (fun f => f.1 - f.2) F.reduce.toFluxesTen)) = ∅ := by
    simp only [Multiset.empty_eq_zero]
    rw [@Multiset.filter_eq_nil]
    intro a ha
    simp at ha
    obtain ⟨c, b, h1, h2⟩ := ha
    obtain ⟨s, h'⟩ : ∃ s ∈ F.toFluxesTen.powerset, (c, b) = s.sum := by
      simp [reduce, toFluxesTen] at h1
      obtain ⟨q, q_mem, h1⟩ := h1
      use (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = q) F))
      simp_all [toFluxesTen]
    have ha : a = s.sum.1 - s.sum.2 := by
      rw [← h2, ← h'.2]
    rw [ha]
    have h2 := h'.1
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h] at h2
      fin_cases h2
      all_goals
      · decide
  have sum_1 : (Multiset.map Prod.fst F.reduce.toFluxesTen).sum
      = (Multiset.map Prod.fst F.toFluxesTen).sum := by
      rw [toFluxesTen, Multiset.map_map]
      let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
        toFun := fun x => x.1
        map_add' := by simp
        map_zero' := by simp
      }
      change (Multiset.map (fun (q5, x) => f q5 x) F.reduce).sum = _
      rw [reduce_sum_eq_sum_toCharges F]
      simp [f, toFluxesTen]
  have sum_2 : (Multiset.map Prod.snd F.reduce.toFluxesTen).sum
      = (Multiset.map Prod.snd F.toFluxesTen).sum := by
      rw [toFluxesTen, Multiset.map_map]
      let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
        toFun := fun x => x.2
        map_add' := by simp
        map_zero' := by simp
      }
      change (Multiset.map (fun (q5, x) => f q5 x) F.reduce).sum = _
      rw [reduce_sum_eq_sum_toCharges F]
      simp [f, toFluxesTen]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FluxesTen.numChiralQ_eq_sum_sub_numAntiChiralQ]
    simp [FluxesTen.numAntiChiralQ, FluxesTen.chiralIndicesOfQ]
    rw [h2, sum_1]
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h]
      decide
  · simp [FluxesTen.numAntiChiralQ, FluxesTen.chiralIndicesOfQ]
    rw [h2]
    simp
  · rw [FluxesTen.numChiralU_eq_sum_sub_numAntiChiralU]
    simp [FluxesTen.numAntiChiralU, FluxesTen.chiralIndicesOfU]
    rw [h3,sum_1, sum_2]
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h]
      decide
  · simp [FluxesTen.numAntiChiralU, FluxesTen.chiralIndicesOfU]
    rw [h3]
    simp
  · rw [FluxesTen.numChiralE_eq_sum_sub_numAntiChiralE]
    simp [FluxesTen.numAntiChiralE, FluxesTen.chiralIndicesOfE]
    rw [h1,sum_1, sum_2]
    rw [mem_ofChargesExpand_iff] at h
    rcases h with ⟨h1, h | h⟩
    all_goals
      rw [h]
      decide
  · simp [FluxesTen.numAntiChiralE, FluxesTen.chiralIndicesOfE]
    rw [h1]
    simp

lemma reduce_mem_elemsNoExotics_of_mem_ofChargesExpand (c : Finset ℤ) (F : TenQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
  rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
  constructor
  · exact reduce_noExotics_of_mem_ofChargesExpand c F h
  · exact reduce_hasNoZeros_of_mem_ofChargesExpand c F h

lemma mem_ofChargesExpand_map_reduce_iff (c : Finset ℤ) (S : TenQuanta) :
    S ∈ (ofChargesExpand c).map reduce ↔ S.toFluxesTen ∈ FluxesTen.elemsNoExotics
      ∧ S.toCharges.toFinset = c ∧ S.reduce = S := by
  constructor
  · intro h
    simp at h
    obtain ⟨F, h1, rfl⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · exact reduce_mem_elemsNoExotics_of_mem_ofChargesExpand c F h1
    · rw [mem_ofChargesExpand_iff] at h1
      rw [← h1.1, reduce_toCharges]
      exact Multiset.toFinset_dedup F.toCharges
    · rw [reduce_reduce]
  · intro h
    simp only [Multiset.mem_map]
    rw [← h.2.2]
    have h1 := h.1
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics] at h1
    refine mem_ofChargesExpand_of_noExotics_hasNoZero S c ?_ ?_ ?_
    · exact h.2.1
    · exact h1.1
    · exact h1.2

end TenQuanta

end SU5U1

end FTheory
