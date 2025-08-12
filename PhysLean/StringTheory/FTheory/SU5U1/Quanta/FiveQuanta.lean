/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.ToList
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.Lemmas
/-!

# Quanta of representations

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

-/
namespace FTheory

namespace SU5U1
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta of 5-bar representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev FiveQuanta : Type := Multiset (ℤ × ℤ × ℤ)

namespace FiveQuanta

/-- The underlying `FluxesFive` from a `FiveQuanta`. -/
def toFluxesFive (x : FiveQuanta) : FluxesFive := x.map Prod.snd

/-- The underlying Multiset charges from a `FiveQuanta`. -/
def toCharges (x : FiveQuanta) : Multiset ℤ := x.map Prod.fst

/-!

## Reduce

-/

/-- The `reduce` of `FiveQuanta` is a new `FiveQuanta` with all the fluxes
  corresponding to the same charge (i.e. represenation) added together. -/
def reduce (x : FiveQuanta) : FiveQuanta :=
  x.toCharges.dedup.map fun q5 => (q5, ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum)

lemma reduce_nodup (x : FiveQuanta) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : FiveQuanta) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

lemma reduce_toCharges (x : FiveQuanta) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

lemma reduce_eq_val (x : FiveQuanta) :
    x.reduce = (x.toCharges.toFinset.image fun q5 =>
      (q5, ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum)).val := by
  simp
  rw [← reduce]
  simp

lemma mem_reduce_iff (x : FiveQuanta) (p : ℤ × ℤ × ℤ) :
    p ∈ x.reduce ↔ p.1 ∈ x.toCharges ∧
      p.2 = ((x.filter (fun f => f.1 = p.1)).map (fun y => y.2)).sum := by
  simp [reduce]
  constructor
  · intro h
    obtain ⟨q, h1, rfl⟩ := h
    simp_all
  · simp
    intro h1 h2
    use p.1
    simp_all
    rw [← h2]

lemma reduce_filter (x : FiveQuanta) (q : ℤ) (h : q ∈ x.toCharges) :
    x.reduce.filter (fun f => f.1 = q) =
     {(q, ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum)} := by
  simp [reduce]
  rw [Multiset.filter_map]
  simp
  have hx : (Multiset.filter (fun x => x = q) x.toCharges.dedup)  = {q} := by
    refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · refine Multiset.Nodup.filter (fun x => x = q) ?_
      exact Multiset.nodup_dedup x.toCharges
    · exact Multiset.nodup_singleton q
    intro a
    simp
    intro h'
    subst h'
    exact h
  rw [hx]
  simp

@[simp]
lemma reduce_reduce (x : FiveQuanta) :
    x.reduce.reduce = x.reduce := by
  refine Multiset.Nodup.toFinset_inj ?_ ?_ ?_
  · exact reduce_nodup x.reduce
  · exact reduce_nodup x
  ext p
  simp
  rw [mem_reduce_iff, reduce_toCharges, mem_reduce_iff]
  simp
  intro hp
  have h1 (a b c : ℤ × ℤ) (h : b = c) : a = b ↔ a = c := by subst h; rfl
  apply h1
  rw [reduce_filter]
  simp
  exact hp

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : FiveQuanta) (f : ℤ → ℤ × ℤ →+ M)  :
    (x.reduce.map fun (q5, x) => f q5 x).sum = (x.map fun (q5, x) => f q5 x).sum := by
  calc _
      _ =  ∑ q5 ∈ x.toCharges.toFinset,
          f q5 ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum  := by
        congr
        funext q5
        rw [AddMonoidHom.map_multiset_sum, Multiset.map_map]
        rfl
      _ = (x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
        rw [Multiset.sum_bind]
        simp [Finset.sum]
      _ = (((x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)))).map (fun y => f y.1 y.2))).sum := by
        congr
        rw [Multiset.map_bind]
        congr
        funext q5
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
          simp
          have h_count_one : Multiset.count p.1 (Multiset.map Prod.fst x).dedup  = 1 := by
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

/-!

## Anomaly cancellation

-/

/--
  The anomaly coefficent of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficent (F : FiveQuanta) : ℤ × ℤ :=
  ((F.map fun x => x.1 * x.2.2).sum, (F.map fun x => x.1 * x.1 * x.2.2).sum)

lemma anomalyCoefficent_of_reduce (F : FiveQuanta) :
    F.reduce.anomalyCoefficent = F.anomalyCoefficent := by
  simp [anomalyCoefficent]
  constructor
  · let f : ℤ → ℤ × ℤ →+ ℤ := fun q5  => {
      toFun := fun x => q5 * x.2
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul, mul_add] }
    have h1 := reduce_sum_eq_sum_toCharges F f
    simpa [f] using h1
  · let f : ℤ → ℤ × ℤ →+ ℤ := fun q5  => {
      toFun := fun x => q5 * q5 * x.2
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul, mul_add] }
    have h1 := reduce_sum_eq_sum_toCharges F f
    simpa [f] using h1

/-!

## ofChargesExpand

-/


open SuperSymmetry.SU5.Charges
def ofChargesExpand (c : Finset ℤ) :  Multiset FiveQuanta :=
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S53 : Multiset (Multiset ℤ) := toMultisetsThree c
  /- Pairs of multisets (s1, s2) such that s1 and s2 are cardinality of `3` containing
    elements of `c` and that all elements of `c` are in `s1 + s2`. -/
  let S5p : Multiset (Multiset ℤ × Multiset ℤ) :=
    (S53.product S53).filter fun (s1, s2) => c.val ≤ s1 + s2
  let Fp : Multiset FiveQuanta :=
    S5p.map (fun y => y.1.map (fun z => (z, 1, -1)) + y.2.map (fun z => (z, 0, 1)))
  Fp

lemma toFluxesFive_of_mem_ofChargesExpand (c : Finset ℤ)
    {x : FiveQuanta} (h : x ∈ ofChargesExpand c) :
    x.toFluxesFive = {(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)} := by
  simp [ofChargesExpand] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  simp [toFluxesFive, s1_card, s2_card]
  decide

lemma toCharges_of_mem_ofChargesExpand (c : Finset ℤ)
    {x : FiveQuanta} (h : x ∈ ofChargesExpand c) :
    x.toCharges.toFinset = c := by
  simp [ofChargesExpand] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  simp [toCharges]
  trans (s1 + s2).toFinset
  · exact Eq.symm (Multiset.toFinset_add s1 s2)
  ext a
  simp
  constructor
  · intro hr
    rcases hr with hr | hr
    · apply s1_subset
      simpa using hr
    · apply s2_subset
      simpa using hr
  · intro hr
    simpa using Multiset.mem_of_le hsum hr

lemma mem_ofChargesExpand_of_toCharges_toFluxesFive (c : Finset ℤ) {x : FiveQuanta}
    (h : x.toCharges.toFinset = c) (h2 : x.toFluxesFive =
      {(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)}) :
    x ∈ ofChargesExpand c := by
  simp [ofChargesExpand]
  let s1 := (x.filter (fun y => y.2 = (1, -1))).map Prod.fst
  let s2 := (x.filter (fun y => y.2 = (0, 1))).map Prod.fst
  use s1, s2
  have hx : Multiset.filter (fun y => y.2 = (0, 1)) x
        = Multiset.filter (fun y => ¬ y.2 = (1, -1)) x := by
    refine Multiset.filter_congr ?_
    intro p hp
    have h1 : p.2 ∈ x.toFluxesFive := by simp [toFluxesFive]; use p.1
    rw [h2] at h1
    simp_all
    rcases h1 with hp | hp
    · simp [hp]
    · simp [hp]
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · simp [s1, ← h, toCharges]
  · simp [s1]
    trans (Multiset.filter (fun y => y = (1, -1)) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · simp [s2, ← h, toCharges]
  · simp [s2]
    trans (Multiset.filter (fun y => y = (0, 1)) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · rw [← h]
    simp [s1, s2, toCharges]
    rw [← Multiset.map_add]
    refine (Multiset.le_iff_subset ( Multiset.nodup_dedup (Multiset.map Prod.fst x))).mpr ?_
    simp only [Multiset.dedup_subset']
    refine Multiset.map_subset_map ?_
    rw [hx, Multiset.filter_add_not]
    exact fun ⦃a⦄ a => a
  · simp [s1, s2]
    have h1 :  Multiset.map (fun x => (x.1, 1, -1)) (Multiset.filter (fun y => y.2 = (1, -1)) x)
        = (Multiset.filter (fun y => y.2 = (1, -1)) x) := by
      trans  Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = (1, -1)) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    have h2 :  Multiset.map (fun x => (x.1, 0, 1)) (Multiset.filter (fun y => y.2 = (0, 1)) x)
        = (Multiset.filter (fun y => y.2 = (0, 1)) x) := by
      trans Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = (0, 1)) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    rw [h1, h2, hx]
    exact Multiset.filter_add_not (fun y => y.2 = (1, -1)) x

lemma mem_ofChargesExpand_iff(c : Finset ℤ) {x : FiveQuanta} :
    x ∈ ofChargesExpand c ↔
    x.toCharges.toFinset = c ∧ x.toFluxesFive =
      {(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)} := by
  constructor
  · intro h
    constructor
    exact toCharges_of_mem_ofChargesExpand c h
    exact toFluxesFive_of_mem_ofChargesExpand c h
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact mem_ofChargesExpand_of_toCharges_toFluxesFive c h1 h2

lemma eq_sum_filter_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    F = (F.filter fun x => x.2 = (1, -1)) + (F.filter fun x => x.2 = (0, 1)) := by
  rw [mem_ofChargesExpand_iff] at h
  obtain ⟨hc, h⟩ := h
  have h1 : Multiset.filter (fun x => x.2 = (0, 1)) F
      = Multiset.filter (fun x => ¬ x.2 = (1, -1)) F := by
    apply Multiset.filter_congr
    intro x f
    have h2 : x.2 ∈ F.toFluxesFive := by
      simp [toFluxesFive]
      use x.1
    rw [h] at h2
    simp at h2
    rcases h2 with h | h
    · simp [h]
    · simp [h]
  rw [h1]
  exact Eq.symm (Multiset.filter_add_not (fun x => x.2 = (1, -1)) F)

lemma mem_ofChargesExpand_of_noExotics_hasNoZero (F : FiveQuanta) (c : Finset ℤ)
    (hc : F.toCharges.toFinset = c)
    (h1 : F.toFluxesFive.NoExotics) (h2 : F.toFluxesFive.HasNoZero) :
    ∃ y ∈ ofChargesExpand c, y.reduce = F.reduce := by
  have hf : F.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
    simp_all
    exact h2
  let Ex : FiveQuanta := F.bind fun (q5, M, N) => Multiset.replicate M.natAbs (q5, 1, -1)
      + Multiset.replicate (M + N).natAbs (q5, 0, 1)
  have ex_filter (q5 : ℤ) : (Ex.filter fun x => x.1 = q5) =
      (F.filter fun x => x.1 = q5).bind fun (q5, M, N) =>
      Multiset.replicate M.natAbs (q5, (1 : ℤ), -1)
      + Multiset.replicate (M + N).natAbs (q5, 0, 1):= by
    dsimp [Ex]
    simp
    congr
    · ext p
      by_cases hp : p ∉ (Multiset.filter (fun x => x.1 = q5) (Multiset.bind F fun a => Multiset.replicate a.2.1.natAbs (a.1, 1, -1)))
      · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
        · simp
          simp at hp
          intro q M N h1 hq
          subst hq
          have hp' := hp q M N h1
          by_contra hn
          have hl := hp' hn
          rw [Multiset.mem_replicate] at hn
          obtain ⟨h, rfl⟩ := hn
          simp at hl
        · exact hp
      · simp at hp
        obtain ⟨q, M, ⟨N, is_mem⟩, h2, rfl⟩ := hp
        rw [Multiset.count_filter]
        simp
        rw [Multiset.count_bind, Multiset.count_bind]
        have hf : F = (Multiset.filter (fun x => x.1 = p.1) F) +
          (Multiset.filter (fun x => ¬ x.1 = p.1) F) :=
            Eq.symm (Multiset.filter_add_not (fun x => x.1 = p.1) F)
        conv_lhs => rw [hf]
        simp
        apply Multiset.sum_eq_zero
        intro x hx
        simp at hx
        obtain ⟨q', M', ⟨⟨N', is_mem⟩, h2⟩, h⟩ := hx
        rw [Multiset.count_eq_zero_of_notMem] at h
        exact h.symm
        rw [Multiset.mem_replicate]
        simp
        intro hM'
        by_contra hn
        subst hn
        simp at h2
    · ext p
      by_cases hp : p ∉ Multiset.filter (fun x => x.1 = q5) (Multiset.bind F fun a => Multiset.replicate (a.2.1 + a.2.2).natAbs (a.1, 0, 1))
      · rw [Multiset.count_eq_zero_of_notMem, Multiset.count_eq_zero_of_notMem]
        · simp
          simp at hp
          intro q M N h1 hq
          subst hq
          have hp' := hp q M N h1
          by_contra hn
          have hl := hp' hn
          rw [Multiset.mem_replicate] at hn
          obtain ⟨h, rfl⟩ := hn
          simp at hl
        · exact hp
      · simp at hp
        obtain ⟨q, M, N, os_mem, h1, rfl⟩ := hp
        rw [Multiset.count_filter]
        simp
        rw [Multiset.count_bind, Multiset.count_bind]
        have hf : F = (Multiset.filter (fun x => x.1 = p.1) F) +
          (Multiset.filter (fun x => ¬ x.1 = p.1) F) :=
            Eq.symm (Multiset.filter_add_not (fun x => x.1 = p.1) F)
        conv_lhs => rw [hf]
        simp
        apply Multiset.sum_eq_zero
        intro x hx
        simp at hx
        obtain ⟨q', M', N', h2, h⟩ := hx
        rw [Multiset.count_eq_zero_of_notMem] at h
        exact h.symm
        rw [Multiset.mem_replicate]
        simp
        intro hM'
        by_contra hn
        subst hn
        simp at h2
  have ex_charges : Ex.toCharges.toFinset = c := by
    ext p
    constructor
    · intro h
      simp [Ex, toCharges] at h
      rcases h with h | h
      · obtain ⟨M', N', p', M, ⟨N, h⟩, h2⟩ := h
        rw [Multiset.mem_replicate] at h2
        simp at h2
        obtain ⟨h2, rfl, rfl, rfl⟩ := h2
        rw [← hc]
        simp [toCharges]
        use M, N
      · obtain ⟨M', N', p', M, N, h1, h2⟩ := h
        simp [Multiset.mem_replicate] at h2
        obtain ⟨h2, rfl, rfl, rfl⟩ := h2
        rw [← hc]
        simp [toCharges]
        use M, N
    · intro h
      simp [Ex, toCharges]
      rw [← hc] at h
      simp [toCharges] at h
      obtain ⟨M, N, h⟩ := h
      have h1 : (M, N) ∈ F.toFluxesFive := by
        simp [toFluxesFive]
        use p
      by_cases h : M.natAbs ≠ 0
      · left
        use 1, -1, p, M
        constructor
        · use N
        · refine Multiset.mem_replicate.mpr ?_
          simp_all
      · right
        use 0, 1, p, M, N
        simp_all
        refine Multiset.mem_replicate.mpr ?_
        simp
        revert h1
        revert hf
        generalize F.toFluxesFive = FF
        intro hFF
        fin_cases hFF
        all_goals simp
        all_goals aesop
  use Ex
  constructor
  /- Ex ∈ ofChargesExpand c -/
  · rw [mem_ofChargesExpand_iff]
    constructor
    /- Ex.toCharges.toFinset = c -/
    · exact ex_charges
    /- Ex.toFluxesFive = {(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)} -/
    · simp [Ex, toFluxesFive]
      rw [Multiset.map_bind, Multiset.map_bind]
      simp
      trans ((Multiset.bind F.toFluxesFive fun a => Multiset.replicate a.1.natAbs (1, -1)) +
         Multiset.bind F.toFluxesFive fun a => Multiset.replicate (a.1 + a.2).natAbs (0, 1))
      · congr 1
        · rw [toFluxesFive, Multiset.bind_map]
        · rw [toFluxesFive, Multiset.bind_map]
      · generalize F.toFluxesFive = FF at *
        fin_cases hf
        any_goals decide
  /- Ex.reduce = F.reduce -/
  · refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · exact reduce_nodup Ex
    · exact reduce_nodup F
    intro a
    rw [mem_reduce_iff, mem_reduce_iff]
    conv_rhs => rw [← Multiset.mem_toFinset, hc]
    rw [← Multiset.mem_toFinset, ex_charges]
    rw [and_congr_right_iff]
    intro h1
    have hab (a b c : ℤ × ℤ) (hcb : c = b) : (a = c ↔ a = b) := by
      subst hcb
      rfl
    rw [hab]
    rw [ex_filter]
    dsimp
    rw [Multiset.map_bind]
    simp only [Int.reduceNeg, Multiset.map_add, Multiset.map_replicate, Multiset.bind_add,
      Multiset.sum_add, Multiset.sum_bind, Multiset.sum_replicate, Prod.smul_mk, nsmul_eq_mul,
      Int.natCast_natAbs, mul_one, smul_neg, smul_zero, Ex]
    have h1 : (Multiset.map (fun x => (|x.2.1|, -|x.2.1|))
        (Multiset.filter (fun x => x.1 = a.1) F)).sum
       =  (Multiset.map (fun x => (|x.1|, -|x.1|))
        (Multiset.map (fun y => y.2) (Multiset.filter (fun x => x.1 = a.1) F))).sum := by
      rw [Multiset.map_map]
      congr
    have h2 : (Multiset.map (fun x => ((0 : ℤ), |x.2.1 + x.2.2|)) (Multiset.filter (fun x => x.1 = a.1) F)).sum
      = (Multiset.map (fun x => (0, |x.1 + x.2|))
        (Multiset.map (fun y => y.2) (Multiset.filter (fun x => x.1 = a.1) F))).sum := by
      rw [Multiset.map_map]
      congr
    rw [h1, h2]
    generalize hS : Multiset.map (fun y => y.2) (Multiset.filter (fun x => x.1 = a.1) F) = S
    have hS' : S ≤ F.toFluxesFive := by
      rw [← hS]
      simp [toFluxesFive]
    have hS'' : S ∈ F.toFluxesFive.powerset := by
      exact Multiset.mem_powerset.mpr hS'
    clear hS hS'
    generalize F.toFluxesFive = FF at hf hS''
    fin_cases hf
    all_goals
    · fin_cases hS''
      all_goals decide

lemma exists_charges_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    ∃ q1 q2 q3 q4 q5 q6 : ℤ,
      F = {(q1, 1, -1), (q2, 1, -1), (q3, 1, -1), (q4, 0, 1), (q5, 0, 1), (q6, 0, 1)} := by
  let F₁ := F.filter (fun x => x.snd = (1, -1))
  let F₂ := F.filter (fun x => x.snd = (0, 1))
  have h_F_split : F = F₁ + F₂ := by
    dsimp [F₁, F₂]
    rw [← eq_sum_filter_of_mem_ofChargesExpand c F h]
  have h_card_F₁ : F₁.card = 3 := by
    trans (F.toFluxesFive.filter (fun x => x = (1, -1))).card
    · simp [toFluxesFive, F₁]
      rw [Multiset.filter_map]
      simp
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  have h_card_F₂ : F₂.card = 3 := by
    trans (F.toFluxesFive.filter (fun x => x = (0, 1))).card
    · simp [toFluxesFive, F₂]
      rw [Multiset.filter_map]
      simp
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  have F₁_map_prod_snd : F₁.map Prod.snd = Multiset.replicate 3 (1, -1) := by
    dsimp [F₁]
    trans  (Multiset.filter (fun x => x = (1, -1)) F.toFluxesFive)
    · simp [toFluxesFive, F₁]
      rw [Multiset.filter_map]
      simp
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  have F₂_map_prod_snd : F₂.map Prod.snd = Multiset.replicate 3 (0, 1) := by
    dsimp [F₂]
    trans (Multiset.filter (fun x => x = (0, 1)) F.toFluxesFive)
    · simp [toFluxesFive, F₂]
      rw [Multiset.filter_map]
      simp
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  obtain ⟨q1, q2, q3, hF₁⟩ : ∃ q1 q2 q3, F₁ = {(q1, 1, -1), (q2, 1, -1), (q3, 1, -1)} := by
    rw [Multiset.card_eq_three] at h_card_F₁
    obtain ⟨a1, a2, a3, h⟩ := h_card_F₁
    rw [h]
    rw [h] at F₁_map_prod_snd
    use a1.1, a2.1, a3.1
    congr
    · have h1 : a1.2 ∈ Multiset.map Prod.snd {a1, a2, a3}  := by
        simp
      rw [F₁_map_prod_snd] at h1
      simp at h1
      rw [← h1]
    · have h1 : a2.2 ∈ Multiset.map Prod.snd {a1, a2, a3} := by
        simp
      rw [F₁_map_prod_snd] at h1
      simp at h1
      rw [← h1]
    · have h1 : a3.2 ∈ Multiset.map Prod.snd {a1, a2, a3} := by
        simp
      rw [F₁_map_prod_snd] at h1
      simp at h1
      rw [← h1]
  obtain ⟨q4, q5, q6, hF₂⟩ : ∃ q4 q5 q6, F₂ = {(q4, 0, 1), (q5, 0, 1), (q6, 0, 1)} := by
    rw [Multiset.card_eq_three] at h_card_F₂
    obtain ⟨a1, a2, a3, h⟩ := h_card_F₂
    rw [h]
    rw [h] at F₂_map_prod_snd
    use a1.1, a2.1, a3.1
    congr
    · have h1 : a1.2 ∈ Multiset.map Prod.snd {a1, a2, a3}  := by
        simp
      rw [F₂_map_prod_snd] at h1
      simp at h1
      rw [← h1]
    · have h1 : a2.2 ∈ Multiset.map Prod.snd {a1, a2, a3} := by
        simp
      rw [F₂_map_prod_snd] at h1
      simp at h1
      rw [← h1]
    · have h1 : a3.2 ∈ Multiset.map Prod.snd {a1, a2, a3} := by
        simp
      rw [F₂_map_prod_snd] at h1
      simp at h1
      rw [← h1]
  use q1, q2, q3, q4, q5, q6
  rw [h_F_split, hF₁, hF₂]
  rfl
lemma exists_charges_le_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    ∃ q1 q2 q3 q4 q5 q6 : ℤ,
      F = {(q1, 1, -1), (q2, 1, -1), (q3, 1, -1), (q4, 0, 1), (q5, 0, 1), (q6, 0, 1)} ∧
      q1 ≤ q2 ∧ q2 ≤ q3 ∧ q4 ≤ q5 ∧ q5 ≤ q6 := by
  obtain ⟨q1, q2, q3, q4, q5, q6, hF⟩ := exists_charges_of_mem_ofChargesExpand c F h
  let F₁ := F.filter (fun x => x.snd = (1, -1))
  let F₂ := F.filter (fun x => x.snd = (0, 1))
  have F₁_eq : F₁ = {(q1, 1, -1), (q2, 1, -1), (q3, 1, -1)} := by
    dsimp [F₁]
    subst hF
    simp [@Multiset.filter_singleton]
  have F₂_eq : F₂ = {(q4, 0, 1), (q5, 0, 1), (q6, 0, 1)} := by
    dsimp [F₂]
    subst hF
    simp [@Multiset.filter_singleton]
  have F_eq : F = F₁ + F₂ := by
    dsimp [F₁, F₂]
    rw [← eq_sum_filter_of_mem_ofChargesExpand c F h]
  suffices h : (∃ q1 q2 q3 : ℤ,  F₁ = {(q1, 1, -1), (q2, 1, -1), (q3, 1, -1)} ∧
        q1 ≤ q2 ∧ q2 ≤ q3) ∧
        (∃ q4 q5 q6 : ℤ, F₂ = {(q4, 0, 1), (q5, 0, 1), (q6, 0, 1)} ∧
        q4 ≤ q5 ∧ q5 ≤ q6) by
      obtain ⟨⟨q1', q2', q3', hF₁, h12⟩, ⟨q4', q5', q6', hF₂, h23⟩⟩ := h
      use q1', q2', q3', q4', q5', q6'
      rw [F_eq, hF₁, hF₂]
      constructor
      · rfl
      simp_all
  have h1 : (q1 ≤ q2 ∧ q2 ≤ q3) ∨ (q2 ≤ q3 ∧ q3 ≤ q1) ∨ (q3 ≤ q1 ∧ q1 ≤ q2)
      ∨ (q1 ≤ q3 ∧ q3 ≤ q2) ∨ (q3 ≤ q2 ∧ q2 ≤ q1) ∨ (q2 ≤ q1 ∧ q1 ≤ q3)  := by
    omega
  have h2 : (q4 ≤ q5 ∧ q5 ≤ q6) ∨ (q5 ≤ q6 ∧ q6 ≤ q4) ∨ (q6 ≤ q4 ∧ q4 ≤ q5)
      ∨ (q4 ≤ q6 ∧ q6 ≤ q5) ∨ (q6 ≤ q5 ∧ q5 ≤ q4) ∨ (q5 ≤ q4 ∧ q4 ≤ q6) := by omega
  constructor
  · rw [F₁_eq]
    rcases h1 with h1 | h1 | h1 | h1 | h1 | h1
    · use q1, q2, q3
    · use q2, q3, q1
      simp_all
      rw [Multiset.cons_swap, Multiset.cons_inj_right,
        ← Multiset.cons_zero, Multiset.cons_swap]
      rfl
    · use q3, q1, q2
      simp_all
      rw [← Multiset.cons_zero]
      conv_lhs =>
        enter [2]
        rw [Multiset.cons_swap]
      rw [Multiset.cons_swap, Multiset.cons_inj_right]
      rfl
    · use q1, q3, q2
      simp_all
      rw [← Multiset.cons_zero, Multiset.cons_swap]
      rfl
    · use q3, q2, q1
      simp_all
      rw [← Multiset.cons_zero]
      conv_lhs =>
        enter [2]
        rw [Multiset.cons_swap]
      rw [Multiset.cons_swap, Multiset.cons_inj_right, Multiset.cons_swap]
      rfl
    · use q2, q1, q3
      simp_all
      rw [Multiset.cons_swap]
  · rw [F₂_eq]
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2
    · use q4, q5, q6
    · use q5, q6, q4
      simp_all
      rw [Multiset.cons_swap, Multiset.cons_inj_right,
        ← Multiset.cons_zero, Multiset.cons_swap]
      rfl
    · use q6, q4, q5
      simp_all
      rw [← Multiset.cons_zero]
      conv_lhs =>
        enter [2]
        rw [Multiset.cons_swap]
      rw [Multiset.cons_swap, Multiset.cons_inj_right]
      rfl
    · use q4, q6, q5
      simp_all
      rw [← Multiset.cons_zero, Multiset.cons_swap]
      rfl
    · use q6, q5, q4
      simp_all
      rw [← Multiset.cons_zero]
      conv_lhs =>
        enter [2]
        rw [Multiset.cons_swap]
      rw [Multiset.cons_swap, Multiset.cons_inj_right, Multiset.cons_swap]
      rfl
    · use q5, q4, q6
      simp_all
      rw [Multiset.cons_swap]

lemma reduce_hasNoZeros_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive.HasNoZero := by
  simp [reduce, toFluxesFive, FluxesFive.HasNoZero]
  intro x hx
  have hs : (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F))
      ∈ F.toFluxesFive.powerset := by
    simp [toFluxesFive]
  have h1 : Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F) ≠ 0 := by
    simp
    rw [@Multiset.filter_eq_nil]
    simp
    simp [toCharges] at hx
    obtain ⟨a, b, h⟩ := hx
    use a, b
  generalize (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F))  = s at *
  rw [mem_ofChargesExpand_iff] at h
  rw [h.2] at hs
  fin_cases hs
  · simp at h1
  all_goals
  · decide

lemma reduce_noExotics_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive.NoExotics := by
  simp [FluxesFive.NoExotics]
  have h1 :  (Multiset.filter (fun x => x < 0)
      (Multiset.map (fun f => f.1 + f.2) F.reduce.toFluxesFive)) = ∅ := by
    simp
    rw [@Multiset.filter_eq_nil]
    intro a ha
    simp at ha
    obtain ⟨c, b, h1, h2⟩ := ha
    obtain ⟨s, h'⟩ : ∃ s ∈ F.toFluxesFive.powerset, (c, b) = s.sum := by
      simp [reduce, toFluxesFive] at h1
      obtain ⟨q, q_mem, h1⟩ := h1
      use (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = q) F))
      simp_all [toFluxesFive]
    have ha : a = s.sum.1 + s.sum.2 := by
      rw [← h2, ← h'.2]
    rw [ha]
    have h2 := h'.1
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2] at h2
    fin_cases h2
    all_goals
    · decide
  have h2 : (Multiset.filter (fun x => x < 0) (Multiset.map (fun f => f.1) F.reduce.toFluxesFive))
      = ∅ := by
    simp
    rw [@Multiset.filter_eq_nil]
    intro a ha
    simp at ha
    obtain ⟨c, h1⟩ := ha
    obtain ⟨s, h'⟩ : ∃ s ∈ F.toFluxesFive.powerset, (a, c) = s.sum := by
      simp [reduce, toFluxesFive] at h1
      obtain ⟨q, q_mem, h1⟩ := h1
      use (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = q) F))
      simp_all [toFluxesFive]
    have ha : a = s.sum.1 := by
      rw [ ← h'.2]
    rw [ha]
    have h2 := h'.1
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2] at h2
    fin_cases h2
    all_goals
    · decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FluxesFive.numChiralL_eq_sum_sub_numAntiChiralL]
    simp [FluxesFive.numAntiChiralL, FluxesFive.chiralIndicesOfL]
    rw [h1]
    have sum_1 : (Multiset.map Prod.fst F.reduce.toFluxesFive).sum
      = (Multiset.map Prod.fst F.toFluxesFive).sum := by
      rw [toFluxesFive, Multiset.map_map]
      let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
        toFun := fun x => x.1
        map_add' := by simp
        map_zero' := by simp
      }
      change (Multiset.map (fun (q5, x) => f q5 x) F.reduce).sum = _
      rw [reduce_sum_eq_sum_toCharges F]
      simp [f, toFluxesFive]
    have sum_2 :  (Multiset.map Prod.snd F.reduce.toFluxesFive).sum
      = (Multiset.map Prod.snd F.toFluxesFive).sum := by
      rw [toFluxesFive, Multiset.map_map]
      let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
        toFun := fun x => x.2
        map_add' := by simp
        map_zero' := by simp
      }
      change (Multiset.map (fun (q5, x) => f q5 x) F.reduce).sum = _
      rw [reduce_sum_eq_sum_toCharges F]
      simp [f, toFluxesFive]
    rw [sum_1, sum_2]
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  · simp [FluxesFive.numAntiChiralL, FluxesFive.chiralIndicesOfL]
    rw [h1]
    simp
  · rw [FluxesFive.numChiralD_eq_sum_sub_numAntiChiralD]
    simp [FluxesFive.numAntiChiralD, FluxesFive.chiralIndicesOfD]
    rw [h2]
    simp
    let f : ℤ → ℤ × ℤ →+ ℤ := fun q5 => {
      toFun := fun x => x.1
      map_add' := by simp
      map_zero' := by simp
    }
    simp [toFluxesFive]
    change (Multiset.map (fun (q5, x) => f q5 x) F.reduce).sum = _
    rw [reduce_sum_eq_sum_toCharges F]
    trans (Multiset.map (fun x => x.1) F.toFluxesFive).sum
    · simp [toFluxesFive]
      rfl
    rw [mem_ofChargesExpand_iff] at h
    rw [h.2]
    decide
  · simp [FluxesFive.numAntiChiralD, FluxesFive.chiralIndicesOfD]
    rw [h2]
    simp

lemma reduce_mem_elemsNoExotics_of_mem_ofChargesExpand (c : Finset ℤ) (F : FiveQuanta)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
  rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
  constructor
  · exact reduce_noExotics_of_mem_ofChargesExpand c F h
  · exact reduce_hasNoZeros_of_mem_ofChargesExpand c F h

lemma mem_ofChargesExpand_map_reduce_iff (c : Finset ℤ) (S : FiveQuanta) :
    S ∈ (ofChargesExpand c).map reduce ↔ S.toFluxesFive ∈ FluxesFive.elemsNoExotics
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
    simp
    rw [← h.2.2]
    have h1 := h.1
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at h1
    refine mem_ofChargesExpand_of_noExotics_hasNoZero S c ?_ ?_ ?_
    · exact h.2.1
    · exact h1.1
    · exact h1.2

end FiveQuanta

end SU5U1

end FTheory
