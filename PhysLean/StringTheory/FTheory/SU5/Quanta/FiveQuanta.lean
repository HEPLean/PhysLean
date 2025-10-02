/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness
/-!

# Quanta of 5-d representations

The 5-bar representations of the `SU(5)×U(1)` carry
the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## Key definitions

- `FiveQuanta` is the type of quanta of 5-bar representations.
- `FiveQuanta.toFluxesFive` is the underlying `FluxesFive` of a `FiveQuanta`.
- `FiveQuanta.toCharges` is the underlying Multiset charges of a `FiveQuanta`.
- `FiveQuanta.reduce` is the reduction of a `FiveQuanta` which adds together
  all the fluxes corresponding to the same charge (i.e. representation).
- `FiveQuanta.anomalyCoefficent` is the anomaly coefficent associated with a `FiveQuanta`.
- `FiveQuanta.ofChargesExpand` is the `FiveQuanta` with fluxes
  `{(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)}` and finite set of charges equal to a given
  `c`.

## Key theorems

- `mem_ofChargesExpand_map_reduce_iff` states that a `FiveQuanta` is in the
  image of `ofChargesExpand c` under `reduce` if and only if it is a `FiveQuanta` with
  charges equal to `c` and fluxes which have no exotics or zero.
-/
namespace FTheory

namespace SU5
open SU5
variable {I : CodimensionOneConfig}

/-!

## A. The definition of `FiveQuanta`

-/
/-- The quanta of 5-bar representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev FiveQuanta (𝓩 : Type := ℤ) : Type := Multiset (𝓩 × Fluxes)

namespace FiveQuanta

variable {𝓩 : Type}

/-!

## A.1. The map to underlying fluxes

-/

/-- The underlying `FluxesFive` from a `FiveQuanta`. -/
def toFluxesFive (x : FiveQuanta 𝓩) : FluxesFive := x.map Prod.snd

/-!

## A.2. The map to underlying charges

-/

/-- The underlying Multiset charges from a `FiveQuanta`. -/
def toCharges (x : FiveQuanta 𝓩) : Multiset 𝓩 := x.map Prod.fst

/-!

## A.3. The map from charges to fluxes

-/

/-- The map which takes a charge to the overall flux it
  corresponds to in a `FiveQuanta`. -/
def toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩) : 𝓩 → Fluxes :=
  fun z => ((x.filter fun p => p.1 = z).map Prod.snd).sum

lemma toChargeMap_of_not_mem [DecidableEq 𝓩] (x : FiveQuanta 𝓩) {z : 𝓩} (h : z ∉ x.toCharges) :
    x.toChargeMap z = 0 := by
  simp [toChargeMap]
  have hl : (Multiset.filter (fun p => p.1 = z) x) = 0 := by
    simp
    intro a b f
    by_contra hn
    subst hn
    simp [toCharges] at h
    exact h b f
  rw [hl]
  simp

/-!

## B. The reducition of a `FiveQuanta`

-/

section reduce

variable [DecidableEq 𝓩]

/-- The `reduce` of `FiveQuanta` is a new `FiveQuanta` with all the fluxes
  corresponding to the same charge (i.e. represenation) added together. -/
def reduce (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.toCharges.dedup.map fun q5 => (q5, ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum)

/-!

### B.1. The reduced `FiveQuanta` has no duplicate elements

-/

lemma reduce_nodup (x : FiveQuanta 𝓩) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : FiveQuanta 𝓩) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

/-!

### B.2. The underlying charges of the reduced `FiveQuanta` are the deduped charges
-/
lemma reduce_toCharges (x : FiveQuanta 𝓩) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

/-!

### B.3. Membership condition on the reduced `FiveQuanta`

-/

lemma mem_reduce_iff (x : FiveQuanta 𝓩) (p : 𝓩 × Fluxes) :
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

/-!

### B.4. Filter of the reduced `FiveQuanta` by a charge

-/

lemma reduce_filter (x : FiveQuanta 𝓩) (q : 𝓩) (h : q ∈ x.toCharges) :
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

/-!

### B.5. The reduction is idempotent

-/

@[simp]
lemma reduce_reduce (x : FiveQuanta 𝓩) :
    x.reduce.reduce = x.reduce := by
  refine Multiset.Nodup.toFinset_inj ?_ ?_ ?_
  · exact reduce_nodup x.reduce
  · exact reduce_nodup x
  ext p
  simp only [Multiset.mem_toFinset]
  rw [mem_reduce_iff, reduce_toCharges, mem_reduce_iff]
  simp only [Multiset.mem_dedup, and_congr_right_iff]
  intro hp
  have h1 (a b c : Fluxes) (h : b = c) : a = b ↔ a = c := by subst h; rfl
  apply h1
  rw [reduce_filter]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  exact hp

/-!

### B.6. Preservation of certain sums under reduction

-/

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : FiveQuanta 𝓩) (f : 𝓩 → Fluxes →+ M) :
    (x.reduce.map fun (q5, x) => f q5 x).sum = (x.map fun (q5, x) => f q5 x).sum := by
  calc _
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          f q5 ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
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
          simp only [↓reduceIte, smul_eq_mul]
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
            simp_all
          (expose_names; exact h_mem_1 h_mem)
          intro p' hp
          simp at hp
          obtain ⟨q5', ⟨f1, hf⟩, hp'⟩ := hp
          by_cases h_eq : p.1 = q5'
          · simp_all
          · simp_all

/-!

### B.7. Reduction does nothing if no duplicate charges

-/

lemma reduce_eq_self_of_ofCharges_nodup (x : FiveQuanta 𝓩) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce, Multiset.Nodup.dedup h]
  simp [toCharges]
  conv_rhs => rw [← Multiset.map_id x]
  apply Multiset.map_congr rfl
  intro p hp
  simp only [id_eq]
  have x_noDup : x.Nodup := Multiset.Nodup.of_map Prod.fst h
  suffices (Multiset.filter (fun f => f.1 = p.1) x) = {p} by simp [this]
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Multiset.Nodup.filter (fun f => f.1 = p.1) x_noDup
  · exact Multiset.nodup_singleton p
  intro p'
  simp only [Multiset.mem_filter, Multiset.mem_singleton]
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

### B.8 The charge map is preserved by reduction

-/

lemma reduce_toChargeMap_eq (x : FiveQuanta 𝓩) :
    x.reduce.toChargeMap = x.toChargeMap := by
  funext q
  by_cases h : q ∈ x.toCharges
  · rw [toChargeMap, reduce_filter]
    · simp
      rfl
    · exact h
  · rw [toChargeMap_of_not_mem, toChargeMap_of_not_mem]
    · exact h
    · rw [reduce_toCharges]
      simp only [Multiset.mem_dedup]
      exact h

/-!

### B.9. A fluxes in the reduced `FiveQuanta` is a sum of fluxes in the original `FiveQuanta`

-/

lemma mem_powerset_sum_of_mem_reduce_toFluxesFive {F : FiveQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesFive) :
    f ∈ (Multiset.powerset F.toFluxesFive).map fun s => s.sum := by
  rw [toFluxesFive, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map, Multiset.mem_powerset]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [toFluxesFive]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F

/-!

### B.10. No exotics condition on the reduced `FiveQuanta`

-/

/-!

#### B.10.1. Number of chiral `L`

-/

lemma reduce_numChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralL = 3 := by
  have hE : F.toFluxesFive.NoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]  at hx
    exact hx.1
  rw [← hE.1, FluxesFive.numChiralL, FluxesFive.numChiralL, FluxesFive.chiralIndicesOfL]
  trans (F.reduce.toFluxesFive.map (fun f => f.M + f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M + x.N, by simp⟩,
      fun x y => by simp [add_add_add_comm]⟩
    rw [toFluxesFive, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesFive.chiralIndicesOfL, toFluxesFive, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesFive.map (fun f => f.M + f.N) := by
      simp [toFluxesFive, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesFive = G at *
    revert G
    decide

/-!

#### B.10.2. Number of anti-chiral `L`

-/

lemma reduce_numAntiChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralL = 0 := by
  rw [FluxesFive.numAntiChiralL, FluxesFive.chiralIndicesOfL]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesFive.map (fun f => f.M + f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.3. Number of chiral `D`

-/

lemma reduce_numChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralD = 3 := by
  have hE : F.toFluxesFive.NoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]  at hx
    exact hx.1
  rw [← hE.2.2.1, FluxesFive.numChiralD, FluxesFive.numChiralD, FluxesFive.chiralIndicesOfD]
  trans (F.reduce.toFluxesFive.map (fun f => f.M)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M, by simp⟩,
      fun x y => by simp⟩
    rw [toFluxesFive, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesFive.chiralIndicesOfD, toFluxesFive, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesFive.map (fun f => f.M) := by
      simp [toFluxesFive, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesFive = G at *
    revert G
    decide

/-!

#### B.10.4. Number of anti-chiral `D`

-/

lemma reduce_numAntiChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralD = 0 := by
  rw [FluxesFive.numAntiChiralD, FluxesFive.chiralIndicesOfD]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesFive.map (fun f => f.M)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

/-!

#### B.10.5. The `NoExotics` condition on the reduced `FiveQuanta`

-/
lemma reduce_noExotics_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.NoExotics := by
  rw [FluxesFive.NoExotics]
  rw [reduce_numChiralL_of_mem_elemsNoExotics hx, reduce_numAntiChiralL_of_mem_elemsNoExotics hx,
    reduce_numChiralD_of_mem_elemsNoExotics hx, reduce_numAntiChiralD_of_mem_elemsNoExotics hx]
  simp

end reduce



/-!

## C. Decomposition of a `FiveQuanta` into basic fluxes

-/

/-!

### C.1. Decomposition of fluxes

-/

def decomposeFluxes (f : Fluxes) : Multiset Fluxes :=
  Multiset.replicate (Int.natAbs f.M) ⟨1, -1⟩  +
  Multiset.replicate (Int.natAbs (f.M + f.N)) ⟨0, 1⟩

lemma decomposeFluxes_sum_of_noExotics (f : Fluxes) (hf : ∃ F ∈ FluxesFive.elemsNoExotics, f ∈ F) :
    (decomposeFluxes f).sum = f := by
  obtain ⟨F, hF, hfF⟩ := hf
  revert f
  revert F
  decide

/-!

### C.2. Decomposition of a `FiveQuanta` (with no exotics)

-/

def decompose (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.bind fun p => (decomposeFluxes p.2).map fun f => (p.1, f)

/-!

#### C.2.1. Decomposition distributes over addition

-/

lemma decompose_add (x y : FiveQuanta 𝓩) :
    (x + y).decompose = x.decompose + y.decompose := by
  simp [decompose]

/-!

#### C.2.2. Decomposition computes with filtering charges

-/

lemma decompose_filter_charge [DecidableEq 𝓩] (x : FiveQuanta 𝓩) (q : 𝓩) :
    (x.decompose).filter (fun p => p.1 = q) =
    decompose (x.filter (fun p => p.1 = q)):= by
  rw [decompose]
  revert x
  apply Multiset.induction
  · simp [decompose]
  · intro a x ih
    simp
    rw [Multiset.filter_cons, decompose_add, ih]
    congr
    match a with
    | (q', f) =>
    simp [decomposeFluxes]
    by_cases h : q' = q
    · subst h
      simp [decompose, decomposeFluxes]
      congr
      all_goals
      · refine Multiset.filter_eq_self.mpr ?_
        intro a ha
        simp [Multiset.mem_replicate] at ha
        rw [ha.2]
    · simp [h, decompose]
      apply And.intro
      all_goals
      · intro a b h
        simp [Multiset.mem_replicate] at h
        simp_all

/-!

#### C.2.3. Decomposition preserves the charge map

-/

lemma decompose_toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toChargeMap = x.toChargeMap := by
  ext q
  rw [toChargeMap, decompose_filter_charge]
  simp [decompose]
  rw [Multiset.map_bind]
  simp
  rw [toChargeMap]
  congr 1
  apply Multiset.map_congr
  · rfl
  intro a ha
  apply decomposeFluxes_sum_of_noExotics
  use x.toFluxesFive
  simp_all  [toFluxesFive]
  use a.1
  exact ha.1

/-!

#### C.2.4. Decomposition preserves the charges

-/

lemma decompose_toCharges_dedup [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
   (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics):
    x.decompose.toCharges.dedup = x.toCharges.dedup := by
  refine Multiset.dedup_ext.mpr ?_
  intro q
  simp [decompose, toCharges]
  constructor
  · rintro ⟨a, b, c, h1, h2, rfl⟩
    exact ⟨c, h1⟩
  · rintro ⟨c, h1⟩
    have hn : (decomposeFluxes c) ≠ 0 := by
      have c_mem_f : c ∈ x.toFluxesFive := by
        simp [toFluxesFive]
        use q
      generalize x.toFluxesFive = F at *
      clear h1
      revert c
      revert F
      decide
    apply Multiset.exists_mem_of_ne_zero at hn
    obtain ⟨c', h⟩ := hn
    use c', q, c

/-!

#### C.2.5. Decomposition preserves the reduction

-/

lemma decompose_reduce (x : FiveQuanta 𝓩) [DecidableEq 𝓩]
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.reduce = x.reduce := by
  rw [reduce, reduce]
  apply Multiset.map_congr
  · rw [decompose_toCharges_dedup x hx]
  · intro q hx'
    simp
    change x.decompose.toChargeMap q = x.toChargeMap q
    rw [decompose_toChargeMap x hx]

/-!

#### C.2.6. Fluxes of the decomposition of a `FiveQuanta`

-/

lemma decompose_toFluxesFive (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toFluxesFive = {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩}  := by
  rw [toFluxesFive, decompose]
  rw [Multiset.map_bind]
  simp
  trans (Multiset.bind x.toFluxesFive fun a => decomposeFluxes a)
  · rw [toFluxesFive, Multiset.bind_map]
  · generalize x.toFluxesFive = F at *
    revert F
    decide

/-!

## D. Lifiting charges to `FiveQuanta`

-/

section ofChargesExpand

open SuperSymmetry.SU5.ChargeSpectrum

variable [DecidableEq 𝓩]

/-!

### D.1.

-/

/-- Given a finite set of charges `c` the `FiveQuanta`
  with fluxes `{(1, -1), (1, -1), (1, -1), (0, 1), (0, 1), (0, 1)}`
  and finite set of charges equal to `c`. -/
def ofChargesExpand (c : Finset 𝓩) : Multiset (FiveQuanta 𝓩) :=
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S53 : Multiset (Multiset 𝓩) := toMultisetsThree c
  /- Pairs of multisets (s1, s2) such that s1 and s2 are cardinality of `3` containing
    elements of `c` and that all elements of `c` are in `s1 + s2`. -/
  let S5p : Multiset (Multiset 𝓩 × Multiset 𝓩) :=
    (S53.product S53).filter fun (s1, s2) => c.val ≤ s1 + s2
  let Fp : Multiset (FiveQuanta 𝓩) :=
    S5p.map (fun y => y.1.map (fun z => (z, ⟨1, -1⟩)) + y.2.map (fun z => (z, ⟨0, 1⟩)))
  Fp

lemma toFluxesFive_of_mem_ofChargesExpand (c : Finset 𝓩)
    {x : FiveQuanta 𝓩} (h : x ∈ ofChargesExpand c) :
    x.toFluxesFive = {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  simp [ofChargesExpand] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  simp [toFluxesFive, s1_card, s2_card]
  decide

lemma toCharges_of_mem_ofChargesExpand (c : Finset 𝓩)
    {x : FiveQuanta 𝓩} (h : x ∈ ofChargesExpand c) :
    x.toCharges.toFinset = c := by
  simp [ofChargesExpand] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  simp [toCharges]
  trans (s1 + s2).toFinset
  · exact Eq.symm (Multiset.toFinset_add s1 s2)
  ext a
  simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.mem_toFinset]
  constructor
  · intro hr
    rcases hr with hr | hr
    · apply s1_subset
      simpa using hr
    · apply s2_subset
      simpa using hr
  · intro hr
    simpa using Multiset.mem_of_le hsum hr

lemma mem_ofChargesExpand_of_toCharges_toFluxesFive (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x.toCharges.toFinset = c) (h2 : x.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩}) :
    x ∈ ofChargesExpand c := by
  simp [ofChargesExpand]
  let s1 := (x.filter (fun y => y.2 = ⟨1, -1⟩)).map Prod.fst
  let s2 := (x.filter (fun y => y.2 = ⟨0, 1⟩)).map Prod.fst
  use s1, s2
  have hx : Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x
        = Multiset.filter (fun y => ¬ y.2 = ⟨1, -1⟩) x := by
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
    trans (Multiset.filter (fun y => y = ⟨1, -1⟩) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · simp [s2, ← h, toCharges]
  · simp [s2]
    trans (Multiset.filter (fun y => y = ⟨0, 1⟩) (x.toFluxesFive)).card
    · rw [toFluxesFive, Multiset.filter_map]
      simp
    rw [h2]
    decide
  · rw [← h]
    simp [s1, s2, toCharges]
    rw [← Multiset.map_add]
    refine (Multiset.le_iff_subset (Multiset.nodup_dedup (Multiset.map Prod.fst x))).mpr ?_
    simp only [Multiset.dedup_subset']
    refine Multiset.map_subset_map ?_
    rw [hx, Multiset.filter_add_not]
    exact fun ⦃a⦄ a => a
  · simp [s1, s2]
    have h1 : Multiset.map (fun x => (x.1, ⟨1, -1⟩)) (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x)
        = (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x) := by
      trans Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = ⟨1, -1⟩) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    have h2 : Multiset.map (fun x => (x.1, ⟨0, 1⟩)) (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x)
        = (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x) := by
      trans Multiset.map (fun x => x) (Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x)
      · apply Multiset.map_congr
        · rfl
        · intro y hx
          simp at hx
          rw [← hx.2]
      simp
    rw [h1, h2, hx]
    exact Multiset.filter_add_not (fun y => y.2 = ⟨1, -1⟩) x

lemma mem_ofChargesExpand_iff(c : Finset 𝓩) {x : FiveQuanta 𝓩} :
    x ∈ ofChargesExpand c ↔
    x.toCharges.toFinset = c ∧ x.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  constructor
  · intro h
    constructor
    exact toCharges_of_mem_ofChargesExpand c h
    exact toFluxesFive_of_mem_ofChargesExpand c h
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact mem_ofChargesExpand_of_toCharges_toFluxesFive c h1 h2

lemma eq_sum_filter_of_mem_ofChargesExpand (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F = (F.filter fun x => x.2 = ⟨1, -1⟩) + (F.filter fun x => x.2 = ⟨0, 1⟩) := by
  rw [mem_ofChargesExpand_iff] at h
  obtain ⟨hc, h⟩ := h
  have h1 : Multiset.filter (fun x => x.2 = ⟨0, 1⟩) F
      = Multiset.filter (fun x => ¬ x.2 = ⟨1, -1⟩) F := by
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
  exact Eq.symm (Multiset.filter_add_not (fun x => x.2 = ⟨1, -1⟩) F)

lemma mem_ofChargesExpand_of_noExotics_hasNoZero (F : FiveQuanta 𝓩) (c : Finset 𝓩)
    (hc : F.toCharges.toFinset = c)
    (h1 : F.toFluxesFive.NoExotics) (h2 : F.toFluxesFive.HasNoZero) :
    ∃ y ∈ ofChargesExpand c, y.reduce = F.reduce := by
  have hf : F.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
    simp_all
    exact h2
  use F.decompose
  apply And.intro
  · rw [mem_ofChargesExpand_iff]
    constructor
    · trans F.decompose.toCharges.dedup.toFinset
      · simp
      · rw [decompose_toCharges_dedup F hf, ← hc]
        simp
    · rw [decompose_toFluxesFive F hf]
  · rw [decompose_reduce F hf]

lemma reduce_hasNoZeros_of_mem_ofChargesExpand (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive.HasNoZero := by
  simp [reduce, toFluxesFive, FluxesFive.HasNoZero]
  intro x hx
  have hs : (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F))
      ∈ F.toFluxesFive.powerset := by
    simp [toFluxesFive]
  have h1 : Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F) ≠ 0 := by
    simp only [ne_eq, Multiset.map_eq_zero]
    rw [@Multiset.filter_eq_nil]
    simp [Prod.forall, not_forall, Classical.not_imp, Decidable.not_not, exists_and_right,
      exists_eq_right]
    simp [toCharges] at hx
    obtain ⟨a, h⟩ := hx
    use a
  generalize (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F)) = s at *
  rw [mem_ofChargesExpand_iff] at h
  rw [h.2] at hs
  fin_cases hs
  · simp at h1
  all_goals
  · decide

lemma reduce_noExotics_of_mem_ofChargesExpand (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive.NoExotics := by
  apply reduce_noExotics_of_mem_elemsNoExotics
  rw [mem_ofChargesExpand_iff] at h
  rw [h.2]
  decide

lemma reduce_mem_elemsNoExotics_of_mem_ofChargesExpand (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
  rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
  constructor
  · exact reduce_noExotics_of_mem_ofChargesExpand c F h
  · exact reduce_hasNoZeros_of_mem_ofChargesExpand c F h

lemma mem_ofChargesExpand_map_reduce_iff (c : Finset 𝓩) (S : FiveQuanta 𝓩) :
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
    simp only [Multiset.mem_map]
    rw [← h.2.2]
    have h1 := h.1
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at h1
    refine mem_ofChargesExpand_of_noExotics_hasNoZero S c ?_ ?_ ?_
    · exact h.2.1
    · exact h1.1
    · exact h1.2

end ofChargesExpand


/-!

## Anomaly cancellation

-/

section ACCs

variable [CommRing 𝓩]

/--
  The anomaly coefficent of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficent (F : FiveQuanta 𝓩) : 𝓩 × 𝓩 :=
  ((F.map fun x => x.2.2 • x.1).sum, (F.map fun x => x.2.2 • (x.1 * x.1)).sum)

@[simp]
lemma anomalyCoefficent_of_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (F : FiveQuanta 𝓩) :
    FiveQuanta.anomalyCoefficent (F.map fun y => (f y.1, y.2) : FiveQuanta 𝓩1) =
    (f.prodMap f) F.anomalyCoefficent := by
  simp [FiveQuanta.anomalyCoefficent, map_multiset_sum, Multiset.map_map]

lemma anomalyCoefficent_of_reduce (F : FiveQuanta 𝓩) [DecidableEq 𝓩] :
    F.reduce.anomalyCoefficent = F.anomalyCoefficent := by
  simp [anomalyCoefficent]
  constructor
  · let f : 𝓩 → Fluxes →+ 𝓩 := fun q5 => {
      toFun := fun x => x.2 • q5
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul] }
    simpa [f] using reduce_sum_eq_sum_toCharges F f
  · let f : 𝓩 → Fluxes →+ 𝓩 := fun q5 => {
      toFun := fun x => x.2 • (q5 * q5)
      map_zero' := by simp
      map_add' := by
        intros x y
        simp [add_mul] }
    simpa [f] using reduce_sum_eq_sum_toCharges F f

end ACCs

end FiveQuanta

end SU5
end FTheory
