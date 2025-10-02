/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness
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

namespace SU5
open SU5
variable {I : CodimensionOneConfig}

/-- The quanta of w0d representations corresponding to a multiset of
  `(q, M, N)` for each partcile. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev TenQuanta (𝓩 : Type := ℤ) : Type := Multiset (𝓩 × Fluxes)

namespace TenQuanta

variable {𝓩 : Type}

/-- The underlying `FluxesTen` from a `TenQuanta`. -/
def toFluxesTen (x : TenQuanta 𝓩) : FluxesTen := x.map Prod.snd

/-- The underlying Multiset charges from a `TenQuanta`. -/
def toCharges (x : TenQuanta 𝓩) : Multiset 𝓩 := x.map Prod.fst


def toChargeMap [DecidableEq 𝓩] (x : TenQuanta 𝓩) : 𝓩 → Fluxes :=
  fun z => ((x.filter fun p => p.1 = z).map Prod.snd).sum

lemma toChargeMap_of_not_mem [DecidableEq 𝓩] (x : TenQuanta 𝓩) {z : 𝓩} (h : z ∉ x.toCharges) :
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

## Reduce

-/

section reduce

variable [DecidableEq 𝓩]

/-- The `reduce` of `TenQuanta` is a new `TenQuanta` with all the fluxes
  corresponding to the same charge (i.e. represenation) added together. -/
def reduce (x : TenQuanta 𝓩) : TenQuanta 𝓩 :=
  x.toCharges.dedup.map fun q10 => (q10, ((x.filter (fun f => f.1 = q10)).map (fun y => y.2)).sum)

lemma reduce_nodup (x : TenQuanta 𝓩) : x.reduce.Nodup := by
  simp [reduce, toCharges]
  refine Multiset.Nodup.map ?_ ?_
  · intro q1 q2 h
    simp at h
    exact h.1
  · exact Multiset.nodup_dedup (Multiset.map Prod.fst x)

@[simp]
lemma reduce_dedup (x : TenQuanta 𝓩) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup

lemma reduce_toCharges (x : TenQuanta 𝓩) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]

lemma reduce_eq_val (x : TenQuanta 𝓩) :
    x.reduce = (x.toCharges.toFinset.image fun q10 =>
      (q10, ((x.filter (fun f => f.1 = q10)).map (fun y => y.2)).sum)).val := by
  simp only [Finset.image_val, Multiset.toFinset_val]
  rw [← reduce]
  simp

lemma mem_reduce_iff (x : TenQuanta 𝓩) (p : 𝓩 × Fluxes) :
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

lemma reduce_filter (x : TenQuanta 𝓩) (q : 𝓩) (h : q ∈ x.toCharges) :
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
lemma reduce_reduce (x : TenQuanta 𝓩) :
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

lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : TenQuanta 𝓩) (f : 𝓩 → Fluxes →+ M) :
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

lemma reduce_eq_self_of_ofCharges_nodup (x : TenQuanta 𝓩) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce]
  rw [Multiset.Nodup.dedup h]
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



lemma reduce_toChargeMap_eq (x : TenQuanta 𝓩) :
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

lemma mem_powerset_sum_of_mem_reduce_toFluxesTen {F : TenQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesTen) :
    f ∈ (Multiset.powerset F.toFluxesTen).map fun s => s.sum := by
  rw [toFluxesTen, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map, Multiset.mem_powerset]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [toFluxesTen]
  refine Multiset.map_le_map ?_
  exact Multiset.filter_le (fun x => x.1 = q) F

lemma reduce_numChiralU_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralU = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]  at hx
    exact hx.1
  rw [← hE.2.2.1, FluxesTen.numChiralU, FluxesTen.numChiralU, FluxesTen.chiralIndicesOfU]
  trans (F.reduce.toFluxesTen.map (fun f => f.M - f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M - x.N, by simp⟩,
      fun x y => by simp; ring⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfU, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M - f.N) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

lemma reduce_numAntiChiralU_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralU = 0 := by
  rw [FluxesTen.numAntiChiralU, FluxesTen.chiralIndicesOfU]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M - f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl

lemma reduce_numChiralQ_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralQ = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]  at hx
    exact hx.1
  rw [← hE.1, FluxesTen.numChiralQ, FluxesTen.numChiralQ, FluxesTen.chiralIndicesOfQ]
  trans (F.reduce.toFluxesTen.map (fun f => f.M)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M, by simp⟩,
      fun x y => by simp⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfQ, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

lemma reduce_numAntiChiralQ_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralQ = 0 := by
  rw [FluxesTen.numAntiChiralQ, FluxesTen.chiralIndicesOfQ]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl


lemma reduce_numChiralE_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numChiralE = 3 := by
  have hE : F.toFluxesTen.NoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]  at hx
    exact hx.1
  rw [← hE.2.2.2.2.1, FluxesTen.numChiralE, FluxesTen.numChiralE, FluxesTen.chiralIndicesOfE]
  trans (F.reduce.toFluxesTen.map (fun f => f.M + f.N)).sum
  · congr
    refine Multiset.filter_eq_self.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  · let f : 𝓩 → Fluxes →+ ℤ := fun q5 => ⟨⟨fun x => x.M + x.N, by simp⟩,
      fun x y => by simp; ring⟩
    rw [toFluxesTen, Multiset.map_map]
    change (F.reduce.map (fun (q5, x) => f q5 x)).sum = _
    rw [reduce_sum_eq_sum_toCharges]
    congr
    rw [FluxesTen.chiralIndicesOfE, toFluxesTen, Multiset.map_map]
    refine (Multiset.filter_eq_self.mpr ?_).symm
    have h' : Multiset.map (fun x => (f x.1) x.2) F = F.toFluxesTen.map (fun f => f.M + f.N) := by
      simp [toFluxesTen, Multiset.map_map]
      rfl
    rw [h']
    clear h'
    generalize F.toFluxesTen = G at *
    revert G
    decide

lemma reduce_numAntiChiralE_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.numAntiChiralE = 0 := by
  rw [FluxesTen.numAntiChiralE, FluxesTen.chiralIndicesOfE]
  have hx : (Multiset.filter (fun x => x < 0) (F.reduce.toFluxesTen.map (fun f => f.M + f.N)))
      = 0 := by
    refine Multiset.filter_eq_nil.mpr ?_
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesTen hf
    generalize F.toFluxesTen = G at *
    revert f
    revert G
    decide
  rw [hx]
  rfl
lemma reduce_noExotics_of_mem_elemsNoExotics {F : TenQuanta 𝓩}
    (hx : F.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    F.reduce.toFluxesTen.NoExotics := by
  rw [FluxesTen.NoExotics]
  rw [reduce_numChiralU_of_mem_elemsNoExotics hx, reduce_numAntiChiralU_of_mem_elemsNoExotics hx,
    reduce_numChiralQ_of_mem_elemsNoExotics hx, reduce_numAntiChiralQ_of_mem_elemsNoExotics hx,
    reduce_numChiralE_of_mem_elemsNoExotics hx, reduce_numAntiChiralE_of_mem_elemsNoExotics hx]
  simp

end reduce

/-!

## Anomaly cancellation

-/
section ACCs

variable [CommRing 𝓩]

/--
  The anomaly coefficent of a `TenQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084.
  The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
    see equation (23) of arXiv:1401.5084.
-/
def anomalyCoefficent (F : TenQuanta 𝓩) : 𝓩 × 𝓩 :=
  ((F.map fun x => x.2.2 • x.1).sum, 3 * (F.map fun x => x.2.2 • (x.1 * x.1)).sum)

@[simp]
lemma anomalyCoefficent_of_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (F : TenQuanta 𝓩) :
    TenQuanta.anomalyCoefficent (F.map fun y => (f y.1, y.2) : TenQuanta 𝓩1) =
    (f.prodMap f) F.anomalyCoefficent := by
  simp [TenQuanta.anomalyCoefficent, map_multiset_sum, Multiset.map_map, map_ofNat]

lemma anomalyCoefficent_of_reduce [DecidableEq 𝓩] (F : TenQuanta 𝓩) :
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
    apply congrArg
    simpa [f] using reduce_sum_eq_sum_toCharges F f

end ACCs

/-!

## Decomposition of a `TenQuanta`

-/


def decomposeFluxes (f : Fluxes) : Multiset Fluxes :=
  if f = ⟨1, 0⟩ then {⟨1, 0⟩}
  else if f = ⟨1, 1⟩ then {⟨1, 1⟩}
  else if f = ⟨1, -1⟩ then {⟨1, -1⟩}
  else if f = ⟨2, 1⟩ then {⟨1, 1⟩, ⟨1, 0⟩}
  else if f = ⟨2, -1⟩ then {⟨1, -1⟩, ⟨1, 0⟩}
  else if f = ⟨3, 0⟩ then {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
  else if f = ⟨2, 0⟩ then {⟨1, 0⟩, ⟨1, 0⟩}
  else {f}

lemma decomposeFluxes_sum_of_noExotics (f : Fluxes) (hf : ∃ F ∈ FluxesTen.elemsNoExotics, f ∈ F) :
    (decomposeFluxes f).sum = f := by
  obtain ⟨F, hF, hfF⟩ := hf
  revert f
  revert F
  decide

def decompose (x : TenQuanta 𝓩) : TenQuanta 𝓩 :=
  x.bind fun p => (decomposeFluxes p.2).map fun f => (p.1, f)

lemma decompose_add (x y : TenQuanta 𝓩) :
    (x + y).decompose = x.decompose + y.decompose := by
  simp [decompose]


lemma decompose_filter_charge [DecidableEq 𝓩] (x : TenQuanta 𝓩) (q : 𝓩) :
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
    · simp [h, decompose]


lemma decompose_toChargeMap [DecidableEq 𝓩] (x : TenQuanta 𝓩)
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
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
  use x.toFluxesTen
  simp_all [toFluxesTen]
  use a.1
  exact ha.1

lemma decompose_toCharges_dedup [DecidableEq 𝓩] (x : TenQuanta 𝓩)
   (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics):
    x.decompose.toCharges.dedup = x.toCharges.dedup := by
  refine Multiset.dedup_ext.mpr ?_
  intro q
  simp [decompose, toCharges]
  constructor
  · rintro ⟨a, b, c, h1, h2, rfl⟩
    exact ⟨c, h1⟩
  · rintro ⟨c, h1⟩
    have hn : (decomposeFluxes c) ≠ 0 := by
      have c_mem_f : c ∈ x.toFluxesTen := by
        simp [toFluxesTen]
        use q
      generalize x.toFluxesTen = F at *
      clear h1
      revert c
      revert F
      decide
    apply Multiset.exists_mem_of_ne_zero at hn
    obtain ⟨c', h⟩ := hn
    use c', q, c

lemma decompose_reduce (x : TenQuanta 𝓩) [DecidableEq 𝓩]
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    x.decompose.reduce = x.reduce := by
  rw [reduce, reduce]
  apply Multiset.map_congr
  · rw [decompose_toCharges_dedup x hx]
  · intro q hx'
    simp
    change x.decompose.toChargeMap q = x.toChargeMap q
    rw [decompose_toChargeMap x hx]

lemma decompose_toFluxesFive (x : TenQuanta 𝓩)
    (hx : x.toFluxesTen ∈ FluxesTen.elemsNoExotics) :
    x.decompose.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩} ∨
    x.decompose.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩} := by
  rw [toFluxesTen, decompose]
  rw [Multiset.map_bind]
  simp
  have hx : (Multiset.bind x fun a => decomposeFluxes a.2) =
      (Multiset.bind x.toFluxesTen fun a => decomposeFluxes a) := by
    rw [toFluxesTen, Multiset.bind_map]
  rw [hx]
  clear hx
  generalize x.toFluxesTen = F at *
  revert F
  decide

/-!

## toChargesExpand

-/

section toChargesExpand

open SuperSymmetry.SU5.ChargeSpectrum

variable [DecidableEq 𝓩]

/-- Given a finite set of charges `c` the `TenQuanta`
  with fluxes `{(1, 0), (1, 0), (1, 0)}` and `{(1, 1), (1, -1), (1, 0)}`
  and finite set of charges equal to `c`. -/
def ofChargesExpand (c : Finset 𝓩) : Multiset (TenQuanta 𝓩) :=
  /- The {(1, 0), (1, 0), (1, 0)} case. -/
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S10 : Multiset (Multiset 𝓩) := toMultisetsThree c
  let F1 : Multiset (TenQuanta 𝓩) :=
    (S10.map (fun s => s.map (fun z => (z, ⟨1, 0⟩)))).filter (fun s => c.val ≤ s.toCharges)
  /- The {(1, 1), (1, -1), (1, 0)} case. -/
  let F2 : Multiset (TenQuanta 𝓩) := ((c.product <| c.product <| c).val.map
    fun (x, y, z) => {(x, ⟨1, 1⟩), (y, ⟨1, -1⟩), (z, ⟨1, 0⟩)}).filter (fun s => c.val ≤ s.toCharges)
  /- All together-/
  F1 + F2

lemma toFluxesFive_of_mem_ofChargesExpand (c : Finset 𝓩)
    {x : TenQuanta 𝓩} (h : x ∈ ofChargesExpand c) :
    x.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
    ∨ x.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}:= by
  simp [ofChargesExpand] at h
  rcases h with h | h
  · obtain ⟨⟨s, h, rfl⟩, h'⟩ := h
    left
    simp [toFluxesTen]
    rw [h.2]
    decide
  · obtain ⟨⟨q1, q2, q3, h, rfl⟩, h'⟩ := h
    simp [toFluxesTen]

lemma toCharges_of_mem_ofChargesExpand (c : Finset 𝓩)
    {x : TenQuanta 𝓩} (h : x ∈ ofChargesExpand c) :
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
      simp only [SProd.sprod, Multiset.mem_product] at h
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

lemma mem_ofChargesExpand_of_toCharges_toFluxesTen (c : Finset 𝓩) {x : TenQuanta 𝓩}
    (h : x.toCharges.toFinset = c) (h2 : x.toFluxesTen =
      {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩} ∨ x.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}) :
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
      simp only [SProd.sprod, Multiset.mem_product]
      subst h
      simp only [Multiset.toFinset_val, Multiset.mem_dedup, Int.reduceNeg]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simp [toCharges]
        use p1.2
      · simp [toCharges]
        use p2.2
        apply Multiset.erase_subset p1 x hp2
      · simp [toCharges]
        use p3.2
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

lemma mem_ofChargesExpand_iff (c : Finset 𝓩) {x : TenQuanta 𝓩} :
    x ∈ ofChargesExpand c ↔
    x.toCharges.toFinset = c ∧ (x.toFluxesTen = {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}
    ∨ x.toFluxesTen = {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}) := by
  constructor
  · intro h
    constructor
    exact toCharges_of_mem_ofChargesExpand c h
    exact toFluxesFive_of_mem_ofChargesExpand c h
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact mem_ofChargesExpand_of_toCharges_toFluxesTen c h1 h2

lemma mem_ofChargesExpand_of_noExotics_hasNoZero (F : TenQuanta 𝓩) (c : Finset 𝓩)
    (hc : F.toCharges.toFinset = c)
    (h1 : F.toFluxesTen.NoExotics) (h2 : F.toFluxesTen.HasNoZero) :
    ∃ y ∈ ofChargesExpand c, y.reduce = F.reduce := by
  have hf : F.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
    rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
    simp_all
    exact h2
  use F.decompose
  rw [decompose_reduce F hf]
  simp
  rw [mem_ofChargesExpand_iff]
  apply And.intro
  · trans  F.decompose.toCharges.dedup.toFinset
    · simp
    simp [decompose_toCharges_dedup F hf, ← hc]
  · exact decompose_toFluxesFive F hf

lemma reduce_hasNoZeros_of_mem_ofChargesExpand (c : Finset 𝓩) (F : TenQuanta 𝓩)
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
    obtain ⟨f, h⟩ := hx
    use f
  generalize (Multiset.map (fun y => y.2) (Multiset.filter (fun f => f.1 = x) F)) = s at *
  rw [mem_ofChargesExpand_iff] at h
  rcases h with ⟨h1, h | h⟩
  all_goals
  · rw [h] at hs
    fin_cases hs
    · simp at h1
    all_goals
    · decide

lemma reduce_noExotics_of_mem_ofChargesExpand (c : Finset 𝓩) (F : TenQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesTen.NoExotics := by
  apply reduce_noExotics_of_mem_elemsNoExotics
  rw [mem_ofChargesExpand_iff] at h
  rcases h with ⟨h1, h | h⟩
  all_goals
  · rw [h]
    decide


lemma reduce_mem_elemsNoExotics_of_mem_ofChargesExpand (c : Finset 𝓩) (F : TenQuanta 𝓩)
    (h : F ∈ ofChargesExpand c) :
    F.reduce.toFluxesTen ∈ FluxesTen.elemsNoExotics := by
  rw [← FluxesTen.noExotics_iff_mem_elemsNoExotics]
  constructor
  · exact reduce_noExotics_of_mem_ofChargesExpand c F h
  · exact reduce_hasNoZeros_of_mem_ofChargesExpand c F h

lemma mem_ofChargesExpand_map_reduce_iff (c : Finset 𝓩) (S : TenQuanta 𝓩) :
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

end toChargesExpand
end TenQuanta

end SU5

end FTheory
