/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Basic
/-!

# Contractions of tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {S : TensorSpecies k}

namespace Tensor


/-!

## Pure.contrPCoeff


-/

namespace Pure

/-!

## dropPairEmb

-/

variable {n : ℕ} {c : Fin (n + 1 + 1) → S.C}

def dropPairEmb (i j : Fin (n + 1 + 1)) (hij : i ≠ j) : Fin n ↪o Fin (n + 1 + 1) :=
  (Finset.orderEmbOfFin {i, j}ᶜ
  (by rw [Finset.card_compl]; simp [Finset.card_pair hij]))

lemma dropPairEmb_apply_eq_orderIsoOfFin {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (m : Fin n) :
    (dropPairEmb i j hij) m = (Finset.orderIsoOfFin {i, j}ᶜ
      (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) m := by
  simp [dropPairEmb]

lemma dropPairEmb_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    dropPairEmb i j hij = dropPairEmb j i hij.symm := by
  simp only [dropPairEmb, Finset.pair_comm]

@[simp]
lemma permCond_dropPairEmb_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    PermCond (c ∘ dropPairEmb i j hij) (c ∘ dropPairEmb j i hij.symm) id :=
  And.intro (Function.bijective_id) (by rw [dropPairEmb_symm]; simp)


@[simp]
lemma dropPairEmb_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (dropPairEmb i j hij) = {i, j}ᶜ := by
  rw [dropPairEmb, Finset.range_orderEmbOfFin]
  simp only [Finset.compl_insert, Finset.coe_erase, Finset.coe_compl, Finset.coe_singleton]
  ext x : 1
  simp only [Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff, not_or]
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]

lemma dropPairEmb_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (X : Set (Fin n)) :
    (dropPairEmb i j hij) '' Xᶜ = ({i, j} ∪ dropPairEmb i j hij '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (dropPairEmb i j hij).injective]
  simp only [compl_compl, dropPairEmb_range,  Set.union_singleton]
  exact Set.union_comm (⇑(dropPairEmb i j hij) '' X) {i, j}

@[simp]
lemma fst_neq_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin n) :
    ¬ i = (dropPairEmb i j hij) m  := by
  by_contra hn
  have hi : i ∉ Set.range (dropPairEmb i j hij) := by
    simp [dropPairEmb]
  nth_rewrite 2 [hn] at hi
  simp [- dropPairEmb_range] at hi

@[simp]
lemma snd_neq_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin n) :
    ¬ j = (dropPairEmb i j hij) m  := by
  by_contra hn
  have hi : j ∉ Set.range (dropPairEmb i j hij) := by
    simp [dropPairEmb]
  nth_rewrite 2 [hn] at hi
  simp [- dropPairEmb_range] at hi

def dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
    (Finset.orderIsoOfFin {i, j}ᶜ (by rw [Finset.card_compl]; simp [Finset.card_pair hij])).symm
    ⟨m, by simp [hm]⟩

@[simp]
lemma dropPairEmb_dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : dropPairEmb i j hij (dropPairEmbPre i j hij m hm) = m := by
  rw [dropPairEmb_apply_eq_orderIsoOfFin, dropPairEmbPre]
  simp

@[simp]
lemma dropPairEmbPre_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    dropPairEmbPre i j hij m1 hm1 = dropPairEmbPre i j hij m2 hm2  ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (dropPairEmb i j hij).injective]
  simp

lemma dropPairEmbPre_surjective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    ∃ m' : Fin (n + 1 + 1), ∃ (h : m' ≠ i ∧ m' ≠ j),
    dropPairEmbPre i j hij m' h = m := by
  use (dropPairEmb i j hij) m
  have h : (dropPairEmb i j hij) m ≠ i ∧ (dropPairEmb i j hij) m ≠ j := by
    simp [Ne.symm]
  use h
  apply (dropPairEmb i j hij).injective
  simp


lemma dropPairEmb_comm (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2 =
    dropPairEmb i2' j2' hi2j2' ∘
    dropPairEmb i1' j1' (by simp [i1', j1', hij1]) := by
  intro i2' j2' hi2j2'
  let fl : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2, by
      refine (EmbeddingLike.comp_injective (⇑(dropPairEmb i2 j2 hij2)) (dropPairEmb i1 j1 hij1)).mpr ?_
      exact RelEmbedding.injective (dropPairEmb i2 j2 hij2)⟩, by simp⟩
  let fr : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i2' j2' hi2j2' ∘ dropPairEmb (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']))
      (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2'])) (by simp [hij1]),
      by
      refine (EmbeddingLike.comp_injective _ _).mpr ?_
      exact RelEmbedding.injective _⟩, by simp⟩
  have h : fl = fr := by
    rw [← OrderEmbedding.range_inj]
    simp [fl, fr, Set.range_comp]
    rw [dropPairEmb_image_compl, dropPairEmb_image_compl]
    congr 1
    rw [Set.image_pair, Set.image_pair]
    simp only [Set.union_singleton, dropPairEmb_dropPairEmbPre, i2', j2', fl, fr]
    exact Set.union_comm {i1, j1} {(dropPairEmb i1 j1 hij1) i2, (dropPairEmb i1 j1 hij1) j2}
  ext1 a
  simpa [fl, fr] using congrFun (congrArg (fun x => x.toFun) h) a

lemma dropPairEmb_comm_apply  (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (m : Fin n) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i2' j2' hi2j2'
    (dropPairEmb i1' j1' (by simp [i1', j1', hij1])  m) =
    dropPairEmb i1 j1 hij1  (dropPairEmb i2 j2 hij2 m) := by
  intro i2' j2' hi2j2' i1' j1'
  change _ = (dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2) m
  rw [dropPairEmb_comm i1 j1 i2 j2 hij1 hij2]
  rfl


@[simp]
lemma permCond_dropPairEmb_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    PermCond
      ((c ∘ dropPairEmb i2' j2' hi2j2') ∘ dropPairEmb i1' j1' (by simp [i1', j1', hij1]))
      ((c ∘ dropPairEmb i1 j1 hij1) ∘ dropPairEmb i2 j2 hij2)
      id := by
  apply And.intro (Function.bijective_id)
  simp
  intro i
  rw [dropPairEmb_comm_apply]

lemma eq_or_exists_dropPairEmb
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1)) :
    m = i ∨ m = j ∨ ∃ m', m = dropPairEmb i j hij m' := by
  by_cases h : m = i
  · subst h
    simp
  · by_cases h' : m = j
    · subst h'
      simp
    · simp_all
      have h'' : m ∈ Set.range (dropPairEmb i j hij) := by
        simp_all [dropPairEmb]
      rw [@Set.mem_range] at h''
      obtain ⟨m', rfl⟩ := h''
      exact ⟨m', rfl⟩

/-!

## dropPairOfMap

-/

def dropPairOfMap {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ)
    (m : Fin n1) : Fin n :=
  dropPairEmbPre (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij])
    (σ (dropPairEmb i j hij m)) (by simp [hσ.injective.eq_iff, Ne.symm])

lemma dropPairOfMap_injective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Injective (dropPairOfMap i j hij σ hσ) := by
  intro m1 m2 h
  simpa [dropPairOfMap, hσ.injective.eq_iff] using h

lemma dropPairOfMap_surjective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Surjective (dropPairOfMap i j hij σ hσ) := by
  intro m
  simp [dropPairOfMap, hσ.surjective]
  obtain ⟨m, hm, rfl⟩ := dropPairEmbPre_surjective (σ i) (σ j) (by simp [hσ.injective.eq_iff, hij]) m
  simp
  obtain ⟨m', rfl⟩ := hσ.surjective m
  simp [hσ.injective.eq_iff] at hm ⊢
  rcases eq_or_exists_dropPairEmb i j hij m' with rfl | rfl | ⟨m'', rfl⟩
  · simp_all
  · simp_all
  · exact ⟨m'', rfl⟩

lemma dropPairOfMap_bijective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Bijective (dropPairOfMap i j hij σ hσ) := by
  apply And.intro
  · apply dropPairOfMap_injective
  · apply dropPairOfMap_surjective

lemma permCond_dropPairOfMap {n n1 : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {c1 : Fin (n1 + 1 + 1) → S.C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) :
    PermCond (c ∘ dropPairEmb (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij]))
      (c1 ∘ dropPairEmb i j hij) (dropPairOfMap i j hij σ hσ.1)  := by
  apply And.intro
  · exact dropPairOfMap_bijective i j hij σ hσ.left
  · intro m
    simp [dropPairOfMap, hσ.2]

/-!

## dropPair

-/

def dropEm {n : ℕ} {c : Fin n → S.C} {m : ℕ} (f : Fin m ↪o Fin n) (p : Pure S c) : Pure S (c ∘ f) :=
  fun i => p (f i)

def dropPair (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) :
    Pure S (c ∘ dropPairEmb i j hij) :=
  dropEm (dropPairEmb i j hij) p

@[simp]
lemma dropPair_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) (g : S.G) :
    dropPair i j hij (g • p) = g • dropPair i j hij p := by
  ext m
  simp only [dropPair, dropEm, actionP_eq]
  rfl

lemma dropPair_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure S c) : dropPair i j hij p =
    permP id (by simp) (dropPair j i hij.symm p) := by
  ext m
  simp [dropPair, dropEm, permP]
  refine (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_symm]

lemma dropPair_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPair i2 j2 hij2 (dropPair i1 j1 hij1 p) =
    permP id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1 hij2)
    ((dropPair i1' j1' (by simp [i1', j1', hij1]) (dropPair i2' j2' hi2j2' p))) := by
  ext m
  simp [dropPair, dropEm, permP]
  apply (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_comm_apply]

@[simp]
lemma dropPair_update_fst {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c i))) :
    dropPair i j hij (p.update i x) = dropPair i j hij p := by
  ext m
  simp [dropPair, dropEm, update]
  rw [Function.update_of_ne]
  exact Ne.symm (fst_neq_dropPairEmb_pre i j hij m)

@[simp]
lemma dropPair_update_snd {n : ℕ}  [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c j))) :
    dropPair i j hij (p.update j x) = dropPair i j hij p := by
  rw [dropPair_symm]
  simp
  conv_rhs => rw [dropPair_symm]

@[simp]
lemma dropPair_update_dropPairEmb {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (m : Fin n)
    (x : S.FD.obj (Discrete.mk (c (dropPairEmb i j hij m)))) :
    dropPair i j hij (p.update (dropPairEmb i j hij m) x) =
    (dropPair i j hij p).update m x := by
  ext m'
  simp [dropPair, dropEm, update]
  by_cases h : m' = m
  · subst h
    simp
  · rw [Function.update_of_ne, Function.update_of_ne]
    · rfl
    · simp [h]
    · simp [h]

TODO "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."


@[simp]
lemma dropPair_permP {n n1 : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {c1 : Fin (n1 + 1 + 1) → S.C} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) (p : Pure S c) :
    dropPair i j hij (permP σ hσ p) =
    permP (dropPairOfMap i j hij σ hσ.1) (permCond_dropPairOfMap i j hij σ hσ)
    (dropPair (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij]) p) := by
  ext m
  simp [dropPair, dropEm, permP, dropPairOfMap]
  apply congr_mid
  · simp
  · simp [hσ.2]
  · simp [hσ.2]

/-!

## Contraction coefficent

-/

noncomputable def contrPCoeff {n : ℕ} {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i))) (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p j)))

@[simp]
lemma contrPCoeff_permP {n n1 : ℕ} {c : Fin n → S.C}
    {c1 : Fin n1 → S.C} (i j : Fin n1) (hij : i ≠ j ∧ c1 i = S.τ (c1 j))
    (σ : Fin n1 → Fin n) (hσ : PermCond c c1 σ) (p : Pure S c) :
    contrPCoeff i j hij (permP σ hσ p) =
    contrPCoeff (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij, hσ.2]) p := by
  simp [contrPCoeff, permP]
  conv_rhs => erw [S.contr_congr (c (σ i)) ((c1 i)) (by simp [hσ.2]) ]
  simp
  apply congrArg
  congr 1
  change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ =
    ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp


@[simp]
lemma contrPCoeff_update_dropPairEmb {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]  {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (m : Fin n)
    (p : Pure S c) (x : S.FD.obj (Discrete.mk (c (dropPairEmb i j hij.1 m)))) :
    contrPCoeff i j hij (p.update (dropPairEmb i j hij.1 m) x) =
    contrPCoeff i j hij p := by
  simp only [contrPCoeff]
  congr
  · simp [update]
  · simp [update]

@[simp]
lemma contrPCoeff_update_fst_add {n : ℕ} [inst : DecidableEq (Fin n)]  {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (x + y)) =
    contrPCoeff i j hij (p.update i x) + contrPCoeff i j hij (p.update i y) := by
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  simp [Function.update_of_ne (Ne.symm hij.1), contrPCoeff, update, TensorProduct.add_tmul, map_add]

@[simp]
lemma contrPCoeff_update_snd_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (x + y)) =
    contrPCoeff i j hij (p.update j x) + contrPCoeff i j hij (p.update j y) := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1,
    Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (x + y)
  simp [contrPCoeff, update, TensorProduct.tmul_add, map_add]
  rfl

@[simp]
lemma contrPCoeff_update_fst_smul {n : ℕ} [inst : DecidableEq (Fin n)]  {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (r • x)) =
    r * contrPCoeff i j hij (p.update i x) := by
  simp [contrPCoeff, update, TensorProduct.smul_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = r * _
  simp
  congr 1
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne (Ne.symm hij.1), Function.update_of_ne (Ne.symm hij.1)]

@[simp]
lemma contrPCoeff_update_snd_smul {n : ℕ} [inst : DecidableEq (Fin n)]  {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (r • x)) =
    r * contrPCoeff i j hij (p.update j x) := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ =  r * _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (r • _)
  simp
  rfl

lemma contrPCoeff_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
     (a b : Fin (n + 1 + 1 )) (hab : a ≠ b)
    (i j : Fin n) (hij : i ≠ j ∧ c (dropPairEmb a b hab i) = S.τ (c (dropPairEmb a b hab j)))
    (p : Pure S c) : (p.dropPair a b hab).contrPCoeff i j hij =
    p.contrPCoeff (dropPairEmb a b hab i) (dropPairEmb a b hab j)
      (by simpa using hij) := by rfl

lemma contrPCoeff_symm {n : ℕ} {c : Fin n → S.C} {i j : Fin n} {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c} :
    p.contrPCoeff i j hij = p.contrPCoeff j i ⟨hij.1.symm, by simp [hij]⟩ := by
  rw [contrPCoeff, contrPCoeff]
  erw [S.contr_tmul_symm]
  rw [S.contr_congr (S.τ (c i)) (c j) ]
  simp
  change _ = (ConcreteCategory.hom (S.contr.app { as := c j }).hom) _
  congr 2
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
  · change ( (S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
    rfl
  · simp [hij.2]

lemma contrPCoeff_mul_dropPair {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ c i1 = S.τ (c j1))
    (hij2 : i2 ≠ j2 ∧ c (dropPairEmb i1 j1 hij1.1 i2) = S.τ (c (dropPairEmb i1 j1 hij1.1 j2)))
    (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 hij1.1 i2);
    let j2' := (dropPairEmb i1 j1 hij1.1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    (p.contrPCoeff i1 j1 hij1) * (dropPair i1 j1 hij1.1 p).contrPCoeff i2 j2 hij2  =
    (p.contrPCoeff i2' j2' (by simp [i2', j2', hij2])) *
    (dropPair i2' j2' (by simp [i2', j2', hij2]) p).contrPCoeff i1' j1' (by simp [i1', j1', hij1]) := by
  simp only [ne_eq, contrPCoeff_dropPair, dropPairEmb_dropPairEmbPre]
  rw [mul_comm]

@[simp]
lemma contrPCoeff_invariant {n : ℕ} {c : Fin n → S.C} {i j : Fin n}
    {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c}
    (g : S.G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  calc (g • p).contrPCoeff i j hij
    _ =  (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij])))
          ((S.FD.obj _).ρ g (p j)))) := rfl
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ (S.FD.obj _).ρ g ((S.FD.map (eqToHom (by simp [hij])))
          (p j))) := by
        congr 2
        simp
        have h1 := (S.FD.map (eqToHom (by simp [hij] : { as := c j } =
          (Discrete.functor (Discrete.mk ∘ S.τ)).obj { as := c i }))).comm g
        have h2 := congrFun (congrArg (fun x => x.hom) h1) (p j)
        simp at h2
        exact h2
  have h1 := (S.contr.app (Discrete.mk (c i))).comm g
  have h2 := congrFun (congrArg (fun x => x.hom) h1) ( (p i) ⊗ₜ
    ((S.FD.map (eqToHom (by simp [hij]))) (p j)))
  simp at h2
  exact h2

/-!

## Contractions

-/

noncomputable def contrP {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) :
    S.Tensor (c ∘ dropPairEmb i j hij.1) :=
  (p.contrPCoeff i j hij) • (p.dropPair i j hij.1).toTensor

@[simp]
lemma contrP_update_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → S.C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (x + y)) =
    contrP i j hij (p.update m x) + contrP i j hij (p.update m y) := by
  rcases eq_or_exists_dropPairEmb i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, add_smul]
  · simp [contrP, add_smul]
  · simp [contrP]

@[simp]
lemma contrP_update_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]  {c : Fin (n + 1 + 1) → S.C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j))
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (r • x)) =
    r • contrP i j hij (p.update m x) := by
  rcases eq_or_exists_dropPairEmb i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul, mul_comm]

@[simp]
lemma contrP_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) (g : S.G) :
    contrP i j hij (g • p) = g • contrP i j hij p := by
  simp [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_pure]

lemma contrP_symm {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c} :
    contrP i j hij p = permT id (by simp)
    (contrP j i ⟨hij.1.symm, by simp [hij]⟩ p) := by
  rw [contrP, contrPCoeff_symm, dropPair_symm]
  simp [contrP, permT_pure]

/-!

## contrP as a multilinear map

-/

noncomputable def contrPMultilinear {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i)))
      (S.Tensor (c ∘ dropPairEmb i j hij.1))where
  toFun p :=  contrP i j hij p
  map_update_add' p m x y := by
    change (update p m (x + y)).contrP i j hij = _
    simp
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).contrP i j hij = _
    rw [Pure.contrP_update_smul]
    rfl


end Pure


/-!

## contrT

-/

open Pure

noncomputable def contrT {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i j : Fin (n + 1 + 1))
      (hij : i ≠ j ∧ c i = S.τ (c j)) :
    Tensor S c →ₗ[k] Tensor S (c ∘ dropPairEmb i j hij.1) :=
  PiTensorProduct.lift (Pure.contrPMultilinear i j hij)

@[simp]
lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i j : Fin (n + 1 + 1))
      (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) :
    contrT i j hij p.toTensor = p.contrP i j hij := by
  simp only [contrT, Pure.toTensor]
  change _ = ((Pure.contrPMultilinear i j hij) p)
  conv_rhs => rw [← PiTensorProduct.lift.tprod]
  rfl

@[simp]
lemma contrT_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (g : S.G)
    (t : Tensor S c) :
    contrT i j hij (g • t) = g • contrT i j hij t := by
  let P (t : Tensor S c) : Prop := contrT i j hij (g • t) = g • contrT i j hij t
  change P t
  apply induction_on_pure
  · intro p
    simp [P]
    rw [actionT_pure, contrT_pure]
    simp [Pure.contrP]
    congr 1
    exact Eq.symm actionT_pure
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]

lemma contrT_permT {n n1 : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {c1 : Fin (n1 + 1 + 1) → S.C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j ∧ c1 i = S.τ (c1 j))
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1))
    (hσ : PermCond c c1 σ) (t : Tensor S c) :
    contrT i j hij (permT σ hσ t) = permT (dropPairOfMap i j hij.1 σ hσ.1)
      (permCond_dropPairOfMap i j hij.1 σ hσ)
      (contrT (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t) := by
  let P (t : Tensor S c) : Prop := contrT i j hij (permT σ hσ t) =
      permT (dropPairOfMap i j hij.1 σ hσ.1)
        (permCond_dropPairOfMap i j hij.1 σ hσ)
        (contrT (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t)
  change P t
  apply induction_on_pure
  · intro p
    simp [P]
    rw [permT_pure, contrT_pure]
    simp [contrP]
    congr
    rw [permT_pure]
  · intro r t ht
    simp_all [P]
  · intro t1 t2 ht1 ht2
    simp_all [P]

lemma contrT_symm {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ c i = S.τ (c j)} (t : Tensor S c) :
    contrT i j hij t = permT id (by simp)
      (contrT j i ⟨hij.1.symm, by simp [hij]⟩ t) := by
  let P (t : Tensor S c) : Prop := contrT i j hij t = permT id (by simp)
      (contrT j i ⟨hij.1.symm, by simp [hij]⟩ t)
  change P t
  apply induction_on_pure
  · intro p
    simp [P]
    rw [contrP_symm]
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]

lemma contrT_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
      (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
      (hij1 : i1 ≠ j1 ∧ c i1 = S.τ (c j1))
      (hij2 : i2 ≠ j2 ∧ c (dropPairEmb i1 j1 hij1.1 i2) = S.τ (c (dropPairEmb i1 j1 hij1.1 j2)))
      (t : Tensor S c) :
      let i2' := (dropPairEmb i1 j1 hij1.1 i2);
      let j2' := (dropPairEmb i1 j1 hij1.1 j2);
      have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
      let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
      let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
      contrT i2 j2 hij2 (contrT i1 j1 hij1 t) =
      permT id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1.left hij2.left)
        (contrT i1' j1' (by simp [i1', j1', i2', j2', hij1])
        (contrT i2' j2' (by simp [i2', j2', hij2]) t)) := by
  let i2' := (dropPairEmb i1 j1 hij1.1 i2);
  let j2' := (dropPairEmb i1 j1 hij1.1 j2);
  let i1' := (dropPairEmbPre i2' j2' (by simp [i2', j2', dropPairEmb, hij2]) i1 (by simp [i2', j2']));
  let j1' := (dropPairEmbPre i2' j2' (by simp [i2', j2', dropPairEmb, hij2])  j1 (by simp [i2', j2']));
  let P (t : Tensor S c) : Prop := contrT i2 j2 hij2 (contrT i1 j1 hij1 t) =
      permT id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1.left hij2.left)
        (contrT i1' j1' (by simp [i1', j1', i2', j2', hij1])
        (contrT i2' j2' (by simp [i2', j2', hij2]) t))
  change P t
  apply induction_on_pure
  · intro p
    dsimp only [P]
    conv_lhs => enter [2]; rw [contrT_pure, contrP]
    conv_lhs => rw [map_smul, contrT_pure, contrP, smul_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
    conv_rhs => enter [2, 2]; rw [contrT_pure, contrP]
    conv_rhs => enter [2]; rw [map_smul, permT_pure]
    conv_rhs => rw [smul_smul]
    congr 1
    · exact contrPCoeff_mul_dropPair i1 j1 i2 j2 hij1 hij2 p
    · congr 1
      rw [dropPair_comm]
  · intro p q hp
    dsimp only [P] at hp ⊢
    conv_lhs => rw [map_smul, map_smul, hp]
    conv_rhs => enter [2, 2]; rw [map_smul]
    conv_rhs => enter [2]; rw [map_smul]
    conv_rhs => rw [map_smul]
  · intro p r hp hr
    dsimp only [P] at hp hr ⊢
    conv_lhs => rw [map_add, map_add, hp]
    conv_lhs => enter [2]; rw [hr]
    conv_rhs => enter [2, 2]; rw [map_add]
    conv_rhs => enter [2]; rw [map_add]
    conv_rhs => rw [map_add]


/-!

## Products and contractions

-/

proof_wanted prodT_contrT_snd {n n1 : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {c1 : Fin n1 → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j))
    (t : Tensor S c) (t1 : Tensor S c1) :
    prodT t1 (contrT i j hij t) =
    (permT id (And.intro (Function.bijective_id) (by
      intro k
      simp only [Nat.add_eq, id_eq, Function.comp_apply]
      sorry
      )) <|
    contrT
      (finSumFinEquiv (m := n1) (Sum.inr i))
      (finSumFinEquiv (m := n1) (Sum.inr j))
      (by simp [hij, - finSumFinEquiv_apply_right, finSumFinEquiv.injective.eq_iff]) <|
    prodT t1 t)

end Tensor

end TensorSpecies
