/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.BackAndForth
public import Architect
public import Mathlib.SetTheory.Ordinal.Family

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

open FirstOrder Structure Fin Ordinal

/-- A pair of finite tuples of the same arity. -/
abbrev TuplePair (M : Type w) (N : Type w') := Σ n : ℕ, (Fin n → M) × (Fin n → N)

/-- A potential isomorphism between structures M and N is a family of finite partial
maps (given as pairs of compatible tuples) that is nonempty and is closed
under extension in both directions.

This is the model-theoretic notion corresponding to "back-and-forth system" or
"winning strategy in the infinite EF game." -/
@[blueprint "def:potential-iso"
  (title := /-- Potential isomorphism -/)
  (statement := /-- A potential isomorphism between $L$-structures $M$ and $N$: a
    nonempty family of finite partial maps (pairs of same-length tuples) preserving
    atomic type and closed under extension in both directions. -/)
  (uses := ["def:BFEquiv"])]
structure PotentialIso (L : Language.{u, v}) [L.IsRelational]
    (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] where
  /-- The family of partial maps, represented as pairs of tuples of equal length. -/
  family : Set (TuplePair M N)
  /-- The family has a starting pair. -/
  nonempty : family.Nonempty
  /-- Each pair in the family preserves atomic type. -/
  compatible : ∀ p ∈ family, SameAtomicType (L := L) p.2.1 p.2.2
  /-- Forth: for any pair and any element of M, there's an extension in the family. -/
  forth : ∀ p ∈ family, ∀ m : M, ∃ n' : N,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family
  /-- Back: for any pair and any element of N, there's an extension in the family. -/
  back : ∀ p ∈ family, ∀ n' : N, ∃ m : M,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family

namespace PotentialIso

variable {M N : Type w} [L.Structure M] [L.Structure N]

section Chain

variable (P : PotentialIso L M N) {p : TuplePair M N} (hp : p ∈ P.family)
  (enum : ℕ → M ⊕ N)

/-- Extend the chosen member, scheduling each carrier point from a single enumeration. -/
private noncomputable def buildChain : (i : ℕ) →
    {q : (Fin (p.1 + i) → M) × (Fin (p.1 + i) → N) // ⟨p.1 + i, q⟩ ∈ P.family}
  | 0 => ⟨p.2, hp⟩
  | i + 1 =>
    let ⟨(a, b), h⟩ := buildChain i
    match enum i with
    | .inl m =>
      let h' := P.forth ⟨_, a, b⟩ h m
      ⟨(Fin.snoc a m, Fin.snoc b h'.choose), h'.choose_spec⟩
    | .inr n =>
      let h' := P.back ⟨_, a, b⟩ h n
      ⟨(Fin.snoc a h'.choose, Fin.snoc b n), h'.choose_spec⟩

local notation "C" => P.buildChain hp enum

private def atPair {k : ℕ} (q : (Fin k → M) × (Fin k → N)) (r : Fin k) : M × N :=
  (q.1 r, q.2 r)

private theorem chain_step {i : ℕ} (r : Fin (p.1 + i)) :
    atPair (C (i + 1)).val (Fin.castSucc r) = atPair (C i).val r := by
  simp only [buildChain]
  split <;> simp [atPair]

private theorem chain_cast {i j : ℕ} (h : i ≤ j) (r : Fin (p.1 + i)) :
    atPair (C j).val (Fin.castLE (Nat.add_le_add_left h _) r) = atPair (C i).val r := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j h ih => exact (P.chain_step hp enum (Fin.castLE (Nat.add_le_add_left h _) r)).trans ih

end Chain

/-- The countable back-and-forth extends any chosen member of the family. -/
theorem exists_equiv_of_mem [Countable M] [Countable N] (P : PotentialIso L M N)
    {p : TuplePair M N} (hp : p ∈ P.family) :
    ∃ e : M ≃[L] N, ∀ i, e (p.2.1 i) = p.2.2 i := by
  classical
  by_cases hM : IsEmpty M
  · have hN : IsEmpty N := ⟨fun n => hM.false (P.back _ hp n).choose⟩
    refine ⟨⟨Equiv.equivOfIsEmpty M N, fun f _ => isEmptyElim f, fun {k} r x => ?_⟩,
      fun i => (hM.false (p.2.1 i)).elim⟩
    have hk : k = 0 := by by_contra h; exact hM.false (x ⟨0, Nat.pos_of_ne_zero h⟩)
    subst k
    simpa only [AtomicIdx.holds, show p.2.1 ∘ Fin.elim0 = x from Subsingleton.elim _ _,
      show p.2.2 ∘ Fin.elim0 = (Equiv.equivOfIsEmpty M N).toFun ∘ x from Subsingleton.elim _ _] using
      (P.compatible _ hp (.rel r Fin.elim0)).symm
  haveI : Nonempty M := not_isEmpty_iff.mp hM
  obtain ⟨enum, henum⟩ := exists_surjective_nat (M ⊕ N)
  let C := P.buildChain hp enum
  have h₁ (m : M) : ∃ i, ∃ r : Fin (p.1 + i), (C i).val.1 r = m := by
    obtain ⟨i, hi⟩ := henum (.inl m)
    exact ⟨i + 1, Fin.last _, by simp [C, buildChain, hi]⟩
  have h₂ (n : N) : ∃ i, ∃ r : Fin (p.1 + i), (C i).val.2 r = n := by
    obtain ⟨i, hi⟩ := henum (.inr n)
    exact ⟨i + 1, Fin.last _, by simp [C, buildChain, hi]⟩
  have agree {i j : ℕ} (r : Fin (p.1 + i)) (s : Fin (p.1 + j)) :
      (C i).val.1 r = (C j).val.1 s ↔ (C i).val.2 r = (C j).val.2 s := by
    let r' := Fin.castLE (Nat.add_le_add_left (le_max_left i j) p.1) r
    let s' := Fin.castLE (Nat.add_le_add_left (le_max_right i j) p.1) s
    have h := P.compatible _ (C (max i j)).property (.eq r' s')
    change (C (max i j)).val.1 r' = (C (max i j)).val.1 s' ↔
      (C (max i j)).val.2 r' = (C (max i j)).val.2 s' at h
    have hr : atPair (C (max i j)).val r' = atPair (C i).val r :=
      P.chain_cast hp enum (le_max_left i j) r
    have hs : atPair (C (max i j)).val s' = atPair (C j).val s :=
      P.chain_cast hp enum (le_max_right i j) s
    simp only [atPair, Prod.mk.injEq] at hr hs
    rwa [hr.1, hs.1, hr.2, hs.2] at h
  choose idx pos hpos using h₁
  let f (m : M) := (C (idx m)).val.2 (pos m)
  have hf {i : ℕ} (r : Fin (p.1 + i)) : f ((C i).val.1 r) = (C i).val.2 r :=
    (agree (pos _) r).mp (hpos _)
  let e : M ≃ N := Equiv.ofBijective f ⟨fun x y h => by
    simpa only [hpos] using (agree (pos x) (pos y)).mpr h,
    fun n => by obtain ⟨i, r, rfl⟩ := h₂ n; exact ⟨_, hf r⟩⟩
  refine ⟨⟨e, fun g => isEmptyElim g, fun r x => ?_⟩, fun i => hf (i := 0) i⟩
  let k := Finset.univ.sup fun i => idx (x i)
  let h (i : Fin _) : idx (x i) ≤ k := Finset.le_sup (f := fun i => idx (x i)) (Finset.mem_univ i)
  let t (i : Fin _) := Fin.castLE (Nat.add_le_add_left (h i) _) (pos (x i))
  have ht i := P.chain_cast hp enum (h i) (pos (x i))
  have hm : (C k).val.1 ∘ t = x := funext fun i => (congrArg Prod.fst (ht i)).trans (hpos _)
  have hn : (C k).val.2 ∘ t = e.toFun ∘ x := funext fun i => congrArg Prod.snd (ht i)
  simpa only [AtomicIdx.holds, hm, hn] using (P.compatible _ (C k).property (.rel r t)).symm

theorem countable_toEquiv [Countable M] [Countable N] (P : PotentialIso L M N) :
    Nonempty (M ≃[L] N) :=
  let ⟨_, hp⟩ := P.nonempty
  let ⟨e, _⟩ := P.exists_equiv_of_mem hp
  ⟨e⟩

end PotentialIso

end Language

end FirstOrder
