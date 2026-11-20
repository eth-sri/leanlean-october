/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.FiniteMaster
public import VaughtConjecture.TypeTower.ChainUnion
public import Mathlib.Order.Ideal
public import Mathlib.Basic.Countable.Basic

@[expose] public section

namespace VaughtConjecture.TypeTower

universe u v w z z'

variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

/-- A rooted obligation, with service persistent under positive realization extension. -/
structure RootedTask (T : TypeTower.{u} Λ) (α : Λ) (M : Type w) where
  n : ℕ
  root : Fin n ↪ M
  base : T.Ty α n
  Served : T.Realization α M → Prop
  mono : ∀ {A B}, A.Extends B → Served A → Served B

namespace FiniteMasterScheduler

variable {S : Type z} (master : S → FiniteMaster T α M)

/-- Supported and either permanently rejected or already served. -/
def Resolved (r : RootedTask T α M) (s : S) : Prop :=
  (master s).Supported r.root ∧
    ((master s).chart.eval r.root ≠ some r.base ∨ r.Served (master s).chart)

variable
  (absorb : ∀ (s : S) (x : M), ∃ t, master s ≤ master t ∧ x ∈ Set.range (master t).tuple)

include absorb

/-- Finitely many absorptions decide all coordinates of a root, not its visibility. -/
theorem absorb_finset (s : S) (F : Finset M) :
    ∃ t, master s ≤ master t ∧ ∀ x ∈ F, x ∈ Set.range (master t).tuple := by
  classical
  induction F using Finset.induction_on with
  | empty => grind
  | @insert x F hx ih =>
    obtain ⟨t, hst, ht⟩ := ih
    obtain ⟨r, htr, hr⟩ := absorb t x
    refine ⟨r, hst.trans htr, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hr
    · exact htr.range_mono (ht y hy)

theorem resolve (s : S) (r : RootedTask T α M)
    (serve : ∀ s, (master s).chart.eval r.root = some r.base →
      ∃ t, master s ≤ master t ∧ r.Served (master t).chart) :
    ∃ t, master s ≤ master t ∧ Resolved master r t := by
  classical
  obtain ⟨t, hst, ht⟩ := absorb_finset master absorb s (Finset.univ.image r.root)
  have hsupp : (master t).Supported r.root :=
    ((master t).supported_iff r.root).mpr fun i => ht _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  by_cases hp : (master t).chart.eval r.root = some r.base
  · obtain ⟨q, htq, hq⟩ := serve t hp
    exact ⟨q, hst.trans htq, htq.supported hsupp, Or.inr hq⟩
  · exact ⟨t, hst, hsupp, Or.inl hp⟩

/-- Countable dense-set scheduling. Each request is resolved once; all points are absorbed. -/
theorem exists_chain {I : Type z'} [Countable I] [Countable M]
    (task : I → RootedTask T α M)
    (serve : ∀ (s : S) (i : I), (master s).chart.eval (task i).root = some (task i).base →
      ∃ t, master s ≤ master t ∧ (task i).Served (master t).chart)
    (seed : S) :
    ∃ A : ℕ → S, A 0 = seed ∧ Monotone (master ∘ A) ∧
      (∀ x, ∃ k, x ∈ Set.range (master (A k)).tuple) ∧
      ∀ i, ∃ k, Resolved master (task i) (A k) := by
  classical
  let : Preorder S := Preorder.lift master
  let : Encodable (I ⊕ M) := Encodable.ofCountable _
  let D : I ⊕ M → Order.Cofinal S
    | .inl i => ⟨{s | Resolved master (task i) s}, fun s => by
        obtain ⟨t, hst, ht⟩ := resolve master absorb s (task i) (fun s => serve s i)
        tauto⟩
    | .inr x => ⟨{s | x ∈ Set.range (master s).tuple}, fun s => by
        obtain ⟨t, hst, ht⟩ := absorb s x
        tauto⟩
  refine ⟨Order.sequenceOfCofinals seed D, rfl,
    Order.sequenceOfCofinals.monotone seed D, ?_, ?_⟩
  · intro x
    exact ⟨_, Order.sequenceOfCofinals.encode_mem seed D (.inr x)⟩
  · intro i
    exact ⟨_, Order.sequenceOfCofinals.encode_mem seed D (.inl i)⟩

omit absorb in
/-- The countable union of a master chain retains whole options on every old support. -/
theorem union_eval_supported {A : ℕ → S} (hA : Monotone (master ∘ A)) (k : ℕ)
    {n : ℕ} (t : Fin n ↪ M) (ht : (master (A k)).Supported t) :
    (Realization.chainUnion fun k => (master (A k)).chart).eval t =
      (master (A k)).chart.eval t := by
  have hchain : ∀ k, (master (A k)).chart.Extends (master (A (k + 1))).chart :=
    fun k => ((master (A k)).extends_iff _).mp (hA (Nat.le_succ k))
  have hc := Realization.chainUnion_consistent hchain (fun k => (master (A k)).consistent)
  obtain ⟨f, rfl⟩ := ht
  rw [(master (A k)).chart_factor]
  exact hc _ _ f (Realization.extends_chainUnion hchain k _ _ (master (A k)).chart_self)

/-- A realization from only finite absorption and finite service. Every defined label
comes from one finite state, permitting any hereditary invariant to pass to the union. -/
theorem exists_realization {I : Type z'} [Countable I] [Countable M]
    (task : I → RootedTask T α M)
    (serve : ∀ (s : S) (i : I), (master s).chart.eval (task i).root = some (task i).base →
      ∃ t, master s ≤ master t ∧ (task i).Served (master t).chart)
    (seed : S) :
    ∃ R : T.Realization α M, R.IsExactParentConsistent ∧ R.IsCovering ∧
      (master seed).chart.Extends R ∧
      (∀ i, R.eval (task i).root = some (task i).base → (task i).Served R) ∧
      ∀ {n} (t : Fin n ↪ M) (p : T.Ty α n), R.eval t = some p →
        ∃ s, (master s).chart.eval t = some p := by
  classical
  obtain ⟨A, hzero, hA, hpoints, htasks⟩ := exists_chain master absorb task serve seed
  have hchain : ∀ k, (master (A k)).chart.Extends (master (A (k + 1))).chart :=
    fun k => ((master (A k)).extends_iff _).mp (hA (Nat.le_succ k))
  refine ⟨Realization.chainUnion (fun k => (master (A k)).chart),
    Realization.chainUnion_consistent hchain (fun k => (master (A k)).consistent), ?_,
    hzero ▸ Realization.extends_chainUnion hchain 0, ?_, ?_⟩
  · intro n t
    choose ks hks using fun i : Fin n => hpoints (t i)
    let k := Finset.univ.sup ks
    have hs : (master (A k)).Supported t := ((master (A k)).supported_iff t).mpr fun i =>
      (hA (Finset.le_sup (Finset.mem_univ i))).range_mono (hks i)
    obtain ⟨f, hf⟩ := hs
    exact ⟨_, (master (A k)).tuple, f, hf, by
      rw [Realization.extends_chainUnion hchain k _ _ (master (A k)).chart_self]; rfl⟩
  · intro i hi
    obtain ⟨k, hs, hn | hserved⟩ := htasks i
    · exact False.elim (hn ((union_eval_supported master hA k _ hs).symm.trans hi))
    · exact (task i).mono (Realization.extends_chainUnion hchain k) hserved
  · intro n t p hp
    obtain ⟨k, hk⟩ := Realization.chainUnion_eval_some_exists hp
    tauto

end FiniteMasterScheduler

end VaughtConjecture.TypeTower
