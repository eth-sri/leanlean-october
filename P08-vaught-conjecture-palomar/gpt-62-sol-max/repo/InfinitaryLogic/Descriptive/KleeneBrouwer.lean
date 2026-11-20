/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.List.Lex
public import Mathlib.Data.ENat.Basic
public import InfinitaryLogic.OrdinalUtil

@[expose] public section

namespace KleeneBrouwer

open Descriptive

/-- `x` is a proper prefix of `y`. -/
def ProperPrefix (x y : List ℕ) : Prop := x <+: y ∧ x ≠ y

/-- The "descending" direction for well-foundedness: `y` sits below `x` when it properly
extends `x`. -/
def ExtBelow (y x : List ℕ) : Prop := ProperPrefix x y

/-- An infinite branch, as a descending chain in strict extension: a sequence of nodes of `T`
each properly extending the previous one. -/
def HasInfiniteBranch (T : tree ℕ) : Prop :=
  ∃ f : ℕ → List ℕ, (∀ n, f n ∈ T) ∧ ∀ n, ProperPrefix (f n) (f (n + 1))

/-- The strict-extension relation restricted to the nodes of `T`. -/
def extBelow (T : tree ℕ) (y x : ↥T) : Prop := ExtBelow (y : List ℕ) x

theorem ProperPrefix.trans {x y z : List ℕ} (h₁ : ProperPrefix x y) (h₂ : ProperPrefix y z) :
    ProperPrefix x z := by
  refine ⟨h₁.1.trans h₂.1, fun hxz => ?_⟩
  subst hxz
  exact h₂.2 (h₁.1.eq_of_length_le h₂.1.length_le).symm

instance (T : tree ℕ) : IsStrictOrder ↥T (extBelow T) where
  irrefl _ h := h.2 rfl
  trans _ _ _ h₁ h₂ := ProperPrefix.trans h₂ h₁

theorem wellFounded_extBelow_iff_not_hasInfiniteBranch (T : tree ℕ) :
    WellFounded (extBelow T) ↔ ¬ HasInfiniteBranch T := by
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  constructor
  · rintro ⟨h⟩ ⟨f, hf, hstep⟩
    exact h (RelEmbedding.natGT (fun n => (⟨f n, hf n⟩ : ↥T)) fun n => hstep n)
  · intro h
    refine ⟨fun e => h ⟨fun n => (e n : List ℕ), by simp, fun n => ?_⟩⟩
    exact e.map_rel_iff.mpr (Nat.lt_succ_self n)

/-- The height of the tree: the strict supremum of the ranks of its nodes under strict
extension. -/
noncomputable def treeHeight (T : tree ℕ) [WellFounded (extBelow T)] : Ordinal :=
  ⨆ x : ↥T, Order.succ (WellFounded.rank (extBelow T) x)

/-- **Branches are sequences**: `T` has an infinite branch iff some `z : ℕ → ℕ` has every finite
initial segment in `T`.  Forward, the `i`-th entry of the sequence is read off the `(i + 1)`-st
node of the branch, all of whose nodes are prefixes of one another. -/
theorem hasInfiniteBranch_iff_exists_seq (T : tree ℕ) :
    HasInfiniteBranch T ↔ ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ T := by
  constructor
  · rintro ⟨f, hf, hstep⟩
    have hchain : ∀ m n, m ≤ n → f m <+: f n := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact List.prefix_refl _
      | succ n _ ih => exact ih.trans (hstep n).1
    have hlen : ∀ n, n ≤ (f n).length := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        have hlt : (f n).length < (f (n + 1)).length :=
          lt_of_le_of_ne (hstep n).1.length_le fun h ↦ (hstep n).2 ((hstep n).1.eq_of_length h)
        omega
    refine ⟨fun i ↦ (f (i + 1)).getD i 0, fun n ↦ ?_⟩
    have heq : List.ofFn (fun i : Fin n ↦ (f (i + 1)).getD i 0) = (f n).take n := by
      refine List.ext_getElem (by simp [hlen n]) fun i h₁ h₂ ↦ ?_
      have hi : i < n := by simpa using h₁
      have hi' : i < (f (i + 1)).length := by tauto
      simp only [List.getElem_ofFn, List.getElem_take, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi', Option.getD_some]
      exact (hchain (i + 1) n hi).getElem hi'
    rw [heq]
    exact Tree.take_mem ⟨f n, hf n⟩
  · rintro ⟨z, hz⟩
    refine ⟨fun n ↦ List.ofFn (fun i : Fin n ↦ z i), hz, fun n ↦ ⟨?_, fun h ↦ ?_⟩⟩
    · simp only [List.ofFn_succ_last]
      exact List.prefix_append _ _
    · simpa using congrArg List.length h

/-- **Rank domination between trees**: a homomorphism of strict extension from `S` to `T`
bounds the height of `S` by the height of `T`.  Not necessarily injective: only the extension
steps are transported. -/
theorem treeHeight_le_of_relHom {S T : tree ℕ} [WellFounded (extBelow S)]
    [WellFounded (extBelow T)] (f : extBelow S →r extBelow T) :
    treeHeight S ≤ treeHeight T :=
  Ordinal.iSup_le fun x ↦ (Order.succ_le_succ (InfinitaryLogic.rank_le_rank_of_relHom f x)).trans
    (Ordinal.le_iSup (fun y : ↥T ↦ Order.succ (WellFounded.rank (extBelow T) y)) (f x))

/-- Ranks in a well-founded relation on a countable type are countable. -/
private theorem rank_lt_omega1 {α : Type} [Countable α] (r : α → α → Prop) [WellFounded r]
    (a : α) : WellFounded.rank r a < Ordinal.omega 1 := by
  induction a using WellFounded.induction' r with
  | ind a ih =>
    rw [WellFounded.rank_eq r]
    exact Ordinal.iSup_lt_omega_one fun b ↦ (Cardinal.isSuccLimit_omega 1).succ_lt (ih b b.2)

/-- **A well-founded tree on `ℕ` has countable height**: it has countably many nodes, each of
countable rank, and `ℵ₁` is regular. -/
theorem treeHeight_lt_omega1 (T : tree ℕ) [WellFounded (extBelow T)] :
    treeHeight T < Ordinal.omega 1 :=
  Ordinal.iSup_lt_omega_one fun x ↦
    (Cardinal.isSuccLimit_omega 1).succ_lt (rank_lt_omega1 (extBelow T) x)

end KleeneBrouwer
