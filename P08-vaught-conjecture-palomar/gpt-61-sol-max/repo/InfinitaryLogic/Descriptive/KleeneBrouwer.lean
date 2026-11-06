/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.List.Lex
import Mathlib.Data.ENat.Basic
import InfinitaryLogic.OrdinalUtil

/-!
# The Kleene–Brouwer order on a tree

Pure combinatorics on `Descriptive.tree ℕ` (prefix-closed sets of `List ℕ`), no codes: the raw
mathematics behind analytic boundedness for well-founded trees (issue #73).

* `HasInfiniteBranch T` is a **descending chain in strict extension** — a sequence of nodes each
  properly extending the previous — so "no infinite branch" is well-foundedness of `extBelow T`
  on the nose (`wellFounded_extBelow_iff_not_hasInfiniteBranch`), with no appeal to König.
* The Kleene–Brouwer order is the lexicographic order on `List ℕ∞` pulled back along
  `kbEncode x = x.map (↑) ++ [⊤]`: appending `⊤` makes every proper extension of a node *smaller*
  than the node, and among incomparable nodes the leftmost first difference decides.  Linearity is
  inherited (`kbLinearOrder`); `kbLT_of_extBelow` records that strict extension is a
  subrelation.
* `wellFounded_kbLT`: KB is well-founded on a well-founded tree.  Along a strictly KB-descending
  sequence every `k`-prefix stabilizes (`exists_stable_prefix`): once the `k`-prefix is fixed, the
  `k`-th KB head is antitone in `ℕ∞` and hence eventually constant, and it cannot stabilize at
  `⊤`, since the sequence would then repeat a list.  The stabilized prefixes form an infinite
  branch.
* `treeHeight T` is the strict supremum of the ranks of the nodes under strict extension, and
  `treeHeight_le_type` bounds it by the KB order type, through the monotonicity of
  `WellFounded.rank` in the relation (`InfinitaryLogic.rank_le_rank_of_imp`).
* Comparing and bounding heights: an infinite branch is a sequence with every initial segment in
  the tree (`hasInfiniteBranch_iff_exists_seq`); a homomorphism of strict extension, injective or
  not, bounds one height by another (`treeHeight_le_of_relHom`, through
  `InfinitaryLogic.rank_le_rank_of_relHom`); and a well-founded tree on `ℕ` has height below `ω₁`
  (`treeHeight_lt_omega1`), by regularity of `ℵ₁`.

The encoding lands in `ℕ∞`, which is defined as `WithTop ℕ`; the named type is what carries the
derived `WellFoundedLT` instance the chain condition uses.
-/

namespace KleeneBrouwer

open Descriptive

/-! ## Strict extension and branches -/

/-- `x` is a proper prefix of `y`. -/
def ProperPrefix (x y : List ℕ) := x <+: y ∧ x ≠ y

/-- The "descending" direction for well-foundedness: `y` sits below `x` when it properly
extends `x`. -/
def ExtBelow y x := ProperPrefix x y

/-- An infinite branch, as a descending chain in strict extension: a sequence of nodes of `T`
each properly extending the previous one. -/
def HasInfiniteBranch (T : tree ℕ) :=
  ∃ f : ℕ → List ℕ, (∀ n, f n ∈ T) ∧ ∀ n, ProperPrefix (f n) (f (n + 1))

/-- The strict-extension relation restricted to the nodes of `T`. -/
def extBelow (T : tree ℕ) (y x : ↥T) := ExtBelow (y : List ℕ) x

theorem ProperPrefix.trans {x y z} (h₁ : ProperPrefix x y) (h₂ : ProperPrefix y z) :
    ProperPrefix x z := by
  refine ⟨h₁.1.trans h₂.1, fun hxz => ?_⟩
  subst hxz
  exact h₂.2 (h₁.1.eq_of_length_le h₂.1.length_le).symm

instance (T : tree ℕ) : IsStrictOrder ↥T (extBelow T) where
  irrefl _ h := h.2 rfl
  trans _ _ _ h₁ h₂ := ProperPrefix.trans h₂ h₁

theorem wellFounded_extBelow_iff_not_hasInfiniteBranch T :
    WellFounded (extBelow T) ↔ ¬ HasInfiniteBranch T := by
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  constructor
  · rintro ⟨h⟩ ⟨f, hf, hstep⟩
    exact h (RelEmbedding.natGT (fun n => (⟨f n, hf n⟩)) fun n => hstep n)
  · intro h
    refine ⟨fun e => h ⟨fun n => (e n), fun n => (e n).2, fun n => ?_⟩⟩
    exact e.map_rel_iff.mpr (Nat.lt_succ_self n)

/-! ## The Kleene–Brouwer order, via lexicographic order on `WithTop ℕ` -/

/-! ## Proper extensions are KB-below -/

/-! ## KB is well-founded on a well-founded tree -/

/-- The height of the tree: the strict supremum of the ranks of its nodes under strict
extension. -/
noncomputable def treeHeight T [WellFounded (extBelow T)] :=
  ⨆ x : ↥T, Order.succ (WellFounded.rank (extBelow T) x)

/-! ## Branches as sequences -/

/-- **Branches are sequences**: `T` has an infinite branch iff some `z : ℕ → ℕ` has every finite
initial segment in `T`.  Forward, the `i`-th entry of the sequence is read off the `(i + 1)`-st
node of the branch, all of whose nodes are prefixes of one another. -/
theorem hasInfiniteBranch_iff_exists_seq T :
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
        have hlt  :=
          lt_of_le_of_ne (hstep n).1.length_le fun h ↦ (hstep n).2 ((hstep n).1.eq_of_length h)
        omega
    refine ⟨fun i ↦ (f (i + 1)).getD i 0, fun n ↦ ?_⟩
    have heq : List.ofFn (fun i : Fin n ↦ (f (i + 1)).getD i 0) = (f n).take n := by
      refine List.ext_getElem (by simp [hlen n]) fun i h₁ h₂ ↦ ?_
      have hi  := by simpa using h₁
      have hi'  := lt_of_lt_of_le (Nat.lt_succ_self i) (hlen (i + 1))
      simp  [  
        List.getElem?_eq_getElem hi', ]
      exact (hchain (i + 1) n hi).getElem hi'
    rw [heq]
    exact Tree.take_mem ⟨f n, hf n⟩
  · rintro ⟨z, hz⟩
    refine ⟨fun n ↦ List.ofFn (fun i : Fin n ↦ z i), hz, fun n ↦ ⟨?_, fun h ↦ ?_⟩⟩
    · grind [List.ofFn_succ_last]
    · simpa using congrArg List.length h

/-! ## Comparing heights -/

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
theorem treeHeight_lt_omega1 T [WellFounded (extBelow T)] :
    treeHeight T < Ordinal.omega 1 :=
  Ordinal.iSup_lt_omega_one fun x ↦
    (Cardinal.isSuccLimit_omega 1).succ_lt (rank_lt_omega1 (extBelow T) x)

