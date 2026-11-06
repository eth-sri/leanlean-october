/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Kempe chains for partial edge colourings

Given a partial proper edge colouring `c` and two colours `a b`, the *Kempe graph* consists of
the edges coloured `a` or `b`.  Swapping the two colours on the connected component of a vertex
`x` produces another partial proper edge colouring, colouring exactly the same edges.
-/

@[expose] public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}

/-- The subgraph consisting of the edges coloured `a` or `b`. -/
def kempeGraph (c : PEC G C) (a b : C) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b)
  symm.symm := by
    rintro u v ⟨h1, h2⟩
    grind [c.col_symm]
  loopless := ⟨fun v h => h.1 rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj_of_col {c : PEC G C} {a b : C} {u v : V}
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Adj u v := by
  refine ⟨?_, h⟩
  rcases h with h | h <;> exact (c.col_adj h).ne

omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Reachability in the Kempe graph propagates along edges coloured `a` or `b`. -/
lemma reachable_of_col {c : PEC G C} {a b : C} {x u v : V}
    (hu : (c.kempeGraph a b).Reachable x u)
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Reachable x v :=
  hu.trans (kempeGraph_adj_of_col h).reachable

open Classical in
/-- The colour function after swapping `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwapFun (c : PEC G C) (a b : C) (x : V) : V → V → Option C :=
  fun u v => if (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    then (c.col u v).map (Equiv.swap a b) else c.col u v

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = (c.col u v).map (Equiv.swap a b) := by
  classical
  unfold kempeSwapFun
  by_cases hv : (c.kempeGraph a b).Reachable x v
  · rw [ite_eq_left ⟨hu, hv⟩]
  · rw [ite_eq_right (by grind)]
    cases h : c.col u v with
    | none => simp
    | some γ =>
      have hγ : γ ≠ a ∧ γ ≠ b := by
        constructor <;> rintro rfl <;> exact hv (reachable_of_col hu (by simp [h]))
      simp [Equiv.swap_apply_of_ne_of_ne hγ.1 hγ.2]

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_not_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : ¬ (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = c.col u v := by
  classical
  unfold kempeSwapFun
  rw [ite_eq_right (by tauto)]

omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_isSome (c : PEC G C) (a b : C) (x u v : V) :
    (c.kempeSwapFun a b x u v = none) ↔ (c.col u v = none) := by
  classical
  unfold kempeSwapFun
  split_ifs <;> simp

/-- Swapping the colours `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwap (c : PEC G C) (a b : C) (x : V) : PEC G C where
  col := c.kempeSwapFun a b x
  col_symm := by
    intro u v
    simp only [kempeSwapFun]
    split_ifs <;> grind [c.col_symm]
  col_adj := by
    intro u v γ h
    unfold kempeSwapFun at h
    split_ifs at h
    · cases hc : c.col u v <;> grind [c.col_adj]
    · exact c.col_adj h
  col_proper := by
    intro u v w γ h1 h2
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · simp only [kempeSwapFun_of_reachable c a b hu] at h1 h2
      have hc : c.col u v = c.col u w :=
        Option.map_injective (Equiv.swap a b).injective (h1.trans h2.symm)
      obtain ⟨δ, hcv⟩ := Option.ne_none_iff_exists'.mp
        (fun (hn : c.col u v = none) => by simp [hn] at h1)
      exact c.col_proper hcv (hc ▸ hcv)
    · simp only [kempeSwapFun_of_not_reachable c a b hu] at h1 h2
      exact c.col_proper h1 h2

omit [Fintype V] [DecidableEq V] in
lemma extends_kempeSwap (c : PEC G C) (a b : C) (x : V) : Extends c (c.kempeSwap a b x) := by
  intro u v h
  change c.kempeSwapFun a b x u v ≠ none
  rwa [ne_eq, kempeSwapFun_isSome]

omit [Fintype V] [DecidableEq V] in
/-- On the Kempe component the free colours get swapped. -/
lemma isFree_kempeSwap_of_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v (Equiv.swap a b γ) := by
  simp [IsFree, kempeSwap, kempeSwapFun_of_reachable c a b hv,
    Option.map_eq_some_iff, Equiv.swap_apply_eq_iff]

omit [Fintype V] [DecidableEq V] in
/-- Off the Kempe component the free colours are unchanged. -/
lemma isFree_kempeSwap_of_not_reachable (c : PEC G C) (a b : C) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v γ := by
  simp [IsFree, kempeSwap, kempeSwapFun_of_not_reachable c a b hv]

/-! ### Degrees in the Kempe graph -/

end PEC

end LeanPool.Vizing
