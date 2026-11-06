/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Kőnig's edge-colouring theorem

`lineGraph_colorable_of_colorable_two`: a finite bipartite graph has a proper edge colouring with
`Δ(G)` colours. The proof colours the edges one at a time with the partial proper edge colourings
`LeanPool.Vizing.PEC` of the Vizing development. To colour an uncoloured edge `xy`, take a colour
`a` free at `x` and a colour `b` free at `y` (both exist since `xy` is uncoloured and there are
`Δ(G)` colours). If neither colours `xy` directly, swap `a` and `b` on the `a/b` Kempe component
of `y`. Since `b` is free at `y`, the colours along any Kempe path ending at `y` alternate, the
edge farthest from `y` having colour `a` exactly when the path has odd length; and a Kempe path
from `y` to `x` has odd length because `G` is bipartite. So `x` is not in the component, `a` is
still free at `x`, and `a` becomes free at `y`.
-/

@[expose] public section

open SimpleGraph Finset

namespace Konig

open LeanPool.Vizing LeanPool.Vizing.PEC

variable {V : Type*} {C : Type*} {G : SimpleGraph V}

/-- At an endpoint of an uncoloured edge some colour is free, provided there are at least `Δ(G)`
colours. -/
theorem exists_free_of_none [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) : ∃ γ, c.IsFree x γ := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    grind
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ (G.neighborFinset x).erase y := by
    simp only [mem_erase, mem_neighborFinset]
    grind [c.col_adj]
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  rw [card_univ, Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 hadj),
    card_neighborFinset_eq_degree] at hcards
  have hdeg := G.degree_le_maxDegree x
  have hpos : 0 < G.degree x := G.degree_pos_iff_exists_adj x |>.2 ⟨y, hadj⟩
  omega

/-- **Alternation along a Kempe path.** If `b` is free at `y`, then on every path of the `a/b`
Kempe graph ending at `y`, the first edge has colour `a` if the length is odd and `b` if it is
even (and positive). -/
theorem col_snd_of_kempe_path (c : PEC G C) {a b : C} {y : V}
    (hy : c.IsFree y b) {u : V} (p : (c.kempeGraph a b).Walk u y) (hp : p.IsPath)
    (hlen : 0 < p.length) :
    c.col u p.snd = some (if p.length % 2 = 1 then a else b) := by
  induction p with
  | nil => simp at hlen
  | @cons u w y h r ih =>
    have hcol := h.2
    rw [Walk.snd_cons]
    rw [Walk.cons_isPath_iff] at hp
    rcases Nat.eq_zero_or_pos r.length with h0 | hpos
    · -- `r` is trivial: `w = y`
      have hwy : w = y := Walk.eq_of_length_eq_zero h0
      subst hwy
      rw [Walk.length_cons, h0, zero_add]
      rcases hcol with hcol | hcol <;> grind [c.col_symm, IsFree]
    · have hih := ih hy hp.1 hpos
      have hne : u ≠ r.snd := by
        intro he
        exact hp.2 (by rw [he]; exact r.getVert_mem_support 1)
      rw [Walk.length_cons]
      -- the colours of `w u` and `w r.snd` differ
      have hdiff : c.col w u ≠ c.col w r.snd := by grind [c.col_proper]
      rw [c.col_symm w u] at hdiff
      rcases Nat.mod_two_eq_zero_or_one r.length with hr | hr <;>
        simp [Nat.add_mod, hr] at hih ⊢
      all_goals rw [hih] at hdiff
      all_goals rcases hcol with hcol | hcol <;> simp_all

/-- **Kőnig's edge-colouring theorem.** The line graph of a finite bipartite graph is
`Δ(G)`-colourable. -/
theorem lineGraph_colorable_of_colorable_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Colorable 2) : G.lineGraph.Colorable G.maxDegree := by
  classical
  obtain ⟨s⟩ := h
  obtain ⟨c, hc⟩ : ∃ c : PEC G (Fin G.maxDegree), ∀ u v, G.Adj u v → c.col u v ≠ none := by
    suffices H : ∀ (k : ℕ) (c : PEC G (Fin G.maxDegree)), c.uncoloured.card = k →
        ∃ c' : PEC G (Fin G.maxDegree), ∀ u v, G.Adj u v → c'.col u v ≠ none by
      exact H _ (empty G _) rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro c hk
      by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
      · exact ⟨c, hall⟩
      push Not at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ : ∃ c' : PEC G (Fin G.maxDegree),
          Extends c c' ∧ c'.col x y ≠ none := by
        have hcard : G.maxDegree ≤ Fintype.card (Fin G.maxDegree) := by simp
        obtain ⟨a, ha⟩ := exists_free_of_none c hcard hadj hnone
        obtain ⟨b, hb⟩ := exists_free_of_none c hcard hadj.symm (by rw [c.col_symm]; exact hnone)
        by_cases hay : c.IsFree y a
        · exact ⟨c.setEdge a hadj ha hay, extends_setEdge c a hadj ha hay, by simp [setEdge]⟩
        have hxy : ¬ (c.kempeGraph a b).Reachable y x := by
          rintro ⟨q⟩
          set p := q.toPath.1.reverse
          have hp : p.IsPath := q.toPath.2.reverse
          have hsx : s x ≠ s y := s.valid hadj
          have hodd : p.length % 2 = 1 := by
            let sB : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv s
            have hsB : sB x ≠ sB y := fun h => hsx (finTwoEquiv.injective h)
            have hb : (¬ sB x ↔ sB y) := by
              cases hx : sB x <;> cases hy : sB y <;> simp_all
            have ho := sB.odd_length_iff_not_congr (p.mapLe (by
              rintro _ _ ⟨_, h | h⟩ <;> exact c.col_adj h))
            rw [Walk.length_mapLe] at ho
            exact Nat.odd_iff.mp (ho.mpr hb)
          have hlen : 0 < p.length := by omega
          have := col_snd_of_kempe_path c hb p hp hlen
          simp only [hodd, ↓reduceIte] at this
          exact ha _ this
        set c1 := c.kempeSwap a b y
        have ha1 : c1.IsFree x a := (isFree_kempeSwap_of_not_reachable c a b hxy a).2 ha
        have hay1 : c1.IsFree y a := by
          rw [isFree_kempeSwap_of_reachable c a b (Reachable.refl y) a, Equiv.swap_apply_left]
          exact hb
        refine ⟨c1.setEdge a hadj ha1 hay1, (extends_kempeSwap c a b y).trans
          (extends_setEdge c1 a hadj ha1 hay1), by simp [setEdge]⟩
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        exact ⟨hp.1, by grind [hext p.1 p.2]⟩
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        grind
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun h => hxy' (h hxy)⟩
      exact ih _ (by omega) c1 rfl
  exact ⟨c.lineGraphColoring hc⟩

end Konig
