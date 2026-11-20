/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.Orientation

/-! # Stable matchings, Galvin's theorem and the Dinitz problem -/

public section

namespace ListEdgeColouring

open Finset SimpleGraph Galvin Function

/-- Finite markets with strict preferences and incomplete lists admit stable matchings. -/
theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Injective (rm m))
    (hrw : ∀ w, Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  classical
  let S := (Set.toFinite {p : M × W | E p.1 p.2}).toFinset
  obtain ⟨K, hK, hi, ha⟩ := stable Prod.fst Prod.snd (uncurry rm) (uncurry (swap rw))
    (by grind [Injective, Prod.ext]) (by grind [Injective, Prod.ext]) S
  exact ⟨fun m w => (m, w) ∈ K, by grind [Incident, Pref, Prod.ext, Set.Finite.mem_toFinset]⟩

/-- A finite bipartite graph can be edge-coloured from lists of size at least its maximum degree. -/
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ #(lists e)) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨X, Y, hXY⟩ := IsBipartite.exists_isBipartiteWith hG
  choose e he hX hY using (show ∀ x : G.edgeSet, ∃ p : V × V,
      s(p.1, p.2) = x.val ∧ p.1 ∈ X ∧ p.2 ∈ Y by
    rintro ⟨⟨a, b⟩, h⟩
    rcases hXY.mem_of_adj (h : G.Adj a b) with h | h
    · exact ⟨(a, b), rfl, h⟩
    · exact ⟨(b, a), Sym2.eq_swap, h.2, h.1⟩)
  -- Complete the adjacency matrix to a regular one by filling the diagonal with deficits.
  let A (i j : V) : ℕ :=
    (if G.Adj i j then 1 else 0) + if i = j then G.maxDegree - G.degree i else 0
  have hr (i) : ∑ j, A i j = G.maxDegree := by
    simp [A, sum_add_distrib, ← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree,
      G.degree_le_maxDegree]
  have hs (i j) : A i j = A j i := by grind [G.adj_comm]
  obtain ⟨f, hf, hp⟩ := listsOfMatrix (Prod.fst ∘ e) (Prod.snd ∘ e)
    (by grind [Injective, Subtype.ext]) A hr (fun j => by simpa only [← hs j] using hr j)
    (by grind [mem_edgeSet]) lists hLists
  refine ⟨Coloring.mk f (fun {x y} h => hp x y ?_), hf⟩
  have := hXY.disjoint
  grind [Incident, lineGraph_adj_iff_exists]

/-- A square array with lists of at least `n` symbols per cell admits a Latin selection. -/
theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ #(lists i j)) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  -- The all-ones matrix represents the complete array of cells.
  obtain ⟨f, hf, hp⟩ := listsOfMatrix Prod.fst Prod.snd injective_id (d := n)
    (fun _ _ => 1) (by simp) (by simp) (by simp) (uncurry lists) (Prod.rec hLists)
  exact ⟨curry f, by grind [curry, Incident]⟩

end ListEdgeColouring
