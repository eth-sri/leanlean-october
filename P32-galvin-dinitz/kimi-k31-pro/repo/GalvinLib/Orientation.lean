/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.GaleShapley
public import GalvinLib.Kernel

/-!
# Galvin's orientation of the line graph of a bipartite graph

Fix a `2`-colouring `c` of `G` (sides `0` and `1`) and a proper edge colouring `φ` with colours
in `Fin Δ`. Every edge `e` has an endpoint `endA c e` on side `0` and `endB c e` on side `1`. For
edges sharing their side-`0` endpoint, the arc goes from the larger to the smaller colour; for
edges sharing their side-`1` endpoint, from the smaller to the larger colour. Every out-degree is
less than `Δ`, and every set of edges has a kernel (a stable matching).
-/

@[expose] public section

namespace Galvin

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem exists_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    ∃ a b : V, (e : Sym2 V) = s(a, b) ∧ c a = 0 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ x y =>
  have hne : c x ≠ c y := c.valid he
  by_cases hx : c x = 0
  · exact ⟨x, y, rfl, hx⟩
  · refine ⟨y, x, Sym2.eq_swap, ?_⟩
    revert hne hx
    generalize c x = i
    generalize c y = j
    revert i j
    decide

/-- The endpoint of an edge on side `0`. -/
noncomputable def endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose

/-- The endpoint of an edge on side `1`. -/
noncomputable def endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose_spec.choose

theorem edge_eq_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    (e : Sym2 V) = s(endA c e, endB c e) :=
  (exists_ends c e).choose_spec.choose_spec.1

theorem colour_endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endA c e) = 0 :=
  (exists_ends c e).choose_spec.choose_spec.2

theorem adj_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) : G.Adj (endA c e) (endB c e) := by
  simpa only [edge_eq_ends c e, SimpleGraph.mem_edgeSet] using e.2

theorem colour_endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endB c e) = 1 := by
  exact Fin.eq_one_of_ne_zero _ fun h =>
    c.valid (adj_ends c e) ((colour_endA c e).trans h.symm)

theorem eq_of_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} (hA : endA c e = endA c f)
    (hB : endB c e = endB c f) : e = f := by
  apply Subtype.ext
  rw [edge_eq_ends c e, edge_eq_ends c f, hA, hB]

theorem mem_edge_iff (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = endA c e ∨ v = endB c e := by
  rw [edge_eq_ends c e, Sym2.mem_iff]

theorem lineGraph_adj_iff_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (endA c e = endA c f ∨ endB c e = endB c f) := by
  rw [lineGraph_adj_iff_exists]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v, hve, hvf⟩
    rw [mem_edge_iff c] at hve hvf
    rcases hve with rfl | rfl <;> rcases hvf with h | h <;> grind [colour_endA, colour_endB]
  · rintro (h | h)
    · exact ⟨endA c e, (mem_edge_iff c e _).2 (Or.inl rfl), (mem_edge_iff c f _).2 (Or.inl h)⟩
    · exact ⟨endB c e, (mem_edge_iff c e _).2 (Or.inr rfl), (mem_edge_iff c f _).2 (Or.inr h)⟩

theorem eq_of_colour_eq (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {e f : G.edgeSet} (hφ : φ e = φ f) (h : endA c e = endA c f ∨ endB c e = endB c f) :
    e = f := by
  by_contra hne
  exact φ.valid ((lineGraph_adj_iff_ends c).2 ⟨hne, h⟩) hφ

/-- Galvin's orientation of the line graph. -/
def arc (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (e f : G.edgeSet) : Prop :=
  (endA c e = endA c f ∧ φ f < φ e) ∨ (endB c e = endB c f ∧ φ e < φ f)

/-- Every out-degree of Galvin's orientation is less than `Δ`. -/
theorem card_arc_lt [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by
  classical
  have hsub : univ.filter (arc c φ e) ⊆
      univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e) ∪
        univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f) := by
    intro f hf
    simpa only [arc, mem_filter, mem_univ, true_and, mem_union] using hf
  have h1 : (univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e)).card ≤
      (Iio (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (by simp [Set.MapsTo]) (fun f hf f' hf' h => ?_)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
    exact eq_of_colour_eq c φ h (Or.inl (hf.1.symm.trans hf'.1))
  have h2 : (univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f)).card ≤
      (Ioi (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (by simp [Set.MapsTo]) (fun f hf f' hf' h => ?_)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
    exact eq_of_colour_eq c φ h (Or.inr (hf.1.symm.trans hf'.1))
  rw [Fin.card_Iio] at h1
  rw [Fin.card_Ioi] at h2
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h4 := (φ e).isLt
  omega

/-- Rank of `w` for the man `m`: the colour of the edge `mw` (smaller colours preferred). -/
noncomputable def rankA (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (m w : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then (φ h.choose : ℕ) else Δ + idx w

/-- Rank of `m` for the woman `w`: `Δ` minus the colour of the edge `mw` (larger colours
preferred). -/
noncomputable def rankB (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (w m : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then Δ - (φ h.choose : ℕ)
  else Δ + 1 + idx m

/-- Every set of edges has a kernel for Galvin's orientation: a stable matching. -/
theorem hasKernels_arc [Finite V] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) : HasKernels G.lineGraph (arc c φ) := by
  classical
  intro S
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin V
  let idx : V → ℕ := fun v => (eqv v : ℕ)
  have hidx : Function.Injective idx := fun a b h => eqv.injective (Fin.ext h)
  unfold Function.Injective at hidx
  let E : V → V → Prop := fun m w => ∃ e ∈ S, endA c e = m ∧ endB c e = w
  have rAe (e : G.edgeSet) : rankA c φ idx (endA c e) (endB c e) = φ e := by
    unfold rankA
    split_ifs with h <;> grind [eq_of_ends]
  have rBe (e : G.edgeSet) : rankB c φ idx (endB c e) (endA c e) = Δ - φ e := by
    unfold rankB
    split_ifs with h <;> grind [eq_of_ends]
  have rAi (m : V) : Function.Injective (rankA c φ idx m) := by
    intro w w' hww
    unfold rankA at hww
    split_ifs at hww with h h' <;> grind [eq_of_colour_eq]
  have rBi (w : V) : Function.Injective (rankB c φ idx w) := by
    intro m m' hmm
    unfold rankB at hmm
    split_ifs at hmm with h h' <;> grind [eq_of_colour_eq]
  obtain ⟨μ, hsub, hm, hw, hst⟩ := exists_isStable E (rankA c φ idx) (rankB c φ idx) rAi rBi
  refine ⟨S.filter (fun e => μ (endA c e) (endB c e)), filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_filter] at hx hy
    rw [lineGraph_adj_iff_ends c] at hxy
    grind [eq_of_ends]
  · intro x hxS hxK
    simp only [mem_filter, hxS, true_and] at hxK
    rcases hst _ _ ⟨x, hxS, rfl, rfl⟩ hxK with ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      refine ⟨f, mem_filter.2 ⟨hfS, ?_⟩, Or.inl ⟨hfA.symm, ?_⟩⟩ <;> grind
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      refine ⟨f, mem_filter.2 ⟨hfS, ?_⟩, Or.inr ⟨hfB.symm, ?_⟩⟩ <;> grind

end Galvin
