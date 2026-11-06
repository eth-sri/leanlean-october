/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Vizing's theorem, upper bound

Iterating the extension step colours all edges, giving a proper edge colouring with
`Δ + 1` colours; equivalently, the line graph is `(Δ + 1)`-colourable.
-/

@[expose] public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

/-- The colouring that colours nothing. -/
def empty (G : SimpleGraph V) (C : Type*) : PEC G C where
  col := fun _ _ => none
  col_symm := fun _ _ => rfl
  col_adj := by intro u v γ h; exact absurd h (by simp)
  col_proper := by intro u v w γ h; exact absurd h (by simp)

/-- The set of (ordered) uncoloured edges. -/
noncomputable def uncoloured [DecidableRel G.Adj] (c : PEC G C) : Finset (V × V) :=
  {p ∈ (Finset.univ : Finset (V × V)) | G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none}

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma mem_uncoloured [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by
  classical
  simp [uncoloured]

/-! ### From total colourings to colourings of the line graph -/

/-- The optional colour on an unordered pair. -/
def edgeOption (c : PEC G C) (e : Sym2 V) : Option C :=
  Sym2.lift ⟨c.col, c.col_symm⟩ e

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
@[simp] lemma edgeOption_mk (c : PEC G C) (u v : V) :
    c.edgeOption s(u, v) = c.col u v := rfl

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
/-- Totality supplies a colour on every actual edge, even for an empty palette. -/
lemma edgeOption_ne_none (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 ≠ none := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact htot u v he

/-- The colour of an actual edge, extracted from totality without a default colour. -/
noncomputable def edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) : C :=
  Classical.choose (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma edgeOption_eq_some_edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 = some (c.edgeColor htot e) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))

/-- A total proper partial colouring gives a colouring of the line graph. -/
noncomputable def lineGraphColoring (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) : (G.lineGraph).Coloring C :=
  Coloring.mk (c.edgeColor htot) (by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hv₁, hv₂⟩ := hadj
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
    intro hcol
    have hγ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, u), he₁⟩
    have hδ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, w), he₂⟩
    simp only [edgeOption_mk] at hγ hδ
    rw [← hcol] at hδ
    have huw : u = w := c.col_proper hγ hδ
    subst huw
    exact hne (Subtype.ext rfl))

end PEC

end LeanPool.Vizing

namespace SimpleGraph

end SimpleGraph
