/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto

/-!
# Partial edge colourings

Basic definitions and extension operations for the fan-and-Kempe proof of Vizing's theorem.
-/

@[expose] public section

section
/-!
# Partial edge colourings

Basic framework for Vizing's theorem: a *partial proper edge colouring* of a simple graph `G`
is a symmetric partial function on pairs of vertices, defined only on edges, such that two
distinct edges sharing a vertex never receive the same colour.
-/

open SimpleGraph Finset

namespace LeanPool.Vizing

variable {V : Type*} [DecidableEq V] {C : Type*}

/-- A partial proper edge colouring of `G` with colours in `C`. -/
structure PEC (G : SimpleGraph V) (C : Type*) where
  /-- The colour of the edge `u v`, if it is coloured. -/
  col : V → V → Option C
  col_symm : ∀ u v, col u v = col v u
  col_adj : ∀ {u v γ}, col u v = some γ → G.Adj u v
  col_proper : ∀ {u v w γ}, col u v = some γ → col u w = some γ → v = w

namespace PEC

variable {G : SimpleGraph V}

/-- A colour is free at a vertex if no edge at that vertex carries it. -/
def IsFree (c : PEC G C) (v : V) (γ : C) : Prop := ∀ u, c.col v u ≠ some γ

/-- `c'` colours at least the edges that `c` colours. -/
def Extends (c c' : PEC G C) : Prop := ∀ u v, c.col u v ≠ none → c'.col u v ≠ none

omit [DecidableEq V] in
lemma Extends.trans {c₁ c₂ c₃ : PEC G C} (h₁ : Extends c₁ c₂) (h₂ : Extends c₂ c₃) :
    Extends c₁ c₃ := fun u v h => h₂ u v (h₁ u v h)

/-! ### Updating a single edge -/

/-- Change the colour of the edge `x y` (in both directions) to `o`. -/
def updFun (f : V → V → Option C) (x y : V) (o : Option C) : V → V → Option C :=
  fun u v => if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then o else f u v

@[simp] lemma updFun_left {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o x y = o := ite_eq_left (Or.inl ⟨rfl, rfl⟩)

/-- Colour the (possibly already coloured) edge `x y` with a colour free at both endpoints. -/
def setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : PEC G C where
  col := updFun c.col x y (some γ)
  col_symm := by
    intro u v
    simp only [updFun]
    split_ifs <;> grind [c.col_symm]
  col_adj := by
    intro u v δ h
    simp only [updFun] at h
    split_ifs at h with hc <;> grind [hadj.symm, c.col_adj]
  col_proper := by
    intro u v w δ h1 h2
    simp only [updFun] at h1 h2
    split_ifs at h1 h2 <;> grind [c.col_proper, IsFree]

lemma extends_setEdge (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : Extends c (c.setEdge γ hadj hx hy) := by
  intro u v h
  simp only [setEdge, updFun]
  split <;> simp_all

end PEC

end LeanPool.Vizing
end
