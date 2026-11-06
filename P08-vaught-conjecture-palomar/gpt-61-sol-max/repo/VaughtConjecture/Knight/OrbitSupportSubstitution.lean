/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # Support substitution at one fixed external threshold

The ordinary receiving renderer is composed across point scopes. Its intermediate
auxiliaries are genuine values, not additional original fields. Substitution
below proves that their replacement orbits remain supported by the original
fields and the same visible grid. The endpoint offset is treated separately:
replacing an endpoint again leaves that endpoint, not the new offset.
-/

namespace VaughtConjecture.Knight.OrbitPrefixSupport
open  Value ExtOrd

/-- Exact replacement composition, including the terminal offset. -/
theorem replace_replace x K i j :
    extVisibilityReplace (extVisibilityReplace x K i) K j =
      extVisibilityReplace x K (if i < K then j else i) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · simp  
    rw [visReplace_eq (visibilityReplace a K i), limitPart_visibilityReplace,
      finitePart_visibilityReplace, visReplace_eq a K]
    split_ifs <;> simp_all

/-- A visible grid value is fixed at every replacement offset. -/
theorem replace_visible {K} {x} (hx : SelfVis K x) i :
    extVisibilityReplace x K i = x := by exact?

theorem Supported.replace {X : Type*} {K} {G} {p : X → ExtOrd}
    {x} (hx : Supported K G p x) (hG : ∀ z ∈ G, SelfVis K z)
    {j} (hj : j ≤ K) : Supported K G p (extVisibilityReplace x K j) := by
  rcases hx with rfl | hx | ⟨d, i, hi, rfl⟩
  · solve_by_elim
  · rw [replace_visible (hG _ hx)]
    exact Or.inr (Or.inl hx)
  · rw [replace_replace]
    exact Or.inr (Or.inr ⟨d, _, by split_ifs <;> assumption, rfl⟩)

/-- Flatten support through an entire intermediate physical vector. In particular
there is no assumption that its auxiliaries equal original-field readings. -/
theorem Supported.substitute {X Y : Type*} {K} {G}
    {p : X → ExtOrd} {q : Y → ExtOrd} {x}
    (hx : Supported K G q x) (hG : ∀ z ∈ G, SelfVis K z)
    (hq : ∀ d, Supported K G p (q d)) : Supported K G p x := by
  rcases hx with hx | hx | ⟨d, i, hi, rfl⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact (hq d).replace hG hi

/-- Literal fields themselves have support, even if they are invisible. -/
theorem supported_field {X : Type*} (K : ℕ) (G : Set ExtOrd) (p : X → ExtOrd) (d : X) :
    Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with he | he | ⟨a, he⟩
  · exact Or.inl he
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [he, extVisibilityReplace_top]⟩)
  · refine Or.inr (Or.inr ⟨d, min (finitePart a) K, min_le_right _ _, ?_⟩)
    rw [he, extVisibilityReplace_ofOrd, ofOrd_inj, visibilityReplace]
    split_ifs with h
    · rw [min_eq_left h.le]
      exact (decomposition a).symm
    · rfl

