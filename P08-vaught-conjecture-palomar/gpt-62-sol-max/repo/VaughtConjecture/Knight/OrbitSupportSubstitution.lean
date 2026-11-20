/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitPrefixSupport

@[expose] public section

namespace VaughtConjecture.Knight.OrbitPrefixSupport

open Transform Value ExtOrd

/-- Exact replacement composition, including the terminal offset. -/
theorem replace_replace (x : ExtOrd) (K i j : ℕ) :
    extVisibilityReplace (extVisibilityReplace x K i) K j =
      extVisibilityReplace x K (if i < K then j else i) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · simp only [extVisibilityReplace_bot]
  · simp only [extVisibilityReplace_top]
  · simp only [extVisibilityReplace_ofOrd, ofOrd_inj]
    rw [visReplace_eq (visibilityReplace a K i), limitPart_visibilityReplace,
      finitePart_visibilityReplace, visReplace_eq a K]
    split_ifs <;> simp_all

/-- A visible grid value is fixed at every replacement offset. -/
theorem replace_visible {K : ℕ} {x : ExtOrd} (hx : SelfVis K x) (i : ℕ) :
    extVisibilityReplace x K i = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact extVisibilityReplace_bot _ _
  · exact extVisibilityReplace_top _ _
  · exact extVisibilityReplace_of_le_finitePart (selfVis_ofOrd_iff.mp hx) i

theorem Supported.replace {X : Type*} {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd}
    {x : ExtOrd} (hx : Supported K G p x) (hG : ∀ z ∈ G, SelfVis K z)
    {j : ℕ} (hj : j ≤ K) : Supported K G p (extVisibilityReplace x K j) := by
  rcases hx with rfl | hx | ⟨d, i, hi, rfl⟩
  · tauto
  · rw [replace_visible (hG _ hx)]
    tauto
  · rw [replace_replace]
    exact Or.inr (Or.inr ⟨d, _, by split_ifs <;> assumption, rfl⟩)

/-- Flatten support through an entire intermediate physical vector. In particular
there is no assumption that its auxiliaries equal original-field readings. -/
theorem Supported.substitute {X Y : Type*} {K : ℕ} {G : Set ExtOrd}
    {p : X → ExtOrd} {q : Y → ExtOrd} {x : ExtOrd}
    (hx : Supported K G q x) (hG : ∀ z ∈ G, SelfVis K z)
    (hq : ∀ d, Supported K G p (q d)) : Supported K G p x := by
  rcases hx with hx | hx | ⟨d, i, hi, rfl⟩
  · exact Or.inl hx
  · tauto
  · exact (hq d).replace hG hi

end VaughtConjecture.Knight.OrbitPrefixSupport
