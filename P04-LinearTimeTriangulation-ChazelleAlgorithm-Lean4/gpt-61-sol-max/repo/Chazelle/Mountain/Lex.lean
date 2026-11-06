module

public meta import Chazelle.Arithmetic

public import Chazelle.Spec
public import Mathlib.Tactic.Linarith

/-!
# The `(y, x)`-lexicographic order on points

Shared by the monotone-mountain algorithm (`Chazelle.Mountain.Stack`) and the trapezoid
diagonal construction (`Chazelle.Mountain.TrapDiagonal`).  Ties in height are broken by the
abscissa; this is the symbolic-perturbation-free order used throughout Phase 5.
-/

@[expose] public section

namespace Chazelle.Mountain

open Chazelle

/-- Strict `(y, x)`-lexicographic order: smaller height, or equal height and smaller abscissa. -/
def ylexLT (p q : Point) : Prop := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)

/-- Non-strict `(y, x)`-lexicographic order. -/
def ylexLE (p q : Point) : Prop := p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 ≤ q.1)

theorem ylexLE_refl (p : Point) : ylexLE p p := Or.inr ⟨rfl, le_rfl⟩

theorem ylexLE_of_ylexLT {p q : Point} (h : ylexLT p q) : ylexLE p q := by
  rcases h with h | ⟨h1, h2⟩
  all_goals core_grind

theorem ylexLT_trans {p q r : Point} (h₁ : ylexLT p q) (h₂ : ylexLT q r) : ylexLT p r := by
  core_grind

/-- `ylexLT` is asymmetric with respect to `ylexLE`. -/
theorem not_ylexLE_of_ylexLT {p q : Point} (h : ylexLT p q) : ¬ ylexLE q p := by
  rintro (h' | ⟨h1, h2⟩) <;> rcases h with h | ⟨h3, h4⟩ <;> linarith

theorem ylexLT_irrefl (p : Point) : ¬ ylexLT p p := by
  rintro (h | ⟨_, h⟩) <;> simp_all

theorem ylexLT_asymm {p q : Point} (h : ylexLT p q) : ¬ ylexLT q p := by
  rintro (h' | ⟨h1, h2⟩) <;> rcases h with h | ⟨h3, h4⟩ <;> linarith

/-- `ylexLT` is a strict total order. -/
theorem ylexLT_trichotomy (p q : Point) : ylexLT p q ∨ p = q ∨ ylexLT q p := by
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy p.1 q.1 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · grind
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem ylexLT_of_snd_lt {p q : Point} (h : p.2 < q.2) : ylexLT p q := Or.inl h

end Chazelle.Mountain

end
