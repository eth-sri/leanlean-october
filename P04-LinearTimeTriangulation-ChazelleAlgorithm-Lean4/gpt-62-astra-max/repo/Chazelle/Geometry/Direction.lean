module

public import Chazelle.Spec

@[expose] public section
namespace Chazelle

/-- A signed unit direction, as used to distinguish the two sides of an edge or ray. -/
abbrev UnitSign (σ : ℝ) : Prop := σ = 1 ∨ σ = -1

@[simp] theorem UnitSign.one : UnitSign 1 := Or.inl rfl

@[simp] theorem UnitSign.neg_one : UnitSign (-1) := Or.inr rfl

theorem UnitSign.neg {σ} (h : UnitSign σ) : UnitSign (-σ) := by
  rcases h with rfl | rfl <;> simp

theorem UnitSign.mul_self {σ} (h : UnitSign σ) : σ * σ = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem UnitSign.abs_eq {σ} (h : UnitSign σ) : |σ| = 1 := by
  rcases h with rfl | rfl <;> simp

theorem UnitSign.ne_zero {σ} (h : UnitSign σ) : σ ≠ 0 := by
  rcases h with rfl | rfl <;> norm_num

end Chazelle
