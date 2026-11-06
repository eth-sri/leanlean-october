import VaughtConjecture.Knight.VisibilityAlgebra
namespace VaughtConjecture.Knight
/-- Pointwise equality, including profiles transported along a map of cells. -/
abbrev PointwiseEq {α β : Sort*} (p q : α → β) : Prop := ∀ x, p x = q x
/-- A common upper bound for an entire profile. -/
abbrev BoundedBy {α : Sort*} {β : Type*} [LE β] (p : α → β) (M : β) : Prop := ∀ x, p x ≤ M
/-- Two profiles give the same receipt at a fixed cap. -/
abbrev CappedEq {α : Sort*} {β : Type*} [Min β] (p q : α → β) (γ : β) : Prop :=
  ∀ x, min (p x) γ = min (q x) γ
/-- Every member of a finite grid is visible at the specified grade. -/
abbrev VisibleOn (k : ℕ) (G : Finset ExtOrd) : Prop := ∀ z ∈ G, SelfVis k z
/-- No point of a profile has the excluded value. -/
abbrev AvoidsValue {α β : Sort*} (p : α → β) (v : β) : Prop := ∀ x, p x ≠ v
