/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalRatchet
public import VaughtConjecture.Knight.TopGradeDichotomy

/-! # Structural stable-spectrum bounds and characteristic-to-tail implication

These proofs use exact parent consistency and initial-segment covering. In particular,
`IsCharacteristicArity.isCoinitial_topGrade` does not invoke the converse or proper-label
cofinality. The zero-grade converse remains in `TopGradeStableSpectrum`.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- A positive top grade is attained by a full-scope `∞`-cell. -/
theorem exists_topCell_of_topGrade_pos (p : S α n) (hpos : 0 < p.topGrade) :
    ∃ Θ : Cell p.scheme.scheme, p.scheme.scheme.scope Θ = Finset.univ ∧
      p.scheme.scheme.grade Θ = p.topGrade ∧ p.label Θ = ⊤ := by
  have hne : p.topGrades.Nonempty := by
    by_contra hn
    have hempty : p.topGrades = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have : p.topGrade = 0 := by
      unfold topGrade
      rw [hempty, csSup_empty]
      rfl
    omega
  exact Nat.sSup_mem hne p.topGrades_bddAbove

end StageType

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- Every cell has a stable value (classical totality of the graph `HasStableValue`). -/
theorem exists_hasStableValue {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) : ∃ γ, R.HasStableValue t p Xi γ := by
  by_cases h : ∃ δ : ExtOrd, δ < ofOrd (α.1 + Ordinal.omega0) ∧ R.StabilizesTo t p Xi δ
  · obtain ⟨δ, hδ, hs⟩ := h
    exact ⟨δ, Or.inl ⟨hδ, hs⟩⟩
  · push Not at h
    exact ⟨⊤, Or.inr ⟨rfl, h⟩⟩

/-- A cell whose label is not `∞` stabilizes at its label. -/
theorem stabilizesTo_label_of_ne_top (x : R.LabelledExt) {Xi : Cell x.type.scheme.scheme}
    (hne : x.type.label Xi ≠ ⊤) (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) :
    R.StabilizesTo x.tuple x.type Xi (x.type.label Xi) := by
  intro m s
  obtain ⟨y, ⟨f, hf, hpq⟩, g, hg⟩ := exists_labelledExt_le hcons hcov x s
  refine ⟨y.arity, y.tuple, g, f, y.type, hpq, y.eval_eq, hg, hf, Or.inl ⟨?_, ?_⟩⟩
  · rw [label_mapCell hpq Xi]; exact hne
  · rw [label_mapCell hpq Xi]

/-! ### Stabilization on a tail of constant top grade -/
