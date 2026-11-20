/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.CountedEncoding
public import VaughtConjecture.Knight.StableLiftCore
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.FiniteOffset

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan Transform

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- The stage is its own limit part. -/
theorem limitPart_stage : limitPart α.1 = α.1 :=
  limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)

/-- A proper ordinal at least `α` (a limit) and `N`-visible is at least `α + N`. -/
theorem stage_add_le_of_selfVis {γ : Ordinal.{0}} (hγ : α.1 ≤ γ) {N : ℕ}
    (hN : SelfVis N (ofOrd γ)) : α.1 + N ≤ γ := by
  rw [selfVis_ofOrd_iff] at hN
  have h1 : α.1 ≤ limitPart γ := by
    have := limitPart_mono hγ
    rwa [limitPart_stage] at this
  calc α.1 + (N : Ordinal.{0}) ≤ limitPart γ + (N : Ordinal.{0}) := add_le_add_left h1 _
    _ ≤ limitPart γ + finitePart γ := add_le_add_right (Nat.cast_le.mpr hN) _
    _ = γ := limitPart_add_finitePart γ

/-- **Stable values of top-labelled cells**: at a cell of grade `N` labelled `⊤`, the stable
value is `⊤` or a proper ordinal at least `α + N` (at least `α`, and `N`-visible by lawfulness
of the stable labelling). -/
theorem stable_ge_of_top (hM : R.IsModel) {m : ℕ} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {Θ : Cell q.scheme.scheme} (hΘ : q.label Θ = ⊤) :
    ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue u q Θ := by
  have hα := le_stableValue_of_top (R := R) hu hΘ
  have hvis : SelfVis (q.scheme.scheme.grade Θ) (R.stableValue u q Θ) :=
    ((stableLiftRespects hM hu).orderly Θ).symm
  rcases ExtOrd.cases (R.stableValue u q Θ) with hb | ht | ⟨γ, hγ⟩
  · aesop
  · simp_all
  · rw [hγ] at hα hvis ⊢
    exact ofOrd_le_ofOrd.mpr (stage_add_le_of_selfVis (ofOrd_le_ofOrd.mp hα) hvis)

/-- `α + j < α + N` for `j < N`. -/
theorem stage_add_lt {j N : ℕ} (h : j < N) : ofOrd (α.1 + j) < ofOrd (α.1 + N) :=
  by simp_all

end VaughtConjecture.Knight
