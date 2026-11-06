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

/-! # Same-stage calibration from an attained stable marker and top-grade growth

The reviewer's assignment (2026-09-18, item 3): at the model's own stage, guard activation
cannot come from an ordinary label strictly below the cap (the marker is labelled `⊤`).  It
comes from the **stable labelling**: an attained marker `a` with ordinary label `⊤` and stable
value `α + j`, `0 < j`, together with top-grade growth, which supplies a cover with a
top-labelled full-scope cell of grade `N > j` — the cap — chosen **after** `j` and every other
offset are known.  In every coface the model realizes over that cover:

* the stable labelling is lawful on the same rows (`stableLiftRespects`), so the guard on the
  stable capped labelling reflects to the controller's row;
* the stable value of the marker is retained (`stableValue_mapCell`, along the cover and along
  the coface), and the stable values of the top-labelled grade-`N` cap and controller are at
  least `α + N > α + j` (`stable_ge_of_top`: at least `α` and `N`-visible), so the capped
  stable marker is `α + j` (`stable_guard_active`);
* the ordinary labelling reads back: the controller is labelled `⊤` (`exists_top_controller`),
  so `guarded_readback_at` transports the row's correctness to the ordinary labels, proper
  requests read exactly (`read_proper`) and, with the block-floor bound, top requests read
  literally `⊤` (`read_top_of_cutoffBound`).

**Explicit hypotheses, not asserted branches.**  The attained marker and top-grade growth are
hypotheses here: they are what the positive tight grade-defect branch supplies, and this module
does not claim them for the band-defect, zero-threshold, or bounded-top-grade branches, nor
does it use a threshold-vacuous infinity anchor.  The safe rows are supplied by the probe.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan Transform

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-! ## A top cap of high grade from top-grade growth -/

/-! ## Stable values of top-labelled cells of grade `N` -/

/-- The stage is its own limit part. -/
theorem limitPart_stage : limitPart α.1 = α.1 :=
  limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)

/-- A proper ordinal at least `α` (a limit) and `N`-visible is at least `α + N`. -/
theorem stage_add_le_of_selfVis {γ} (hγ : α.1 ≤ γ) {N}
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
theorem stable_ge_of_top (hM : R.IsModel) {m} {u} {q : S α.1 m}
    (hu : R.eval u = some q) {Θ} (hΘ : q.label Θ = ⊤) :
    ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue u q Θ := by
  have hα := le_stableValue_of_top (R := R) hu hΘ
  have hvis : SelfVis (q.scheme.scheme.grade Θ) (R.stableValue u q Θ) :=
    ((stableLiftRespects hM hu).orderly Θ).symm
  rcases ExtOrd.cases (R.stableValue u q Θ) with hb | ht | ⟨γ, hγ⟩
  · rw [hb] at hα; exact absurd hα (not_ofOrd_le_bot _)
  · rw [ht]; exact le_top
  · rw [hγ] at hα hvis ⊢
    exact ofOrd_le_ofOrd.mpr (stage_add_le_of_selfVis (ofOrd_le_ofOrd.mp hα) hvis)

/-- `α + j < α + N` for `j < N`. -/
theorem stage_add_lt {j N : ℕ} (h : j < N) : ofOrd (α.1 + j) < ofOrd (α.1 + N) :=
  ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr h) _)

/-! ## The controller and the stable guard in a realized coface -/

end VaughtConjecture.Knight
