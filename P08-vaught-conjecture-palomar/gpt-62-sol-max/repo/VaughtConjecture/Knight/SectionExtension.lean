/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.VisibilityAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Bountifulness with the source index allowed to equal the target index. -/
private theorem extend_in_plan 
    {sem : Semantics D} (hb : sem.IsBountiful) {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan) (h : GradedLe CI BJ)
    {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hcompat : ∀ d : D.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d : D.below BJ, min (q' d) γ = min (q d) γ) ∧
      ∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d := by
  by_cases heq : CI = BJ
  · subst heq
    exact ⟨p, hp, fun d => (hcompat d).symm, fun _ => rfl⟩
  apply_rules

/-- Lowering a cutoff past no existing cell preserves its section. -/
def CellScheme.cutoffEquiv (J : Finset ι × ℕ) {k : ℕ} (h : ∀ d : D.below J, D.grade d.1 ≤ k) :
    D.below (J.1, min J.2 k) ≃ D.below J where
  toFun d := ⟨d.1, d.2.1, (le_min_iff.mp d.2.2).1⟩
  invFun d := ⟨d.1, d.2.1, le_min d.2.2 (h d)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem CellScheme.cutoff_respects {sem : Semantics D} (J : Finset ι × ℕ) {k : ℕ}
    (h : ∀ d : D.below J, D.grade d.1 ≤ k) (p : D.below (J.1, min J.2 k) → ExtOrd) :
    RespectsSemanticsBelow sem (J.1, min J.2 k) p ↔
      RespectsSemanticsBelow sem J (p ∘ (cutoffEquiv J h).symm) :=
  respects_iff_of_equiv (cutoffEquiv J h) (fun _ => rfl) (fun _ _ => Iff.rfl) (fun _ _ _ => rfl) p

/-- Bountiful extension at nominal grades: clipping grades at the scope size leaves
exactly the same lower sets, and an empty lower set imposes no prescription. -/
theorem Semantics.IsBountiful.extend {sem : Semantics D} (hb : sem.IsBountiful)
    {CI BJ : Finset ι × ℕ} (hCI : CI.1 ∈ D.plan) (hBJ : BJ.1 ∈ D.plan) (h : GradedLe CI BJ)
    {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : SelfVis BJ.2 γ)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow sem BJ r ∧ (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono h d) = p d := by
  have size (J : Finset ι × ℕ) (d : D.below J) : D.grade d.1 ≤ J.1.card :=
    (D.grade_le_card_scope d.1).trans (Finset.card_le_card d.2.1)
  let e := CellScheme.cutoffEquiv CI (size CI)
  let f := CellScheme.cutoffEquiv BJ (size BJ)
  by_cases hz : 0 < min CI.2 CI.1.card
  · have hc : GradedLe (CI.1, min CI.2 CI.1.card) (BJ.1, min BJ.2 BJ.1.card) :=
      ⟨h.1, min_le_min h.2 (Finset.card_le_card h.1)⟩
    have hp' : RespectsSemanticsBelow sem _ (p ∘ e) := (CellScheme.cutoff_respects CI (size CI) _).mpr hp
    have hq' : RespectsSemanticsBelow sem _ (q ∘ f) := (CellScheme.cutoff_respects BJ (size BJ) _).mpr hq
    obtain ⟨r, hr, hcap, hread⟩ := extend_in_plan hb (CI := (CI.1, min CI.2 CI.1.card)) (BJ := (BJ.1, min BJ.2 BJ.1.card))
      (Plan.mem_gradedPlan.mpr ⟨hCI, hz, min_le_right _ _⟩)
      (Plan.mem_gradedPlan.mpr ⟨hBJ, hz.trans_le hc.2, min_le_right _ _⟩)
      hc hp' hq' (hγ.mono (min_le_left _ _)) (fun d => hag (e d))
    exact ⟨r ∘ f.symm, (CellScheme.cutoff_respects BJ (size BJ) r).mp hr,
      fun d => hcap (f.symm d), fun d => hread (e.symm d)⟩
  · exact ⟨q, hq, fun _ => rfl,
      fun d => (hz ((D.grade_pos d.1).trans_le (e.symm d).2.2)).elim⟩

/-- Install a source section along the inverse of an equivalence of two faces. -/
theorem Semantics.IsBountiful.extend_inverse {sem : Semantics D} (hb : sem.IsBountiful)
    {ι' : Type*} [DecidableEq ι'] {A' : Finset ι'} {E : CellScheme A'} {sem' : Semantics E}
    {L : Finset ι' × ℕ} {I J : Finset ι × ℕ}
    (hI : I.1 ∈ D.plan) (hJ : J.1 ∈ D.plan) (h : GradedLe I J)
    (e : E.below L ≃ D.below I)
    (he : ∀ f, RespectsSemanticsBelow sem I f ↔ RespectsSemanticsBelow sem' L (f ∘ e))
    {q : D.below J → ExtOrd} {p : E.below L → ExtOrd} {γ : ExtOrd}
    (hq : RespectsSemanticsBelow sem J q) (hp : RespectsSemanticsBelow sem' L p)
    (hγ : SelfVis J.2 γ) (hag : ∀ d, min (q (CellScheme.below.mono h (e d))) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow sem J r ∧ (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono h (e d)) = p d := by
  have hf := (he (p ∘ e.symm)).mpr (by simpa [Function.comp_def] using hp)
  obtain ⟨r, hr, hc, hf⟩ := hb.extend hI hJ h hf hq hγ (fun d => by simpa using hag (e.symm d))
  exact ⟨r, hr, hc, fun d => by simpa using hf (e d)⟩

end VaughtConjecture.Knight
