/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Literal single-face restoration from a predecessor lifting clause

The lower ambient is constructed by restricting the capped lawful section.
Lower values need not be equal, bounded by the owner, visible upstairs, or
proper. The unchanged upper tail is bounded by the restoration cap.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SingleFaceTailRestoration
open Transform Value ExtOrd GradeTailRestoration CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) {C B : Finset ι} {j : ℕ} (hCB : C ⊆ B)

/-- Internal restoration producer. Only the lower lifting clause is used;
no lifting property of the upper output or scalar unsaturation is assumed. -/
theorem exists_restore
    (hlift : CappedLift sem (show GradedLe (C, j) (B, j) from ⟨hCB, le_rfl⟩))
    {p}
    (hp : sem.Lawful p)
    {u}
    (hu : sem.Lawful u)
    {M} (hM : SelfVis (j + 1) M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = min (p e) M)
    (hhigh : ∀ e : D.below (C, j + 1), D.grade e.1 = j + 1 → p e ≤ M) :
    ∃ r,
      sem.Lawful r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = p e) ∧
      CappedEq r u M ∧
      ∀ d, j < D.grade d.1 → r d ≤ M := by
  let v := fun d => min (u d) M
  have hv := hu.cap hM
  let hC : GradedLe (C, j) (C, j + 1) := ⟨Finset.Subset.refl _, Nat.le_succ j⟩
  let hB : GradedLe (B, j) (B, j + 1) := ⟨Finset.Subset.refl _, Nat.le_succ j⟩
  let hl : GradedLe (C, j) (B, j) := ⟨hCB, le_rfl⟩
  let pl := p ∘ CellScheme.below.mono hC
  let ql := v ∘ CellScheme.below.mono hB
  have hag (d : D.below (C, j)) :
      min (ql (CellScheme.below.mono hl d)) M = min (pl d) M := by
    change min (min (u _) M) M = min (p _) M
    have hh := congrArg (fun z => min (min z M) M) (hread (CellScheme.below.mono hC d))
    exact hh.trans (by simp)
  obtain ⟨w, hw, hwcap, hwread⟩ := hlift pl ql M (hp.mono hC) (hv.mono hB)
    (hM.mono (Nat.le_succ j)) hag
  refine ⟨splice v w, splice_respects (Nat.le_succ j) hv hw
    (fun _ _ => min_le_right _ _) hwcap, ?_, ?_, ?_⟩
  · intro e
    by_cases he : D.grade e.1 ≤ j
    · rw [splice_low v w _ he]
      exact hwread ⟨e.1, e.2.1, he⟩
    · rw [splice_high v w _ he]
      change min (u _) M = p e
      have hg : D.grade e.1 = j + 1 := by
        have hb : D.grade e.1 ≤ j + 1 := e.2.2
        omega
      simp_all
  · intro d
    exact (splice_cap (Nat.le_succ j) hwcap d).trans
      (show min (min (u d) M) M = min (u d) M by simp)
  · intro d hd
    rw [splice_high v w d (not_le.mpr hd)]
    grind

/-- Inactive upper prescriptions lift directly from an arbitrary lawful
ambient. This includes bottom and top caps and an empty upper-owner set. -/
theorem exists_inactive
    (hlift : CappedLift sem (show GradedLe (C, j) (B, j) from ⟨hCB, le_rfl⟩))
    {p}
    (hp : sem.Lawful p)
    {q}
    (hq : sem.Lawful q)
    {γ} (hγ : SelfVis (j + 1) γ)
    (hag : CappedEq (q ∘ CellScheme.below.mono (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩)) p γ)
    (hhigh : ∀ e : D.below (C, j + 1), D.grade e.1 = j + 1 → p e ≤ γ) :
    ∃ r,
      sem.Lawful r ∧
      CappedEq r q γ ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = p e := by
  obtain ⟨r, hr, hread, hcap, _⟩ := exists_restore sem hCB hlift hp (hq.cap hγ) hγ hag hhigh
  grind

end
end VaughtConjecture.Knight.SingleFaceTailRestoration
