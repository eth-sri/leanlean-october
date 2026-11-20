/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NormalForm
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.CappedLifting

@[expose] public section

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd

open VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {I J U V : Finset ι × ℕ}

/-- Clamp the overlap's nominal grade to its actual cardinality before
invoking an old face's graded-plan bountifulness clause. -/
def overlapTarget (U V : Finset ι × ℕ) : Finset ι × ℕ :=
  (U.1 ∩ V.1, min (min U.2 V.2) (U.1 ∩ V.1).card)

theorem target_le_left : GradedLe (overlapTarget U V) U :=
  ⟨Finset.inter_subset_left, (min_le_left _ _).trans (min_le_left _ _)⟩

theorem target_le_right : GradedLe (overlapTarget U V) V :=
  ⟨Finset.inter_subset_right, (min_le_left _ _).trans (min_le_right _ _)⟩

/-- Clamping drops no occurrence, including any high-grade auxiliary. -/
theorem below_target_iff (d : Cell D) :
    GradedLe (D.cell d) (overlapTarget U V) ↔
      GradedLe (D.cell d) U ∧ GradedLe (D.cell d) V := by
  constructor
  · intro h
    exact ⟨h.trans target_le_left, h.trans target_le_right⟩
  · rintro ⟨hu, hv⟩
    have hs : D.scope d ⊆ U.1 ∩ V.1 := Finset.subset_inter hu.1 hv.1
    exact ⟨hs, le_min (le_min hu.2 hv.2)
      ((D.grade_le_card_scope d).trans (Finset.card_le_card hs))⟩

theorem target_mem_gradedPlan (hR : U.1 ∩ V.1 ∈ D.plan)
    (hU : 0 < U.2) (hV : 0 < V.2) (hne : (U.1 ∩ V.1).Nonempty) :
    overlapTarget U V ∈ Plan.gradedPlan D.plan :=
  Plan.mem_gradedPlan.mpr ⟨hR,
    lt_min (lt_min hU hV) (Finset.card_pos.mpr hne), min_le_right _ _⟩

/-- Disjoint old faces have an empty actual overlap domain, regardless of
their nominal grades. `lift_empty` handles the second lifting step. -/
theorem target_empty (he : U.1 ∩ V.1 = ∅) : IsEmpty (D.below (overlapTarget U V)) := by
  refine ⟨fun d => ?_⟩
  have hg : D.grade d.1 ≤ 0 := by
    have h := d.2.2
    simpa only [overlapTarget, he, Finset.card_empty, min_zero, CellScheme.grade] using h
  exact (Nat.not_lt_of_ge hg) (D.grade_pos d.1)

/-- Given both old lifting clauses, the two-face extension takes place at a
single cutoff. The overlap is determined by the faces, not part of the input. -/
structure CutCover (sem : Semantics D) (I : Finset ι × ℕ) (k : ℕ) where
  L : Finset ι
  R : Finset ι
  covered : ∀ d : Cell D, D.grade d ≤ k → D.scope d ⊆ L ∨ D.scope d ⊆ R
  le : GradedLe I (L, k)
  left_lift : CappedLift sem le
  right_lift : CappedLift sem (target_le_right (U := (L, k)) (V := (R, k)))

namespace CutCover

variable {k : ℕ} (W : CutCover sem I k)

theorem cover (hg : ∀ d : Cell D, D.grade d ≤ k) (d : Cell D) :
    GradedLe (D.cell d) (W.L, k) ∨ GradedLe (D.cell d) (W.R, k) :=
  (W.covered d (hg d)).imp (fun h => ⟨h, hg d⟩) (fun h => ⟨h, hg d⟩)

def precomp (h : GradedLe J I) (hl : CappedLift sem h) : CutCover sem J k :=
  ⟨W.L, W.R, W.covered, h.trans W.le, hl.comp W.left_lift, W.right_lift⟩

include W

/-- Lift on the left, then its overlap on the right. Locality and
availability on the union are read in a face containing the relevant owner. -/
theorem extend (hg : ∀ d : Cell D, D.grade d ≤ k)
    {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    {p : D.below I → ExtOrd} (hp : RespectsSemanticsBelow sem I p)
    {γ : ExtOrd} (hγ : SelfVis k γ)
    (hag : ∀ d : D.below I, min (q d.1) γ = min (p d) γ) :
    ∃ r : Cell D → ExtOrd, RespectsSemantics sem r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧ ∀ d : D.below I, r d.1 = p d := by
  classical
  obtain ⟨u, hu, hucap, huread⟩ := W.left_lift p (fun d => q d.1) γ hp (hq.toBelow _) hγ hag
  let O := overlapTarget (W.L, k) (W.R, k)
  let o (d : D.below O) := u (CellScheme.below.mono target_le_left d)
  obtain ⟨v, hv, hvcap, hvread⟩ := W.right_lift o (fun d => q d.1) γ
    (hu.mono target_le_left) (hq.toBelow _) hγ (fun d => (hucap (CellScheme.below.mono target_le_left d)).symm)
  let r (d : Cell D) := if h : GradedLe (D.cell d) (W.L, k) then u ⟨d, h⟩
    else v ⟨d, (W.cover hg d).resolve_left h⟩
  have hL (d : D.below (W.L, k)) : r d.1 = u d := dif_pos d.2
  have hR (d : D.below (W.R, k)) : r d.1 = v d := by
    by_cases hd : GradedLe (D.cell d.1) (W.L, k)
    · rw [hL ⟨d.1, hd⟩]
      exact (hvread ⟨d.1, (below_target_iff d.1).mpr ⟨hd, d.2⟩⟩).symm
    · exact dif_neg hd
  have hu' : RespectsSemanticsBelow sem (W.L, k) (fun d => r d.1) := (funext hL).symm ▸ hu
  have hv' : RespectsSemanticsBelow sem (W.R, k) (fun d => r d.1) := (funext hR).symm ▸ hv
  refine ⟨r, ⟨?_, ?_, ?_⟩, ?_, fun d => (hL (CellScheme.below.mono W.le d)).trans (huread d)⟩
  · intro d
    rcases W.cover hg d with hd | hd
    · exact hu'.orderly ⟨d, hd⟩
    · exact hv'.orderly ⟨d, hd⟩
  · intro d
    rcases W.cover hg d with hd | hd
    · exact hu'.locality ⟨d, hd⟩
    · exact hv'.locality ⟨d, hd⟩
  · intro c d hs hgrade
    have hcd : GradedLe (D.cell c) (D.cell d) := ⟨hs, hgrade.le⟩
    rcases W.cover hg d with hd | hd
    · obtain ⟨e, he, hce⟩ := hu'.availability ⟨c, hcd.trans hd⟩ ⟨d, hd⟩ hs hgrade
      exact ⟨e.1, he, hce⟩
    · obtain ⟨e, he, hce⟩ := hv'.availability ⟨c, hcd.trans hd⟩ ⟨d, hd⟩ hs hgrade
      exact ⟨e.1, he, hce⟩
  · intro d
    rcases W.cover hg d with hd | hd
    · rw [hL ⟨d, hd⟩]; exact hucap ⟨d, hd⟩
    · rw [hR ⟨d, hd⟩]; exact hvcap ⟨d, hd⟩

/-- Bottom-cap completion needs no ambient. -/
theorem section_of (hg : ∀ d : Cell D, D.grade d ≤ k)
    {p : D.below I → ExtOrd} (hp : RespectsSemanticsBelow sem I p) :
    ∃ r : Cell D → ExtOrd, RespectsSemantics sem r ∧ ∀ d : D.below I, r d.1 = p d := by
  obtain ⟨r, hr, -, hread⟩ := W.extend hg (RespectsSemantics.bot sem) hp (selfVis_bot _) (by simp)
  exact ⟨r, hr, hread⟩

end CutCover

end VaughtConjecture.Knight.CoatomBoundaryExtension
