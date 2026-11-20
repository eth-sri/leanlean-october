/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCodingSupport

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalSeedCoding

open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer CanonicalCodingSupport

open PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem fieldLayer (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X]
    (occ : Cell D → X) (hj : 0 < j) (hA : j ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)
    (hc : sem.IsCoded) : (CanonicalFieldLayer.rows sem j X occ hj hA hp hg).IsCoded := by
  apply layer D _ j hj hA (SeparatedSourceLayerCarrier.separated_of_proper D j hp)
    sem _ hc (CanonicalFieldLayer.inherited_row sem j X occ hj hA hp hg)
  intro q d
  let F := CanonicalFieldLayer.data sem j X occ hj hA hp hg
  change IsCodedLabel j (F.rows.E (CanonicalFieldLayer.controller sem j X occ hj hA q).1 d)
  rw [F.row_new (CanonicalFieldLayer.controller sem j X occ hj hA q) d]
  by_cases hd : (CanonicalFieldLayer.scheme sem j X occ hj hA).cell d.1 = (A, j)
  · rw [show d.1 = (⟨d.1, hd⟩ : Controller _ j).1 from rfl, F.profile_new]
    exact grid j _ (cut_mem (sourceGrid_bot _ _) _ _)
  · obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D
      (CanonicalFieldLayer.Profile sem j X occ) j hj hA d.1 hd
    change IsCodedLabel j (CanonicalFieldLayer.source sem j X occ hj hA hp hg q d.1)
    rw [hx, CanonicalFieldLayer.source_old]
    apply field

theorem cutLayer (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hc : sem.IsCoded) :
    (CanonicalGradeCutSections.rows sem j hj hA hp).IsCoded := by
  let Q := CanonicalGradeCutSections.Profiles sem j
  have low := fieldLayer (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) hj hA (GradeCutBoundary.proper D j hp)
    (GradeCutBoundary.grade_bound D j) (gradeCut sem j hc)
  exact (GradeCutLayerRows.assembly D Q j hj hA hp).union.coded sem _ hc low

open CanonicalMixedGradeLayers in
theorem mixed (M : Frame D) (hc : M.sem.IsCoded) : (rows M).IsCoded := by
  apply layer (lowerScheme M) _ M.upper M.upper_pos M.height
    (lower_separated M) (lowerSem M) _
    (cutLayer M.sem M.lower M.pos M.lower_card M.proper hc) (inherited_row M)
  intro q d
  let F := data M
  change IsCodedLabel M.upper (F.rows.E (controller M q).1 d)
  rw [F.row_new (controller M q) d]
  exact supported (fun _ hh => grid _ _ hh) (field M.sem M.upper id q) (source_supported M q d.1)

theorem pairSplice (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
    (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)
    (sem : Semantics D) (low : Semantics (GradeCutPairCarrier.small D Q R j k hj hjA hk hkA))
    (hc : sem.IsCoded) (hl : low.IsCoded) :
    (GradeCutPairRows.rows D Q R j k hj hjA hk hkA hp hjk sem low).IsCoded :=
  (GradeCutPairRows.assembly D Q R j k hj hjA hk hkA hp hjk).union.coded sem low hc hl

theorem pair (sem : Semantics D) (hA : 2 ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hc : sem.IsCoded) :
    (CanonicalPairLocalSections.semantics sem hA hp).IsCoded := by
  apply pairSplice D _ _ 1 2 (by decide) _ (by decide) hA hp (by decide) sem _ hc
  exact mixed (CanonicalPairBoundary.frame sem 1 2 (by decide) hA hp (by decide))
    (gradeCut sem 2 hc)

end

end VaughtConjecture.Knight.CanonicalSeedCoding
