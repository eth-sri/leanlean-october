/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairRows
public import VaughtConjecture.Knight.CanonicalSections

/-! # Two canonical lower layers retaining higher proper owners

Construct the canonical pair on the grade-k boundary cut, then retain every
higher proper owner with its literal original row and label. The selected
operator is lawful, orbit supported, and agrees on every lower auxiliary at
fixed outer parameters. The old boundary need not have grade at most k.

This constructs lower rows for the proper-grade-three problem; it does not
claim arbitrary cap-preserving extension of a joint boundary/controller history.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalPairBoundary
open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SourcePrefixRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j k : ℕ)
  (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

abbrev boundary := GradeCutBoundary.scheme D k
abbrev boundaryRows := GradeCutBoundary.rows D k sem
abbrev firstProfiles := CanonicalGradeCutSections.Profiles (boundaryRows sem k) j
abbrev secondProfiles :=
  CanonicalFieldLayer.Profile (boundaryRows sem k) k (Cell (boundary (D := D) k)) id
abbrev lower := CanonicalMixedGradeLayers.scheme (boundaryRows sem k) j hj hjA k hk hkA
abbrev lowerRows := CanonicalMixedGradeLayers.rows (boundaryRows sem k) j hj hjA
  (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
abbrev scheme := GradeCutPairCarrier.enlarged D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev old := GradeCutPairCarrier.old D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev embed := GradeCutPairCarrier.embed D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev rows := GradeCutPairRows.rows D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA hp hjk.le sem (lowerRows sem j k hj hjA hk hkA hp hjk)

theorem overlap (c : Cell (boundary (D := D) k))
    (d : (boundary (D := D) k).below ((boundary (D := D) k).cell c)) :
    (lowerRows sem j k hj hjA hk hkA hp hjk).E
      (GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA c)
      ⟨GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA d.1, by
          simpa only [GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
            GradeCutPairCarrier.idx] using d.2⟩ = (boundaryRows sem k).E c d :=
  CanonicalMixedGradeLayers.original_row (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j k hj hjA hk hkA hp hjk).IsConsistent :=
  GradeCutPairRows.consistent D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) hs
    (CanonicalMixedGradeLayers.consistent (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.consistent D k sem hs))

theorem lower_row (c : Cell (lower sem j k hj hjA hk hkA))
    (d : (lower sem j k hj hjA hk hkA).below ((lower sem j k hj hjA hk hkA).cell c)) :
    (rows sem j k hj hjA hk hkA hp hjk).E (embed sem j k hj hjA hk hkA c)
      ⟨embed sem j k hj hjA hk hkA d.1, by
        simpa only [embed, GradeCutPairCarrier.embed_index] using d.2⟩ =
      (lowerRows sem j k hj hjA hk hkA hp hjk).E c d :=
  GradeCutPairRows.embedded_row D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) c d

variable {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)

  {G : Finset ExtOrd} {C : ExtOrd}

/-- Ordinary whole-boundary sections also allow literal top, independently
of the proper-profile selected operator. There is no ambient-cap conclusion. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk) r ∧
      ∀ d, r (old sem j k hj hjA hk hkA d) = p d := by
  obtain ⟨u, hu, hread⟩ := CanonicalSections.exists_whole (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
  let all (d : Cell (lower sem j k hj hjA hk hkA)) :
      (lower sem j k hj hjA hk hkA).below (A, k) :=
    ⟨d, (lower sem j k hj hjA hk hkA).isPlan.subset_of_mem
        ((lower sem j k hj hjA hk hkA).scope_mem_plan d),
      GradeCutPairCarrier.small_grade D _ _ j k hj hjA hk hkA hjk.le d⟩
  let v := fun d => u (all d)
  have hv : RespectsSemantics (lowerRows sem j k hj hjA hk hkA hp hjk) v :=
    hu.toRespects (fun d => (all d).2)
  refine ⟨GradeCutPairRows.glue D _ _ j k hj hjA hk hkA p v,
    GradeCutPairRows.glue_respects D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) hpr hv ?_,
    GradeCutPairRows.glue_old D _ _ j k hj hjA hk hkA p v⟩
  exact hread
