/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairRows
public import VaughtConjecture.Knight.CanonicalSections

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPairBoundary

open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SourcePrefixRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (j k : ℕ)

variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

abbrev boundary := GradeCutBoundary.scheme D k

abbrev boundaryRows := GradeCutBoundary.rows D k sem

abbrev firstProfiles := CanonicalGradeCutSections.Profiles (boundaryRows sem k) j

abbrev secondProfiles :=
  CanonicalFieldLayer.Profile (boundaryRows sem k) k (Cell (boundary (D := D) k)) id

abbrev lower := CanonicalMixedGradeLayers.enlarged (boundaryRows sem k) j hj hjA k hk hkA

def frame : CanonicalMixedGradeLayers.Frame (boundary (D := D) k) :=
  ⟨boundaryRows sem k, j, k, hj, hjk, hkA,
    GradeCutBoundary.proper D k hp, GradeCutBoundary.grade_bound D k⟩

abbrev lowerRows := CanonicalMixedGradeLayers.rows (frame sem j k hj hkA hp hjk)

abbrev scheme := GradeCutPairCarrier.enlarged D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA

abbrev old := GradeCutPairCarrier.old D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA

abbrev embed := GradeCutPairCarrier.embed D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA

abbrev rows := GradeCutPairRows.rows D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA hp hjk.le sem (lowerRows sem j k hj hkA hp hjk)

theorem overlap :
    (GradeCutPairRows.assembly D (firstProfiles sem j k) (secondProfiles sem k)
      j k hj hjA hk hkA hp hjk.le).Compatible sem (lowerRows sem j k hj hkA hp hjk) :=
  CanonicalMixedGradeLayers.original_row (frame sem j k hj hkA hp hjk)

theorem consistent (hs : sem.IsConsistent) : (rows sem j k hj hjA hk hkA hp hjk).IsConsistent :=
  GradeCutPairRows.consistent D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) hs
    (CanonicalMixedGradeLayers.consistent (frame sem j k hj hkA hp hjk)
      (GradeCutBoundary.consistent D k sem hs))

theorem lower_row (c : Cell (lower sem j k hj hjA hk hkA))
    (d : (lower sem j k hj hjA hk hkA).below ((lower sem j k hj hjA hk hkA).cell c)) :
    (rows sem j k hj hjA hk hkA hp hjk).E (embed sem j k hj hjA hk hkA c)
      ⟨embed sem j k hj hjA hk hkA d.1, by
        simpa only [embed, GradeCutPairCarrier.embed_index] using d.2⟩ =
      (lowerRows sem j k hj hkA hp hjk).E c d :=
  GradeCutPairRows.embedded_row D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) c d

variable {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p)

/-- Ordinary whole-boundary sections also allow literal top, independently
of the proper-profile selected operator. There is no ambient-cap conclusion. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk) r ∧
      ∀ d, r (old sem j k hj hjA hk hkA d) = p d := by
  obtain ⟨u, hu, hread⟩ := CanonicalSections.exists_whole (frame sem j k hj hkA hp hjk)
    (GradeCutBoundary.restrict_respects D k sem hpr)
  let all (d : Cell (lower sem j k hj hjA hk hkA)) :
      (lower sem j k hj hjA hk hkA).below (A, k) :=
    ⟨d, (lower sem j k hj hjA hk hkA).scope_subset d,
      GradeCutPairCarrier.small_grade D _ _ j k hj hjA hk hkA hjk.le d⟩
  let v := fun d => u (all d)
  have hv : RespectsSemantics (lowerRows sem j k hj hkA hp hjk) v :=
    hu.toRespects (fun d => (all d).2)
  let Γ := GradeCutPairRows.assembly D (firstProfiles sem j k) (secondProfiles sem k)
    j k hj hjA hk hkA hp hjk.le
  refine ⟨Γ.union.paste p v,
    Γ.paste_respects (overlap sem j k hj hjA hk hkA hp hjk) hpr hv ?_, Γ.union.paste_old p v⟩
  exact hread

end

end VaughtConjecture.Knight.CanonicalPairBoundary
