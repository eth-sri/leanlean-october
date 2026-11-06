/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalProperOwnerLift
public import VaughtConjecture.Knight.CanonicalProperOwnerLower

/-! # Independent section supply through the three canonical layers

Full-controller rows are short at their own grades; proper long rows are
retained literally. Decoding can therefore reconstruct an arbitrary lawful
old boundary, including top, without any positive-cap lifting assumption.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalProperOwnerSections
open Transform Value ExtOrd CanonicalProperOwnerLayer
open SharpWitnessComposition CoatomBoundaryExtension PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ k)

theorem lower_full_short (c : Cell (lowerScheme sem k h2k hkA))
    (hc : (lowerScheme sem k h2k hkA).scope c = A)
    (d : (lowerScheme sem k h2k hkA).below ((lowerScheme sem k h2k hkA).cell c)) :
    Short ((lowerScheme sem k h2k hkA).grade c) ((lowerSem sem k h2k hkA hp).E c d) := by
  have hc2 : (lowerScheme sem k h2k hkA).grade c ≤ 2 := by
    obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
      (one_le k h2k hkA) (by decide) (two_le k h2k hkA)).surjective c
    change (lowerScheme sem k h2k hkA).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ 2
    change ((lowerScheme sem k h2k hkA).cell
      (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x)).1 = A at hc
    rw [GradeCutPairCarrier.cell_idx] at hc
    rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
    rcases x with (c | q) | q
    · exact (hp c hc).elim
    · exact (by decide : 1 ≤ 2)
    · exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutPairCarrier.exhaustive D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA) c hc2
  obtain ⟨e, rfl⟩ := (GradeCutPairCarrier.belowEquiv D _ _ 1 2 (by decide)
    (one_le k h2k hkA) (by decide) (two_le k h2k hkA) _ hc2).surjective d
  have he := CanonicalPairBoundary.lower_row sem 1 2 (by decide) (one_le k h2k hkA)
    (by decide) (two_le k h2k hkA) hp (by decide) a
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  have hv := CanonicalMixedGradeLayers.full_source_short
    (CanonicalPairBoundary.boundaryRows sem 2) 1 (by decide) (one_le k h2k hkA)
    (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) (two_le k h2k hkA) (by decide) a
    (by simpa only [CellScheme.scope, GradeCutPairCarrier.embed_index] using hc)
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutPairCarrier.embed_index D _ _ 1 2 (by decide) (one_le k h2k hkA)
      (by decide) (two_le k h2k hkA) a))).mpr hv

