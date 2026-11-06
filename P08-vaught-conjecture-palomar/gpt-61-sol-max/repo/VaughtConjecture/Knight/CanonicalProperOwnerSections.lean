
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalProperOwnerLayer
import VaughtConjecture.Knight.SourcePrefixAmbient
import VaughtConjecture.Knight.CanonicalPairedInverse
import VaughtConjecture.Knight.CanonicalOwnerBoundary
import VaughtConjecture.Knight.RetunedCutDecoding
import VaughtConjecture.Knight.HighLayerBountiful

/-! # Independent section supply through the three canonical layers

Full-controller rows are short at their own grades; proper long rows are
retained literally. Decoding can therefore reconstruct an arbitrary lawful
old boundary, including top, without any positive-cap lifting assumption.
-/

namespace VaughtConjecture.Knight.CanonicalProperOwnerSections
open    CanonicalProperOwnerLayer
open SharpWitnessComposition  


variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : AvoidsValue D.scope A) 

local notation "lowerScheme₀" => lowerScheme sem k h2k hkA

local notation "one_le₀" => one_le k h2k hkA

local notation "two_le₀" => two_le k h2k hkA

theorem lower_full_short c
    (hc : (lowerScheme₀).scope c = A)
    d :
    Short ((lowerScheme₀).grade c) ((lowerSem sem k h2k hkA hp).E c d) := by
  have hc2 : (lowerScheme₀).grade c ≤ 2 := by
    obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
      one_le₀ (by decide) two_le₀).surjective c
    change (lowerScheme₀).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ 2
    change ((lowerScheme₀).cell
      (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x)).1 = A at hc
    rw [GradeCutPairCarrier.cell_idx] at hc
    rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
    rcases x with (c | q) | q
    · exact (hp c hc).elim
    · exact (by decide : 1 ≤ 2)
    · exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutPairCarrier.exhaustive D _ _ 1 2 (by decide)
    one_le₀ (by decide) two_le₀ c hc2
  obtain ⟨e, rfl⟩ := (GradeCutPairCarrier.belowEquiv D _ _ 1 2 (by decide)
    one_le₀ (by decide) two_le₀ _ hc2).surjective d
  have he := CanonicalPairBoundary.lower_row sem 1 2 (by decide) (one_le₀)
    (by decide) (two_le₀) hp (by decide) a
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  have hv := CanonicalMixedGradeLayers.full_source_short
    (CanonicalPairBoundary.boundaryRows sem 2) 1 (by decide) one_le₀
    (GradeCutBoundary.proper hp) 2 (GradeCutBoundary.grade_bound)
    (by decide) two_le₀ (by decide) a
    (by simpa only [CellScheme.scope, GradeCutPairCarrier.embed_index] using hc)
    ⟨e.1, by grind⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutPairCarrier.embed_index a))).mpr hv


