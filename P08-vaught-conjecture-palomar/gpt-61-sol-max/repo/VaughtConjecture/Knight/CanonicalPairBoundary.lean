
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutPairRows
import VaughtConjecture.Knight.CanonicalSections

/-! # Two canonical lower layers retaining higher proper owners

Construct the canonical pair on the grade-k boundary cut, then retain every
higher proper owner with its literal original row and label. The selected
operator is lawful, orbit supported, and agrees on every lower auxiliary at
fixed outer parameters. The old boundary need not have grade at most k.

This constructs lower rows for the proper-grade-three problem; it does not
claim arbitrary cap-preserving extension of a joint boundary/controller history.
-/

namespace VaughtConjecture.Knight.CanonicalPairBoundary

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j k : ℕ)
variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : AvoidsValue D.scope A) (hjk : j < k)

abbrev boundary := GradeCutBoundary.scheme D k
abbrev boundaryRows := GradeCutBoundary.rows D k sem
local notation "boundaryRows₀" => boundaryRows sem k

abbrev firstProfiles := CanonicalGradeCutSections.Profiles (boundaryRows₀) j
abbrev secondProfiles :=
  CanonicalFieldLayer.Profile (boundaryRows₀) k (Cell (boundary  k)) id
abbrev lower := CanonicalMixedGradeLayers.scheme (boundaryRows₀) j hj hjA k hk hkA
abbrev lowerRows := CanonicalMixedGradeLayers.rows (boundaryRows₀) j hj hjA
  (GradeCutBoundary.proper hp) k GradeCutBoundary.grade_bound hk hkA hjk
local notation "firstProfiles₀" => firstProfiles sem j k

abbrev scheme := GradeCutPairCarrier.enlarged D (firstProfiles₀) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev old := GradeCutPairCarrier.old D (firstProfiles₀) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev embed := GradeCutPairCarrier.embed D (firstProfiles₀) (secondProfiles sem k)
  j k hj hjA hk hkA
local notation "lowerRows₀" => lowerRows sem j k hj hjA hk hkA hp hjk

abbrev rows := GradeCutPairRows.rows D (firstProfiles₀) (secondProfiles sem k)
  j k hj hjA hk hkA hp hjk.le sem (lowerRows₀)

local notation "boundary₀" => boundary (D := D) k

variable {sem j k hj hjA hk hkA hp hjk} in
theorem overlap (c : Cell (boundary₀))
    (d : (boundary₀).belowCell c) :
    (lowerRows₀).E
      (GradeCutPairCarrier.old (boundary₀) (firstProfiles₀)
        (secondProfiles sem k) j k hj hjA hk hkA c)
      ⟨GradeCutPairCarrier.old (boundary₀) (firstProfiles₀)
        (secondProfiles sem k) j k hj hjA hk hkA d.1, by
          simpa only [GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
            GradeCutPairCarrier.idx] using d.2⟩ = (boundaryRows₀).E c d :=
  CanonicalMixedGradeLayers.original_row (boundaryRows₀) j hj hjA
    (GradeCutBoundary.proper hp) k GradeCutBoundary.grade_bound hk hkA hjk c d

local notation "overlap₀" => overlap

local notation "rows₀" => rows sem j k hj hjA hk hkA hp hjk

variable {sem j k hj hjA hk hkA hp hjk} in
theorem consistent (hs : sem.IsConsistent) : (rows₀).IsConsistent :=
  GradeCutPairRows.consistent D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap₀) hs
    (CanonicalMixedGradeLayers.consistent (boundaryRows₀) j hj hjA
      (GradeCutBoundary.proper hp) k GradeCutBoundary.grade_bound hk hkA hjk
      (GradeCutBoundary.consistent D k sem hs))

local notation "lower₀" => lower sem j k hj hjA hk hkA

theorem lower_row c
    (d : (lower₀).belowCell c) :
    (rows₀).E (embed sem j k hj hjA hk hkA c)
      ⟨embed sem j k hj hjA hk hkA d.1, by
        simpa only [embed, GradeCutPairCarrier.embed_index] using d.2⟩ =
      (lowerRows₀).E c d :=
  GradeCutPairRows.embedded_row
    (overlap₀) c d

variable {p : CellLabels D} (hpr : RespectsSemantics sem p) 

theorem exists_whole {p} (hpr : RespectsSemantics sem p) :
    ∃ r ,
      RespectsSemantics (rows₀) r ∧
      ∀ d, r (old sem j k hj hjA hk hkA d) = p d := by
  obtain ⟨u, hu, hread⟩ := CanonicalSections.exists_whole (boundaryRows₀) j hj hjA
    (GradeCutBoundary.proper hp) k GradeCutBoundary.grade_bound hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
  let all (d : Cell lower₀) :
      (lower₀).below (A, k) :=
    ⟨d, (lower₀).scope_subset d,
      GradeCutPairCarrier.small_grade D _ _ j k hj hjA hk hkA hjk.le d⟩
  let v := fun d => u (all d)
  have hv : RespectsSemantics (lowerRows₀) v :=
    hu.toRespects (fun d => (all d).2)
  refine ⟨GradeCutPairRows.glue D _ _ j k hj hjA hk hkA p v,
    GradeCutPairRows.glue_respects D _ _ j k hj hjA hk hkA hp hjk.le sem _
      overlap₀ hpr hv ?_,
    GradeCutPairRows.glue_old p v⟩
  exact hread

