
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutLayerRows
import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Constructed sections retaining higher proper owners

Normalize the complete old field inventory while constructing its grade-j layer, then splice back
the entire proper boundary. The boundary may have higher-grade active owners.
Their rows and labels remain literal. No overlap compatibility, future locality
or lower completion is supplied as an input.
-/

namespace VaughtConjecture.Knight.CanonicalGradeCutSections

open  Value ExtOrd SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d , D.scope d ≠ A)

abbrev boundary := GradeCutBoundary.scheme D j
abbrev boundaryRows := GradeCutBoundary.rows D j sem
local notation "boundaryRows₀" => boundaryRows sem j

local notation "toCell₀" => GradeCutBoundary.toCell D j

abbrev Profiles := CanonicalFieldLayer.Profile (boundaryRows₀) j
    (Cell D) (toCell₀)
abbrev lower := CanonicalFieldLayer.scheme (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
local notation "proper₀" => GradeCutBoundary.proper hproper

abbrev lowerRows := CanonicalFieldLayer.rows (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
  (proper₀) (GradeCutBoundary.grade_bound)
local notation "Profiles₀" => Profiles sem j

abbrev scheme := GradeCutLayerCarrier.enlarged D (Profiles₀) j hj hA
local notation "lowerRows₀" => lowerRows sem j hj hA hproper

abbrev rows := GradeCutLayerRows.rows hproper sem
  (lowerRows₀)
abbrev old c := SourceLayerCarrier.toCell D (Profiles₀) j hj hA (.inl c)
abbrev lowerEmbed := GradeCutLayerCarrier.embed D (Profiles₀) j hj hA

local notation "boundary₀" => boundary (D := D) j

theorem overlap (c : Cell (boundary₀))
    (d : (boundary₀).belowCell c) :
    (lowerRows₀).E
      (SourceLayerCarrier.toCell (boundary₀) (Profiles₀) j hj hA (.inl c))
      (GradeCutLayerCarrier.ownerEquiv hj hA
        (GradeCutBoundary.proper hproper) c d) = (boundaryRows₀).E c d :=
  CanonicalFieldLayer.inherited_row c d

local notation "rows₀" => rows sem j hj hA hproper

theorem consistent (hs : sem.IsConsistent) : (rows₀).IsConsistent :=
  GradeCutLayerRows.consistent D (Profiles₀) j hj hA hproper sem
    (lowerRows₀) (overlap sem j hj hA hproper) hs
    (CanonicalFieldLayer.consistent (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
      (proper₀) GradeCutBoundary.grade_bound
      (GradeCutBoundary.consistent D j sem hs))

theorem old_row c d :
    (rows₀).E (old sem j hj hA c)
      (GradeCutLayerCarrier.ownerEquiv hj hA hproper c d) = sem.E c d :=
  GradeCutLayerRows.old_row D (Profiles₀) j hj hA hproper sem _ c d

local notation "lower₀" => lower sem j hj hA

theorem lower_row c
    d :
    (rows₀).E (lowerEmbed sem j hj hA c)
      ⟨lowerEmbed sem j hj hA d.1, by
        simpa only [GradeCutLayerCarrier.embed_cell] using d.2⟩ =
      (lowerRows₀).E c d :=
  GradeCutLayerRows.embedded_row D (Profiles₀) j hj hA hproper sem _
    (overlap sem j hj hA hproper) c d

variable {p : CellLabels D} (hp : RespectsSemantics sem p)
variable (ht : ∀ d , p d ≠ ⊤)

local notation "restrict_respects₀" => GradeCutBoundary.restrict_respects D j sem hp

def lowerSection (G : Finset ExtOrd) (C : ExtOrd) : CellLabels (lower₀) :=
  CanonicalFieldLayer.sectionOf (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
    (proper₀) (GradeCutBoundary.grade_bound)
    (restrict_respects₀) ht G C

local notation "Cell₀" => Cell (scheme sem j hj hA)

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell₀ → ExtOrd :=
  GradeCutLayerRows.glue D (Profiles₀) j hj hA p
    (lowerSection sem j hj hA hproper hp ht G C)

variable {G : Finset ExtOrd} {C : ExtOrd}

local notation "sectionOf₀" => sectionOf sem j hj hA hproper hp ht

theorem section_old d :
    sectionOf₀ G C (old sem j hj hA d) = p d :=
  GradeCutLayerRows.glue_old D (Profiles₀) j hj hA p _ d

theorem section_lawful (hG : VisibleOn j G) (hC : SelfVis j C) :
    RespectsSemantics (rows₀) (sectionOf₀ G C) :=
  GradeCutLayerRows.glue_respects D (Profiles₀) j hj hA hproper sem _
    (overlap sem j hj hA hproper) hp
    (CanonicalFieldLayer.section_lawful (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
      (proper₀) GradeCutBoundary.grade_bound
      (restrict_respects₀) ht hG hC)
    (CanonicalFieldLayer.section_old (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
      (proper₀) GradeCutBoundary.grade_bound
      (restrict_respects₀) ht hG hC)

local notation "toOcc₀" => SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA

theorem section_bound (hC : SelfVis j C) (hb : BoundedBy p C)
    d : sectionOf₀ G C d ≤ C := by
  unfold sectionOf GradeCutLayerRows.glue
  cases toOcc₀ d with
  | inl c => exact hb c
  | inr q =>
    exact CanonicalFieldLayer.section_bound (boundaryRows₀) j
      (Cell D) (toCell₀) hj hA
      proper₀ GradeCutBoundary.grade_bound
      restrict_respects₀ ht hC
      hb _

private theorem boundary_supported {K} {H} d :
    OrbitPrefixSupport.Supported K H p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        grind [extVisibilityReplace_of_le_finitePart]⟩)

theorem section_supported {K} (hjK : j ≤ K) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf₀ G C d) := by
  unfold sectionOf GradeCutLayerRows.glue
  cases toOcc₀ d with
  | inl c => exact boundary_supported c
  | inr q =>
    exact CanonicalFieldLayer.section_supported (boundaryRows₀) j
      (Cell D) (toCell₀) hj hA
      proper₀ GradeCutBoundary.grade_bound
      restrict_respects₀ ht hjK hCG _

theorem section_agreement {q} (hq : RespectsSemantics sem q)
    (htq : AvoidsValue q ⊤)
    {h} (hG : VisibleOn j G) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀ G C)
      (sectionOf sem j hj hA hproper hq htq G C) h := by
  have hl := CanonicalFieldLayer.section_agreement (boundaryRows₀) j
    (Cell D) (toCell₀) hj hA
    proper₀ GradeCutBoundary.grade_bound
    restrict_respects₀ ht
    (GradeCutBoundary.restrict_respects D j sem hq) htq hG hC hh hhC hag
  intro d
  unfold sectionOf GradeCutLayerRows.glue
  cases toOcc₀ d with
  | inl c => exact hag c
  | inr q => exact hl _

