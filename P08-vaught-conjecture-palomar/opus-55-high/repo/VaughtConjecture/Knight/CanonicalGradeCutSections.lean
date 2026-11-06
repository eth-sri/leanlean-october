/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerRows
public import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Constructed sections retaining higher proper owners

Normalize the complete old field inventory while constructing its grade-j layer, then splice back
the entire proper boundary. The boundary may have higher-grade active owners.
Their rows and labels remain literal. No overlap compatibility, future locality
or lower completion is supplied as an input.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalGradeCutSections

open Transform Value ExtOrd SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

abbrev boundary := GradeCutBoundary.scheme D j
abbrev boundaryRows := GradeCutBoundary.rows D j sem
abbrev Profiles := CanonicalFieldLayer.Profile (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j)
abbrev lower := CanonicalFieldLayer.scheme (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
abbrev lowerRows := CanonicalFieldLayer.rows (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
  (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
abbrev scheme := GradeCutLayerCarrier.enlarged D (Profiles sem j) j hj hA
abbrev rows := GradeCutLayerRows.rows D (Profiles sem j) j hj hA hproper sem
  (lowerRows sem j hj hA hproper)
abbrev old (c : Cell D) := SourceLayerCarrier.toCell D (Profiles sem j) j hj hA (.inl c)
abbrev lowerEmbed := GradeCutLayerCarrier.embed D (Profiles sem j) j hj hA

theorem overlap (c : Cell (boundary (D := D) j))
    (d : (boundary (D := D) j).below ((boundary (D := D) j).cell c)) :
    (lowerRows sem j hj hA hproper).E
      (SourceLayerCarrier.toCell (boundary (D := D) j) (Profiles sem j) j hj hA (.inl c))
      (GradeCutLayerCarrier.ownerEquiv (boundary (D := D) j) (Profiles sem j) j hj hA
        (GradeCutBoundary.proper D j hproper) c d) = (boundaryRows sem j).E c d :=
  CanonicalFieldLayer.inherited_row (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j hj hA hproper).IsConsistent :=
  GradeCutLayerRows.consistent D (Profiles sem j) j hj hA hproper sem
    (lowerRows sem j hj hA hproper) (overlap sem j hj hA hproper) hs
    (CanonicalFieldLayer.consistent (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.consistent D j sem hs))

theorem old_row c d :
    (rows sem j hj hA hproper).E (old sem j hj hA c)
      (GradeCutLayerCarrier.ownerEquiv D (Profiles sem j) j hj hA hproper c d) = sem.E c d :=
  GradeCutLayerRows.old_row D (Profiles sem j) j hj hA hproper sem _ c d

theorem lower_row (c : Cell (lower sem j hj hA))
    (d : (lower sem j hj hA).below ((lower sem j hj hA).cell c)) :
    (rows sem j hj hA hproper).E (lowerEmbed sem j hj hA c)
      ⟨lowerEmbed sem j hj hA d.1, by
        simpa only [GradeCutLayerCarrier.embed_cell] using d.2⟩ =
      (lowerRows sem j hj hA hproper).E c d :=
  GradeCutLayerRows.embedded_row D (Profiles sem j) j hj hA hproper sem _
    (overlap sem j hj hA hproper) c d

variable {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
variable (ht : ∀ d : Cell D, p d ≠ ⊤)

section
variable (G : Finset ExtOrd) (C : ExtOrd)

def lowerSection  : Cell (lower sem j hj hA) → ExtOrd :=
  CanonicalFieldLayer.sectionOf (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht G C

def sectionOf  : Cell (scheme sem j hj hA) → ExtOrd :=
  GradeCutLayerRows.glue D (Profiles sem j) j hj hA p
    (lowerSection sem j hj hA hproper hp ht G C)

end

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_old d :
    sectionOf sem j hj hA hproper hp ht G C (old sem j hj hA d) = p d :=
  GradeCutLayerRows.glue_old D (Profiles sem j) j hj hA p _ d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j hj hA hproper) (sectionOf sem j hj hA hproper hp ht G C) :=
  GradeCutLayerRows.glue_respects D (Profiles sem j) j hj hA hproper sem _
    (overlap sem j hj hA hproper) hp
    (CanonicalFieldLayer.section_lawful (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hG hC)
    (CanonicalFieldLayer.section_old (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hG hC)

theorem section_bound (hC : SelfVis j C) (hb : ∀ d, p d ≤ C)
    d : sectionOf sem j hj hA hproper hp ht G C d ≤ C := by
  unfold sectionOf GradeCutLayerRows.glue
  cases SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA d with
  | inl c => exact hb c
  | inr q =>
    exact CanonicalFieldLayer.section_bound (boundaryRows sem j) j
      (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hC
      hb _

section
variable {K : ℕ}

private theorem boundary_supported {H} d :
    OrbitPrefixSupport.Supported K H p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · tauto
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by simp_all⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]⟩)

theorem section_supported (hjK : j ≤ K) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hA hproper hp ht G C d) := by
  unfold sectionOf GradeCutLayerRows.glue
  cases SourceLayerCarrier.toOcc D (Profiles sem j) j hj hA d with
  | inl c => exact boundary_supported c
  | inr q =>
    exact CanonicalFieldLayer.section_supported (boundaryRows sem j) j
      (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hjK hCG _

end

theorem section_agreement {q} hq
    (htq : ∀ d, q d ≠ ⊤)
    {h} (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j hj hA hproper hp ht G C)
      (sectionOf sem j hj hA hproper hq htq G C) h := by
  have hl := CanonicalFieldLayer.section_agreement (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht
    (GradeCutBoundary.restrict_respects D j sem hq) htq hG hC hh hhC hag
  intro d
  unfold sectionOf GradeCutLayerRows.glue
  aesop

end
end VaughtConjecture.Knight.CanonicalGradeCutSections
