/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerRows
public import VaughtConjecture.Knight.CanonicalFieldLayer

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

local notation "Γ" => GradeCutLayerRows.assembly D (Profiles sem j) j hj hA hproper

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
    (lowerRows sem j hj hA hproper) (by solve_by_elim [overlap]) hs
    (CanonicalFieldLayer.consistent (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.consistent D j sem hs))

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j hj hA hproper).E (old sem j hj hA c)
      (GradeCutLayerCarrier.ownerEquiv D (Profiles sem j) j hj hA hproper c d) = sem.E c d :=
  GradeCutLayerRows.old_row D (Profiles sem j) j hj hA hproper sem _ c d

theorem lower_row (c : Cell (lower sem j hj hA))
    (d : (lower sem j hj hA).below ((lower sem j hj hA).cell c)) :
    (rows sem j hj hA hproper).E (lowerEmbed sem j hj hA c)
      ⟨lowerEmbed sem j hj hA d.1, by grind [GradeCutLayerCarrier.embed_cell]⟩ =
      (lowerRows sem j hj hA hproper).E c d :=
  GradeCutLayerRows.embedded_row D (Profiles sem j) j hj hA hproper sem _
    (by solve_by_elim [overlap]) c d

variable {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)

variable (ht : ∀ d : Cell D, p d ≠ ⊤)

def lowerSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (lower sem j hj hA) → ExtOrd :=
  CanonicalFieldLayer.sectionOf (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (scheme sem j hj hA) → ExtOrd :=
  (Γ).union.paste p
    (lowerSection sem j hj hA hproper hp ht G C)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_old (d : Cell D) :
    sectionOf sem j hj hA hproper hp ht G C (old sem j hj hA d) = p d :=
  (Γ).union.paste_old p _ d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j hj hA hproper) (sectionOf sem j hj hA hproper hp ht G C) :=
  (Γ).paste_respects
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
    (d : Cell (scheme sem j hj hA)) : sectionOf sem j hj hA hproper hp ht G C d ≤ C :=
  (Γ).union.paste_pred (P := (· ≤ C)) hb (CanonicalFieldLayer.section_bound (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht hC hb) d

theorem section_supported {K : ℕ} (hjK : j ≤ K) (hCG : C ∈ G)
    (d : Cell (scheme sem j hj hA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j hj hA hproper hp ht G C d) :=
  (Γ).union.paste_pred (OrbitPrefixSupport.supported_field _ _ _)
    (CanonicalFieldLayer.section_supported (boundaryRows sem j) j
      (Cell D) (GradeCutBoundary.toCell D j) hj hA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
      (GradeCutBoundary.restrict_respects D j sem hp) ht hjK hCG) d

theorem section_agreement {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    (htq : ∀ d : Cell D, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j hj hA hproper hp ht G C)
      (sectionOf sem j hj hA hproper hq htq G C) h := by
  have hl := CanonicalFieldLayer.section_agreement (boundaryRows sem j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j)
    (GradeCutBoundary.restrict_respects D j sem hp) ht
    (GradeCutBoundary.restrict_respects D j sem hq) htq hG hC hh hhC hag
  exact (Γ).union.paste_rel (R := fun x y => min x h = min y h) hag hl

end

end VaughtConjecture.Knight.CanonicalGradeCutSections
