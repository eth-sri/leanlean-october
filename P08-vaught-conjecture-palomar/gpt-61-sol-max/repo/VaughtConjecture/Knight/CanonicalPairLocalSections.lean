
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalPairBoundary
import VaughtConjecture.Knight.ScopedSourcePrefixLayer

/-! # Selected seed sections from actual current-domain lawfulness

The old profile need not be lawful at future higher proper owners. Their values
remain literal, but only owners through `K` are used in the current source row.
Both seed controller layers retain their existing rows and catalogues.
-/

namespace VaughtConjecture.Knight.CanonicalPairLocalSections
open  Value ExtOrd SourcePrefixRows  
open CanonicalPairBoundary
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card) (hp : AvoidsValue D.scope A)
abbrev one_le := (by decide : 1 ≤ 2).trans hA
local notation "one_le₀" => one_le hA

abbrev carrier := scheme sem 1 2 (by decide) (one_le₀) (by decide) hA
abbrev semantics := rows sem 1 2 (by decide) (one_le₀) (by decide) hA hp (by decide)
abbrev original := old sem 1 2 (by decide) (one_le₀) (by decide) hA
abbrev small := lower sem 1 2 (by decide) (one_le₀) (by decide) hA
abbrev smallRows := lowerRows sem 1 2 (by decide) (one_le₀) (by decide) hA hp (by decide)

variable {K : ℕ} (hK : 2 ≤ K) {p : CellLabels D}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : AvoidsValue p ⊤)

local notation "rows₀" => GradeCutBoundary.rows D 2 sem

local notation "toCell₀" => GradeCutBoundary.toCell D 2

include hK hpr in
theorem cut_lawful : RespectsSemantics (rows₀)
    (fun d => p (toCell₀ d)) := by
  have hr := GradeCutBoundary.pullback_respects le_rfl
    (hpr.mono (show GradedLe (A, 2) (A, K) from ⟨Finset.Subset.refl _, hK⟩))
  exact hr.toRespects (fun d =>
    ⟨D.scope_subset _, GradeCutBoundary.grade_bound d⟩)

local notation "cut_lawful₀" => cut_lawful sem hK hpr

local notation "proper₀" => GradeCutBoundary.proper hp

def smallSection (G : Finset ExtOrd) (C : ExtOrd) : CellLabels (small sem hA) :=
  CanonicalMixedGradeLayers.sectionOf rows₀ 1 (by decide)
    (one_le₀) proper₀ 2 (GradeCutBoundary.grade_bound)
    (by decide) hA (by decide) cut_lawful₀
    (fun d => ht (toCell₀ d)) G C

local notation "smallSection₀" => smallSection sem hA hp hK hpr ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : CellLabels (carrier sem hA) :=
  GradeCutPairRows.glue D _ _ 1 2 (by decide) (one_le₀) (by decide) hA p
    (smallSection₀ G C)

variable {sem hA hp hK hpr ht} in
theorem section_old {G} {C} d :
    sectionOf sem hA hp hK hpr ht G C (original sem hA d) = p d :=
  GradeCutPairRows.glue_old p _ d

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem small_readback (hG : VisibleOn 2 G) (hC : SelfVis 2 C)
    d :
    smallSection₀ G C
      (GradeCutPairCarrier.old (GradeCutBoundary.scheme D 2) _ _ 1 2
        (by decide) (one_le₀) (by decide) hA d) = p (toCell₀ d) :=
  CanonicalMixedGradeLayers.section_boundary (rows₀) 1 (by decide)
    (one_le₀) (proper₀) 2 GradeCutBoundary.grade_bound
    (by decide) hA (by decide) (cut_lawful₀) _ hG hC d

local notation "sectionOf₀" => sectionOf sem hA hp hK hpr ht G C

theorem section_embedded (hG : VisibleOn 2 G) (hC : SelfVis 2 C)
    d :
    sectionOf₀
      (embed sem 1 2 (by decide) (one_le₀) (by decide) hA d) =
      smallSection₀ G C d :=
  GradeCutPairRows.glue_embed D _ _ 1 2 (by decide) (one_le₀) (by decide) hA p _
    (small_readback sem hA hp hK hpr ht hG hC) d

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (semantics sem hA hp)

theorem section_lawful (hG : VisibleOn 2 G) (hC : SelfVis 2 C) :
    RespectsSemanticsBelow₀ (A, K)
      (fun d => sectionOf₀ d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  obtain ⟨x, hx⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le₀) (by decide) hA).surjective c.1
  have hc := c.2
  rw [← hx] at hc ⊢
  change RespectsSemanticsBelow₀
    ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
      (by decide) (one_le₀) (by decide) hA x))
    (fun d => sectionOf₀ d.1)
  have hlow (J : GradedIndex ι) (hJ : J.2 ≤ 2) :
      RespectsSemanticsBelow₀ J
        (fun d => sectionOf₀ d.1) := by
    have hr := CanonicalMixedGradeLayers.section_lawful (rows₀)
      1 (by decide) (one_le₀) (proper₀) 2
      (GradeCutBoundary.grade_bound) (by decide) hA (by decide)
      (cut_lawful₀) (fun d => ht (toCell₀ d)) hG hC
    have hs := (GradeCutPairRows.lower_respects_iff D _ _ 1 2 (by decide)
      (one_le₀) (by decide) hA hp (by decide) sem (smallRows sem hA hp)
      (overlap) J hJ _).mp
      (hr.toBelow J)
    convert hs using 1
    funext d
    let e := GradeCutPairCarrier.belowEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide) (one_le₀) (by decide) hA J hJ
    exact (congrArg (sectionOf₀)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
      (section_embedded sem hA hp hK hpr ht hG hC _)
  rcases x with (a | q) | q
  · have ha : GradedLe (D.cell a) (A, K) := by
      change GradedLe ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
        (by decide) (one_le₀) (by decide) hA (.inl (.inl a)))) (A, K) at hc
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using hc
    let e := GradeCutPairRows.ownerEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide)
      (one_le₀) (by decide) hA hp a
    have hr := (GradeCutPairRows.proper_respects_iff hp (by decide) sem (smallRows sem hA hp)
      (D.cell a) (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.mono ha)
    have hs := GradeCutLayerRows.cast_respects
      (GradeCutPairCarrier.cell_idx D (firstProfiles sem 1 2) (secondProfiles sem 2)
        1 2 (by decide) (one_le₀)
        (by decide) hA (.inl (.inl a))).symm hr
    change RespectsSemanticsBelow₀ _ _ at hs
    convert hs using 1
    funext d
    let d' : (carrier sem hA).below (D.cell a) := ⟨d.1, by
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    exact (congrArg (sectionOf₀)
      (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
      (section_old (e.symm d').1)
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact (by decide : 1 ≤ 2))
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact le_rfl)

theorem section_bound (hC : SelfVis 2 C) (hb : BoundedBy p C)
    d : sectionOf₀ d ≤ C := by
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le₀) (by decide) hA).symm d with (a | q) | q
  · exact hb a
  all_goals
    exact CanonicalMixedGradeLayers.section_bound (rows₀)
      1 (by decide) (one_le₀) (proper₀) 2
      GradeCutBoundary.grade_bound (by decide) hA (by decide)
      (cut_lawful₀) _ hC (fun a => hb (toCell₀ a)) _

theorem section_supported {L} (hL : 2 ≤ L) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := by
  have hl (a : Cell (small sem hA)) : OrbitPrefixSupport.Supported L (G) p
      (smallSection₀ G C a) := by
    rcases CanonicalMixedGradeLayers.section_supported (rows₀)
      1 (by decide) (one_le₀) (proper₀) 2
      GradeCutBoundary.grade_bound (by decide) hA (by decide) hL hCG
      (cut_lawful₀) (fun d => ht (toCell₀ d)) a with
      hb | hm | ⟨e, i, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ⟨toCell₀ e, i, hi, he⟩)
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le₀) (by decide) hA).symm d with (a | q) | q
  · change OrbitPrefixSupport.Supported L (G) p (p a)
    rcases ExtOrd.cases (p a) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · simp_all
    · by_cases hi : finitePart v < L
      · exact Or.inr (Or.inr ⟨a, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨a, L, le_rfl, by
          grind [extVisibilityReplace_of_le_finitePart]⟩)
  · exact hl _
  · exact hl _

theorem section_agreement {q : CellLabels D}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : AvoidsValue q ⊤)
    {h : ExtOrd} (hG : VisibleOn 2 G) (hC : SelfVis 2 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀) (sectionOf sem hA hp hK hqr htq G C) h := by
  have hl := CanonicalMixedGradeLayers.section_agreement (rows₀)
    1 (by decide) (one_le₀) (proper₀) 2
    GradeCutBoundary.grade_bound (by decide) hA (by decide)
    (cut_lawful₀) (cut_lawful sem hK hqr)
    (fun d => ht (toCell₀ d))
    (fun d => htq (toCell₀ d)) hG hC hh hhC
    (fun d => hag (toCell₀ d))
  intro d
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le₀) (by decide) hA).symm d with (a | r) | r
  · exact hag a
  · exact hl _
  · exact hl _

